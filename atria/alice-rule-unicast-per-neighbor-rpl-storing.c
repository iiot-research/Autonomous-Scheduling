/**
 * Copyright (c) 2015, Swedish Institute of Computer Science.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the Institute nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE INSTITUTE AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE INSTITUTE OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 */
/**
 * \file
 *         Orchestra: a slotframe dedicated to unicast data transmission. Designed for
 *         RPL storing mode only, as this is based on the knowledge of the children (and parent).
 *         If receiver-based:
 *           Nodes listen at a timeslot defined as hash(MAC) % ORCHESTRA_SB_UNICAST_PERIOD
 *           Nodes transmit at: for each nbr in RPL children and RPL preferred parent,
 *                                             hash(nbr.MAC) % ORCHESTRA_SB_UNICAST_PERIOD
 *         If sender-based: the opposite
 *
 * \author Simon Duquennoy <simonduq@sics.se>
 */

/* MODIFY for ATRIA */

/* for hash time measure
#include "sys/clock.h"
#include "sys/rtimer.h"
*/
#include "contiki.h"
#include "orchestra.h"
#include "net/ipv6/uip-ds6-route.h"
#include "net/packetbuf.h"
#include "net/rpl/rpl-conf.h"
#include "net/mac/tsch/tsch-private.h"
//#include "net/mac/tsch/tsch-asn.h"
#include <stdbool.h>

#if ORCHESTRA_UNICAST_SENDER_BASED && ORCHESTRA_COLLISION_FREE_HASH
#define UNICAST_SLOT_SHARED_FLAG    ((ORCHESTRA_UNICAST_PERIOD < (ORCHESTRA_MAX_HASH + 1)) ? LINK_OPTION_SHARED : 0)
#else
#define UNICAST_SLOT_SHARED_FLAG      LINK_OPTION_SHARED
#endif

#include "net/mac/tsch/tsch-log.h"

#define DEBUG DEBUG_FULL 
#include "net/net-debug.h"

#include "net/rpl/rpl.h"
#include "net/rpl/rpl-private.h"


uint16_t asfn_schedule=0; //absolute slotframe number for ATRIA time varying scheduling
uint16_t pre_asfn=0;
uint16_t routing_change=0; //
static uint16_t sub_period = 3;
static uint16_t num_sub_period = 67;

static uint16_t slotframe_handle = 0;
static struct tsch_slotframe *sf_unicast;

uint8_t link_option_rx = LINK_OPTION_RX ;
//uint8_t link_option_tx = LINK_OPTION_TX | UNICAST_SLOT_SHARED_FLAG ; //ksh.. If it is a shared link, backoff will be applied.
uint8_t link_option_tx = LINK_OPTION_TX ; 


/*-------------------------------------------------------------------------------*/
static uint16_t
get_node_timeslot_us(const linkaddr_t *addr1, const linkaddr_t *addr2) //get timeslot for upstream
{
  if(addr1 != NULL && addr2 != NULL && ORCHESTRA_UNICAST_PERIOD > 0) { 
    return real_hash((ORCHESTRA_LINKADDR_HASH2(addr1, addr2)+asfn_schedule), (ORCHESTRA_UNICAST_PERIOD)); //link-based
  } else {
    return 0xffff;
  }
}
/*---------------------------------------------------------------------------*/
static uint16_t
get_node_timeslot_ds(const linkaddr_t *addr1, const linkaddr_t *addr2) //get timeslot for downstream
{
  if(addr1 != NULL && addr2 != NULL && ORCHESTRA_UNICAST_PERIOD > 0) { 
     return real_hash((ORCHESTRA_LINKADDR_HASH2(addr1, addr2)+asfn_schedule), (ORCHESTRA_UNICAST_PERIOD)); //link-based
  } else {
    return 0xffff;
  }
}
/*---------------------------------------------------------------------------*/
static uint16_t
get_node_channel_offset_us(const linkaddr_t *addr1, const linkaddr_t *addr2)
{
  int num_ch = (sizeof(TSCH_DEFAULT_HOPPING_SEQUENCE)/sizeof(uint8_t))-1; 

  if(addr1 != NULL && addr2 != NULL  && num_ch > 0) {   
       return 1+real_hash((ORCHESTRA_LINKADDR_HASH2(addr1, addr2)+asfn_schedule),num_ch); //link-based
  } else {
    return 1+0; 
  }
}
/*---------------------------------------------------------------------------*/
static uint16_t
get_node_channel_offset_ds(const linkaddr_t *addr1, const linkaddr_t *addr2)
{
  int num_ch = (sizeof(TSCH_DEFAULT_HOPPING_SEQUENCE)/sizeof(uint8_t))-1; 

  if(addr1 != NULL && addr2 != NULL  && num_ch > 0) {
       return 1+real_hash((ORCHESTRA_LINKADDR_HASH2(addr1, addr2)+asfn_schedule),num_ch); //link-based
  } else {
    return 1+0; 
  }
}

/*---------------------------------------------------------------------------*/
static uint16_t
get_node_multiple_timeslot_us(const linkaddr_t *addr1, const linkaddr_t *addr2, uint16_t cell_seq) //get timeslot for upstream
{
  if(addr1 != NULL && addr2 != NULL && ORCHESTRA_UNICAST_PERIOD > 0) { 

    return real_hash((ORCHESTRA_LINKADDR_HASH2(addr1, addr2)+asfn_schedule*(cell_seq+1)), (ORCHESTRA_UNICAST_PERIOD)); //link-based
  } else {
    return 0xffff;
  }
}

static uint16_t
get_node_multiple_timeslot_ds(const linkaddr_t *addr1, const linkaddr_t *addr2, uint16_t cell_seq) //get timeslot for downstream
{
  if(addr1 != NULL && addr2 != NULL && ORCHESTRA_UNICAST_PERIOD > 0) { 

     return real_hash((ORCHESTRA_LINKADDR_HASH2(addr1, addr2)+asfn_schedule*(cell_seq+1)), (ORCHESTRA_UNICAST_PERIOD)); //link-based
  } else {
    return 0xffff;
  }
}

static uint16_t
get_node_multiple_channel_offset_us(const linkaddr_t *addr1, const linkaddr_t *addr2, uint16_t cell_seq)
{
  int num_ch = (sizeof(TSCH_DEFAULT_HOPPING_SEQUENCE)/sizeof(uint8_t))-1; 

  if(addr1 != NULL && addr2 != NULL  && num_ch > 0) { 
       return 1+real_hash((ORCHESTRA_LINKADDR_HASH2(addr1, addr2)+asfn_schedule*(cell_seq+1)),num_ch); //link-based
  } else {
    return 1+0; 
  }
}

static uint16_t
get_node_multiple_channel_offset_ds(const linkaddr_t *addr1, const linkaddr_t *addr2, uint16_t cell_seq)
{
  int num_ch = (sizeof(TSCH_DEFAULT_HOPPING_SEQUENCE)/sizeof(uint8_t))-1; 

  if(addr1 != NULL && addr2 != NULL  && num_ch > 0) {  
       return 1+real_hash((ORCHESTRA_LINKADDR_HASH2(addr1, addr2)+asfn_schedule*(cell_seq+1)),num_ch); //link-based
  } else {
    return 1+0; 
  }
}
/*---------------------------------------------------------------------------*/

/*------------------------------- Xia ---------------------------------------*/
static uint16_t
get_slotframe_offset(const linkaddr_t *addr1, const linkaddr_t *addr2, uint16_t block_seq, uint16_t block_size)
{

  if(addr1 != NULL && addr2 != NULL && block_size > 0) {

    return real_hash((ORCHESTRA_LINKADDR_HASH2(addr1, addr2)+asfn_schedule*(block_seq+1)), (block_size)); 
  } 
  else {
    return 0xffff;
  }
}

static uint16_t
get_slot_offset(const linkaddr_t *addr1, const linkaddr_t *addr2, uint16_t block_seq)
{

  if(addr1 != NULL && addr2 != NULL && sub_period > 0) {

    return real_hash((ORCHESTRA_LINKADDR_HASH2(addr1, addr2)+asfn_schedule*(block_seq+1)), (sub_period)); 
  } 
  else {
    return 0xffff;
  }
}

static uint16_t
get_channel_offset(const linkaddr_t *addr1, const linkaddr_t *addr2, uint16_t block_seq)
{

  int num_ch = (sizeof(TSCH_DEFAULT_HOPPING_SEQUENCE)/sizeof(uint8_t))-1; 
  if(addr1 != NULL && addr2 != NULL  && num_ch > 0) {

    return 1+real_hash((ORCHESTRA_LINKADDR_HASH2(addr1, addr2)+asfn_schedule*(block_seq+1)), num_ch); 
  } 
  else {
    return 1+0; 
  }
}
/*---------------------------------------------------------------------------*/

uint16_t
is_root(){
  rpl_instance_t *instance =rpl_get_default_instance();
  if(instance!=NULL && instance->current_dag!=NULL){
       uint16_t min_hoprankinc = instance->min_hoprankinc;
       uint16_t rank=(uint16_t)instance->current_dag->rank;
       if(min_hoprankinc == rank){
          return 1;
       }
  }
  return 0;
}

/****--------------- Count the routes of each neighbor ---------------****/
int neighbor_routes_count(linkaddr_t *addr)
{
  int count = 0;
  struct uip_ds6_route_neighbor_routes *routes;
  struct uip_ds6_route_neighbor_route *nbr;

  routes = nbr_table_get_from_lladdr(nbr_routes, (linkaddr_t *)addr);
  
  for(nbr = list_head(routes->route_list);
      nbr != NULL;
      nbr = list_item_next(nbr)) 
  {
  //  printf("Ip address is:%d \n", nbr->route->ipaddr.u8[15]);
    count++;
  }
  return count;
}
/*---------------------------------------------------------------------------*/


/*---------------------------------------------------------------------------*/
static void
atria_RESCHEDULE_unicast_slotframe1(void){   //remove current slotframe scheduling and re-schedule this slotframe.

//  printf("Self address: %u slotframe: %d\n", linkaddr_node_addr.u8[LINKADDR_SIZE-1], asfn_schedule);
  uint16_t timeslot_us, timeslot_ds, channel_offset_us, channel_offset_ds;
  uint16_t timeslot_us_p, timeslot_ds_p, channel_offset_us_p, channel_offset_ds_p; //parent's schedule
  uint8_t link_option_up, link_option_down;
  uint16_t slotframe_offset, slot_offset, cell_seq, block_size;
  int     schedule_num, i;
  float   block_avg;

  struct tsch_link *l;
  l = list_head(sf_unicast->links_list);

 if(is_root()!=1){
//schedule the links between parent-node and current node
  if(l!=NULL){
    if(pre_asfn != asfn_schedule && pre_asfn%6 == 0)
    {
      printf("R : %d, a:%d, addr:%u\n", uip_ds6_route_num_routes(), asfn_schedule, orchestra_parent_linkaddr.u8[LINKADDR_SIZE-1]);
    }
    schedule_num = uip_ds6_route_num_routes() + 1;  
    #if IMP_METHOD3
      if(schedule_num > 0)
      {
        schedule_num = schedule_num * 2;
     

        block_avg = (float)num_sub_period/(float)schedule_num;
      //  printf("B_S is %f\n", block_avg);
        for(i=1; i<=schedule_num; i++)
        {
          if(i < schedule_num) {
            block_size = (uint16_t)(block_avg*i) - (uint16_t)(block_avg*(i-1));
          }
          else {
            block_size = num_sub_period - (uint16_t)(block_avg*(i-1));
          }
          if(i%2 == 1) {
            slotframe_offset = get_slotframe_offset(&linkaddr_node_addr, &orchestra_parent_linkaddr, i, block_size);
            slot_offset = get_slot_offset(&linkaddr_node_addr, &orchestra_parent_linkaddr, i);
            timeslot_us_p = (slotframe_offset + (uint16_t)(block_avg * (i - 1))) * sub_period + slot_offset; 
            channel_offset_us_p = get_channel_offset(&linkaddr_node_addr, &orchestra_parent_linkaddr, i);
            link_option_up=link_option_tx;

            if(l!=NULL) {
              l->link_options=link_option_up;
              l->timeslot=timeslot_us_p;
              l->channel_offset=channel_offset_us_p;
              l->cell_seq = i;
              l->schedule_num = schedule_num;
              l->direction = 2;
              l = list_item_next(l);
            } 
          }
          else {
            slotframe_offset = get_slotframe_offset(&orchestra_parent_linkaddr, &linkaddr_node_addr, i, block_size);
            slot_offset = get_slot_offset(&orchestra_parent_linkaddr, &linkaddr_node_addr, i);
            timeslot_ds_p = (slotframe_offset + (uint16_t)(block_avg * (i - 1))) * sub_period + slot_offset; 
            channel_offset_ds_p = get_channel_offset(&orchestra_parent_linkaddr, &linkaddr_node_addr, i);
            link_option_down=link_option_rx;

            if(l!=NULL) {
              l->link_options=link_option_down;
              l->timeslot=timeslot_ds_p;
              l->channel_offset=channel_offset_ds_p;
              l->cell_seq = i;
              l->schedule_num = schedule_num;
              l->direction = 2;
              l = list_item_next(l);
            }
          }
        }
      }
    #endif
  }
 
 }//is_root()! end

  nbr_table_item_t *item = nbr_table_head(nbr_routes);
  while(l!=NULL && item!=NULL) {    

    linkaddr_t *addr = nbr_table_get_lladdr(nbr_routes, item);

    if(linkaddr_cmp(&orchestra_parent_linkaddr, addr)){
       item = nbr_table_next(nbr_routes, item);
       printf("PARENT MATCH\n");
       if(item==NULL){
         printf("NULL ITEM\n");

#ifdef ALICE_TSCH_CALLBACK_SLOTFRAME_START // sf update
           while(l!=NULL){
              
              //parent downlink schedule
              l->link_options=link_option_up;
              l->timeslot=timeslot_us;
              l->channel_offset=channel_offset_us;
              l = list_item_next(l);     
              
              if(l!=NULL){
                 //parent downlink schedule
                 l->link_options=link_option_down;
                 l->timeslot=timeslot_ds;
                 l->channel_offset=channel_offset_ds;
                 l = list_item_next(l);
              }
           }
#endif
           return;
       }
    }

    if(pre_asfn != asfn_schedule && pre_asfn%6 == 0)
    {
      printf("N :%d a:%d, addr:%u \n", neighbor_routes_count(addr), asfn_schedule, addr->u8[LINKADDR_SIZE-1]);
    } 
  #if IMP_METHOD3
    schedule_num = neighbor_routes_count(addr) * 2;
    

    if(schedule_num > 0) { 
      block_avg = (float)num_sub_period/(float)schedule_num;
    //  printf("B_S is %f\n", block_avg);
      for(i=1; i<=schedule_num; i++)
      {
        if(i < schedule_num) {
          block_size = (uint16_t)(block_avg*i) - (uint16_t)(block_avg*(i-1));
        }
        else {
          block_size = num_sub_period - (uint16_t)(block_avg*(i-1));
        }
        if(i%2 == 1) {
          slotframe_offset = get_slotframe_offset(addr, &linkaddr_node_addr, i, block_size);
          slot_offset = get_slot_offset(addr, &linkaddr_node_addr, i);
          timeslot_us = (slotframe_offset + (uint16_t)(block_avg * (i - 1))) * sub_period + slot_offset; 
          channel_offset_us = get_channel_offset(addr, &linkaddr_node_addr, i);
          link_option_up=link_option_rx;
   
          if(l!=NULL) {
            l->link_options=link_option_up;
            l->timeslot=timeslot_us;
            l->channel_offset=channel_offset_us;
            l->cell_seq = i;
            l->schedule_num = schedule_num;
            l->direction = 1;
            l = list_item_next(l);
          } 
        }
        else {
          slotframe_offset = get_slotframe_offset(&linkaddr_node_addr, addr, i, block_size);
          slot_offset = get_slot_offset(&linkaddr_node_addr, addr, i);
          timeslot_ds = (slotframe_offset + (uint16_t)(block_avg * (i - 1))) * sub_period + slot_offset; 
          channel_offset_ds = get_channel_offset(&linkaddr_node_addr, addr, i);
          link_option_down=link_option_tx;
 
          if(l!=NULL) {
            l->link_options=link_option_down;
            l->timeslot=timeslot_ds;
            l->channel_offset=channel_offset_ds;
            l->cell_seq = i;
            l->schedule_num = schedule_num;
            l->direction = 1;
            l = list_item_next(l);
          }
        }
      }
    }
  #endif

    item = nbr_table_next(nbr_routes, item);    
  } //while end..

}

/*---------------------------------------------------------------------------*/
static void
atria_schedule_unicast_slotframe(const linkaddr_t *change_addr, uint16_t reason)
{   //remove current slotframe scheduling and re-schedule this slotframe.
  printf("Initial Schedule\n");
  uint16_t timeslot_us, timeslot_ds, channel_offset_us, channel_offset_ds;
  uint16_t timeslot_us_p, timeslot_ds_p, channel_offset_us_p, channel_offset_ds_p; //parent's schedule
  uint8_t link_option_up, link_option_down;
  uint16_t cell_seq, slotframe_offset, slot_offset;
  uint16_t neighbor_seq, block_size;
  int     schedule_num;
  float   block_avg;
  int     i;

//remove the whole links scheduled in the unicast slotframe
  struct tsch_link *l;
  l = list_head(sf_unicast->links_list);
  while(l!=NULL) {    
    tsch_schedule_remove_link(sf_unicast, l);
    l = list_head(sf_unicast->links_list);
  }

 if(is_root()!=1){
//schedule the links between parent-node and current node

     timeslot_us_p = get_node_timeslot_us(&linkaddr_node_addr, &orchestra_parent_linkaddr);
     timeslot_ds_p = get_node_timeslot_ds(&orchestra_parent_linkaddr, &linkaddr_node_addr);

     channel_offset_us_p = get_node_channel_offset_us(&linkaddr_node_addr, &orchestra_parent_linkaddr);
     channel_offset_ds_p = get_node_channel_offset_ds(&orchestra_parent_linkaddr, &linkaddr_node_addr);
     link_option_up=link_option_tx;
     link_option_down=link_option_rx;
     tsch_schedule_add_first_link(sf_unicast, link_option_up, LINK_TYPE_NORMAL, &tsch_broadcast_address, timeslot_us_p, channel_offset_us_p, 2);
     tsch_schedule_add_first_link(sf_unicast, link_option_down, LINK_TYPE_NORMAL, &tsch_broadcast_address, timeslot_ds_p, channel_offset_ds_p, 2);
  #if IMP_METHOD1
     printf("Parent additional schedule %d link\n", uip_ds6_route_num_routes());
     cell_seq = 1;
    
     if (uip_ds6_route_num_routes() > 1 || routing_change == 2 || (uip_ds6_route_num_routes() == 1 && routing_change !=1 ))
     {
      timeslot_us_p = get_node_multiple_timeslot_us(&linkaddr_node_addr, &orchestra_parent_linkaddr, cell_seq);
      timeslot_ds_p = get_node_multiple_timeslot_ds(&orchestra_parent_linkaddr, &linkaddr_node_addr, cell_seq);

      channel_offset_us_p = get_node_multiple_channel_offset_us(&linkaddr_node_addr, &orchestra_parent_linkaddr, cell_seq);
      channel_offset_ds_p = get_node_multiple_channel_offset_ds(&orchestra_parent_linkaddr, &linkaddr_node_addr, cell_seq);
      link_option_up=link_option_tx;
      link_option_down=link_option_rx;
      printf("Up tx:%d %d, rx:%d %d\n", timeslot_us_p, channel_offset_us_p, timeslot_ds_p, channel_offset_ds_p);
      tsch_schedule_add_multiple_link(sf_unicast, link_option_up, LINK_TYPE_NORMAL, &tsch_broadcast_address, timeslot_us_p, channel_offset_us_p, cell_seq);
      tsch_schedule_add_multiple_link(sf_unicast, link_option_down, LINK_TYPE_NORMAL, &tsch_broadcast_address, timeslot_ds_p, channel_offset_ds_p, cell_seq);
    }
  #endif
  #if IMP_METHOD2
    if(routing_change == 2) {
      schedule_num = uip_ds6_route_num_routes() + 1;
    }
    else if(routing_change == 1) {
      schedule_num = uip_ds6_route_num_routes() - 1;
    }
    else {
      schedule_num = uip_ds6_route_num_routes();
    }
    if(schedule_num > 0)
    {
      printf("Parent additional schedule %d link\n", schedule_num);
      cell_seq = schedule_num;
      while(cell_seq > 0)
      {
        timeslot_us_p = get_node_multiple_timeslot_us(&linkaddr_node_addr, &orchestra_parent_linkaddr, cell_seq);
        timeslot_ds_p = get_node_multiple_timeslot_ds(&orchestra_parent_linkaddr, &linkaddr_node_addr, cell_seq);

        channel_offset_us_p = get_node_multiple_channel_offset_us(&linkaddr_node_addr, &orchestra_parent_linkaddr, cell_seq);
        channel_offset_ds_p = get_node_multiple_channel_offset_ds(&orchestra_parent_linkaddr, &linkaddr_node_addr, cell_seq);
        link_option_up=link_option_tx;
        link_option_down=link_option_rx;
      //  printf("Up group(%d) tx:%d %d, rx:%d %d\n", cell_seq, timeslot_us_p, channel_offset_us_p, timeslot_ds_p, channel_offset_ds_p);
        tsch_schedule_add_multiple_link(sf_unicast, link_option_up, LINK_TYPE_NORMAL, &tsch_broadcast_address, timeslot_us_p, channel_offset_us_p, cell_seq, 2);
        tsch_schedule_add_multiple_link(sf_unicast, link_option_down, LINK_TYPE_NORMAL, &tsch_broadcast_address, timeslot_ds_p, channel_offset_ds_p, cell_seq, 2);
        cell_seq--;
      }
    }
  #endif
  #if IMP_METHOD3
    if(routing_change == 2) {
      schedule_num = uip_ds6_route_num_routes() + 1;
    }
    else if(routing_change == 1) {
      schedule_num = uip_ds6_route_num_routes() - 1;
    }
    else {
      schedule_num = uip_ds6_route_num_routes();
    }
    schedule_num = schedule_num * 2;
    

      if(schedule_num > 0)
      {     
        block_avg = (float)num_sub_period/(float)schedule_num;
      //  printf("Average block_size is %f\n", block_avg);
        for(i=1; i<=schedule_num; i++)
        {
          if(i<schedule_num) {
            block_size = (uint16_t)(block_avg*i) - (uint16_t)(block_avg*(i-1));
          }
          else {
            block_size = num_sub_period - (uint16_t)(block_avg*(i-1));
          }
          if(i%2 == 1)
          {
            slotframe_offset = get_slotframe_offset(&linkaddr_node_addr, &orchestra_parent_linkaddr, i, block_size);
            slot_offset = get_slot_offset(&linkaddr_node_addr, &orchestra_parent_linkaddr, i);
            timeslot_us_p = (slotframe_offset + (uint16_t)(block_avg * (i - 1))) * sub_period + slot_offset; 
            channel_offset_us_p = get_channel_offset(&linkaddr_node_addr, &orchestra_parent_linkaddr, i);
            link_option_up=link_option_tx;

            tsch_schedule_add_evenly_link(sf_unicast, link_option_up, LINK_TYPE_NORMAL, &tsch_broadcast_address, timeslot_us_p, channel_offset_us_p, i, schedule_num, 2);
          }
          else
          {
            slotframe_offset = get_slotframe_offset(&orchestra_parent_linkaddr, &linkaddr_node_addr, i, block_size);
            slot_offset = get_slot_offset(&orchestra_parent_linkaddr, &linkaddr_node_addr, i);
            timeslot_ds_p = (slotframe_offset + (uint16_t)(block_avg * (i - 1))) * sub_period + slot_offset; 
            channel_offset_ds_p = get_channel_offset(&orchestra_parent_linkaddr, &linkaddr_node_addr, i);
            link_option_down=link_option_rx;

            tsch_schedule_add_evenly_link(sf_unicast, link_option_down, LINK_TYPE_NORMAL, &tsch_broadcast_address, timeslot_ds_p, channel_offset_ds_p, i, schedule_num, 2); 
          }
        }
      }
  #endif

 }//is_root end

//schedule the links between child-node and current node   //(lookup all route next hops)
  nbr_table_item_t *item = nbr_table_head(nbr_routes);
  neighbor_seq = 0;
  while(item != NULL) {
    neighbor_seq++;
    linkaddr_t *addr = nbr_table_get_lladdr(nbr_routes, item);
    //ts and choff allocation

    timeslot_us = get_node_timeslot_us(addr, &linkaddr_node_addr); 
    timeslot_ds = get_node_timeslot_ds(&linkaddr_node_addr, addr); 

    channel_offset_us = get_node_channel_offset_us(addr, &linkaddr_node_addr);
    channel_offset_ds = get_node_channel_offset_ds(&linkaddr_node_addr, addr);

    //upstream link option
    if(timeslot_us==timeslot_us_p && channel_offset_us==channel_offset_us_p){
       link_option_up = link_option_tx | link_option_rx;
    }else{
       link_option_up = link_option_rx;
    }

    //downstream link option
    if(timeslot_ds==timeslot_ds_p && channel_offset_ds==channel_offset_ds_p){
       link_option_down = link_option_rx | link_option_tx;
    }else{
       link_option_down = link_option_tx;
    }

    //add links (upstream and downstream)
    tsch_schedule_add_first_link(sf_unicast, link_option_up, LINK_TYPE_NORMAL, &tsch_broadcast_address, timeslot_us, channel_offset_us, 1);
    tsch_schedule_add_first_link(sf_unicast, link_option_down, LINK_TYPE_NORMAL, &tsch_broadcast_address, timeslot_ds, channel_offset_ds, 1);

  #if IMP_METHOD3
    if(routing_change == 2) {
      if(reason == 1) {
        schedule_num = neighbor_routes_count(addr);
      }
      else if(reason == 2) {
        if(linkaddr_cmp(addr, change_addr)) {
          schedule_num = neighbor_routes_count(addr) + 1;
        }
        else {
          schedule_num = neighbor_routes_count(addr);
        }
      }
    }
    else {
      schedule_num = neighbor_routes_count(addr);
    }
    schedule_num = (schedule_num - 1) * 2;
    

    if(schedule_num > 0) { 
      block_avg = (float)num_sub_period/(float)schedule_num;
    
      for(i=1; i<=schedule_num; i++)
      {
        if(i < schedule_num) {
          block_size = (uint16_t)(block_avg*i) - (uint16_t)(block_avg*(i-1));
        }
        else {
          block_size = num_sub_period - (uint16_t)(block_avg*(i-1));
        }
        if(i%2 == 1) {
          slotframe_offset = get_slotframe_offset(addr, &linkaddr_node_addr, i, block_size);
          slot_offset = get_slot_offset(addr, &linkaddr_node_addr, i);
          timeslot_us = (slotframe_offset + (uint16_t)(block_avg * (i - 1))) * sub_period + slot_offset; 
          channel_offset_us = get_channel_offset(addr, &linkaddr_node_addr, i);
          link_option_up = link_option_rx; 
      
          tsch_schedule_add_evenly_link(sf_unicast, link_option_up, LINK_TYPE_NORMAL, &tsch_broadcast_address, timeslot_us, channel_offset_us, i, schedule_num, 1);
        }
        else {
          slotframe_offset = get_slotframe_offset(&linkaddr_node_addr, addr, i, block_size);
          slot_offset = get_slot_offset(&linkaddr_node_addr, addr, i);
          timeslot_ds = (slotframe_offset + (uint16_t)(block_avg * (i - 1))) * sub_period + slot_offset; 
          channel_offset_ds = get_channel_offset(&linkaddr_node_addr, addr, i);
          link_option_down = link_option_tx;
        
          tsch_schedule_add_evenly_link(sf_unicast, link_option_down, LINK_TYPE_NORMAL, &tsch_broadcast_address, timeslot_ds, channel_offset_ds, i, schedule_num, 1);
        }
      }
    }
  #endif

    //move to the next item for while loop.
    item = nbr_table_next(nbr_routes, item);
  }
  routing_change = 0;
//  tsch_schedule_print();
}

/*---------------------------------------------------------------------------*/ // slotframe_callback. 
#ifdef ALICE_TSCH_CALLBACK_SLOTFRAME_START
void alice_callback_slotframe_start (uint16_t sfid, uint16_t sfsize){  
  asfn_schedule=sfid; // update curr asfn_schedule.
//  printf("CALL(%d)\n", asfn_schedule);
  atria_RESCHEDULE_unicast_slotframe1();
  pre_asfn = asfn_schedule;

}
#endif
/*---------------------------------------------------------------------------*/ // packet_selection_callback. 
#ifdef ALICE_CALLBACK_PACKET_SELECTION
int alice_callback_packet_selection (uint16_t* ts, uint16_t* choff, const linkaddr_t rx_lladdr){


//schedule the links between parent-node and current node
  if(linkaddr_cmp(&orchestra_parent_linkaddr, &rx_lladdr)){
    *ts= get_node_timeslot_us(&linkaddr_node_addr, &orchestra_parent_linkaddr);
    *choff= get_node_channel_offset_us(&linkaddr_node_addr, &orchestra_parent_linkaddr);       
//    printf("ksh.. PCS.... parent : (%u,%u)\n", *ts, *choff);
    return 1;
  }

//schedule the links between child-node and current node   //(lookup all route next hops)
  nbr_table_item_t *item = nbr_table_head(nbr_routes);
  while(item != NULL) {
    linkaddr_t *addr = nbr_table_get_lladdr(nbr_routes, item);
    if(linkaddr_cmp(addr, &rx_lladdr)){
      *ts= get_node_timeslot_ds(&linkaddr_node_addr, addr);
      *choff= get_node_channel_offset_ds(&linkaddr_node_addr, addr); 

      return 1;
    } 
    item = nbr_table_next(nbr_routes, item);
  }

 
  *ts =0;
  *choff= ALICE_BROADCAST_SF_ID;
  //-----------------------

  return 0;
}
#endif 

/*---------------------------------------------------------------------------*/ //xia. packet_selection_callback. 
#ifdef IMP_CALLBACK_PACKET_SELECTION
int imp_callback_packet_selection (uint16_t* ts, uint16_t* choff, const linkaddr_t rx_lladdr, uint16_t cell_seq)
{
//schedule the links between parent-node and current node
  if(linkaddr_cmp(&orchestra_parent_linkaddr, &rx_lladdr)){
    *ts= get_node_multiple_timeslot_us(&linkaddr_node_addr, &orchestra_parent_linkaddr, cell_seq);
    *choff= get_node_multiple_channel_offset_us(&linkaddr_node_addr, &orchestra_parent_linkaddr, cell_seq);       

    return 1;
  }

//schedule the links between child-node and current node   //(lookup all route next hops)
  nbr_table_item_t *item = nbr_table_head(nbr_routes);
  while(item != NULL) {
    linkaddr_t *addr = nbr_table_get_lladdr(nbr_routes, item);
    if(linkaddr_cmp(addr, &rx_lladdr)){
      *ts= get_node_multiple_timeslot_ds(&linkaddr_node_addr, addr, cell_seq);
      *choff= get_node_multiple_channel_offset_ds(&linkaddr_node_addr, addr, cell_seq); 

      return 1;
    } 
    item = nbr_table_next(nbr_routes, item);
  }

 
  *ts =0;
  *choff= ALICE_BROADCAST_SF_ID;
  //-----------------------

  return 0;
}
#endif  //IMP_CALLBACK_PACKET_SELECTION
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/ //xia. packet_selection_callback. 
#ifdef SPE_CALLBACK_PACKET_SELECTION
int spe_callback_packet_selection (uint16_t* ts, uint16_t* choff, const linkaddr_t rx_lladdr, uint16_t cell_seq, uint16_t schedule_num)
{
  float block_avg;
  uint16_t block_size;
  uint16_t slotframe_offset, slot_offset;

//schedule the links between parent-node and current node
  if(linkaddr_cmp(&orchestra_parent_linkaddr, &rx_lladdr)) {
    block_avg = (float)num_sub_period/(float)schedule_num;
    if(cell_seq<schedule_num) {
      block_size = (uint16_t)(block_avg*cell_seq) - (uint16_t)(block_avg*(cell_seq-1));
    }
    else {
      block_size = num_sub_period - (uint16_t)(block_avg*(cell_seq-1));
    }
    if(cell_seq%2 == 1) {
      slotframe_offset = get_slotframe_offset(&linkaddr_node_addr, &orchestra_parent_linkaddr, cell_seq, block_size);
      slot_offset = get_slot_offset(&linkaddr_node_addr, &orchestra_parent_linkaddr, cell_seq);
      *ts = (slotframe_offset + (uint16_t)(block_avg * (cell_seq - 1))) * sub_period + slot_offset; 
      *choff = get_channel_offset(&linkaddr_node_addr, &orchestra_parent_linkaddr, cell_seq);
    }

    return 1;
  }

//schedule the links between child-node and current node   //(lookup all route next hops)
  nbr_table_item_t *item = nbr_table_head(nbr_routes);
  while(item != NULL) {
    linkaddr_t *addr = nbr_table_get_lladdr(nbr_routes, item);
    if(linkaddr_cmp(addr, &rx_lladdr)){
      block_avg = (float)num_sub_period/(float)schedule_num;
      if(cell_seq < schedule_num) {
        block_size = (uint16_t)(block_avg*cell_seq) - (uint16_t)(block_avg*(cell_seq-1));
      }
      else {
        block_size = num_sub_period - (uint16_t)(block_avg*(cell_seq-1));
      }
      if(cell_seq%2 == 0) {
        slotframe_offset = get_slotframe_offset(&linkaddr_node_addr, addr, cell_seq, block_size);
        slot_offset = get_slot_offset(&linkaddr_node_addr, addr, cell_seq);
        *ts = (slotframe_offset + (uint16_t)(block_avg * (cell_seq - 1))) * sub_period + slot_offset; 
        *choff = get_channel_offset(&linkaddr_node_addr, addr, cell_seq);
        return 1;
      }
    } 
    item = nbr_table_next(nbr_routes, item);
  }
 
  *ts =0;
  *choff= ALICE_BROADCAST_SF_ID;
  return 0;
}
#endif  //SPE_CALLBACK_PACKET_SELECTION
/*---------------------------------------------------------------------------*/

static int
neighbor_has_uc_link(const linkaddr_t *linkaddr)
{
  if(linkaddr != NULL && !linkaddr_cmp(linkaddr, &linkaddr_null)) {
    if(orchestra_parent_knows_us 
       && linkaddr_cmp(&orchestra_parent_linkaddr, linkaddr)) {
      return 1;
    }
    if(nbr_table_get_from_lladdr(nbr_routes, (linkaddr_t *)linkaddr) != NULL  && !linkaddr_cmp(&orchestra_parent_linkaddr, linkaddr)) {
      return 1;
    }
  }
  return 0;
}
/*---------------------------------------------------------------------------*/
static void
child_added(const linkaddr_t *linkaddr, uint16_t reason)
{
  routing_change = 2;
  if(reason == 2)
  {
    printf("Child Add, leaf\n");
  }
  else if(reason == 1)
  {
    printf("Child Add, neighbor\n");
  }
  atria_schedule_unicast_slotframe(linkaddr, reason);
}
/*---------------------------------------------------------------------------*/
static void
child_removed(const linkaddr_t *linkaddr)
{
  routing_change = 1;
  printf("Child Remove\n");
  atria_schedule_unicast_slotframe(linkaddr, 0);
}
/*---------------------------------------------------------------------------*/
static int
select_packet(uint16_t *slotframe, uint16_t *timeslot, uint16_t *channel_offset)
{
  const linkaddr_t *dest = packetbuf_addr(PACKETBUF_ADDR_RECEIVER);

  if(packetbuf_attr(PACKETBUF_ATTR_FRAME_TYPE) == FRAME802154_DATAFRAME && neighbor_has_uc_link(dest)) {
    if(slotframe != NULL) {
      *slotframe = slotframe_handle;
    }
    if(timeslot != NULL) {

        //if the destination is the parent node, schedule it in the upstream period, if the destination is the child node, schedule it in the downstream period.
        if(linkaddr_cmp(&orchestra_parent_linkaddr, dest)){
           *timeslot = get_node_timeslot_us(&linkaddr_node_addr, dest); //parent node (upstream)
        }else{
           *timeslot = get_node_timeslot_ds(&linkaddr_node_addr, dest);  //child node (downstream)
        }
    }
    if(channel_offset != NULL) { 
        //if the destination is the parent node, schedule it in the upstream period, if the destination is the child node, schedule it in the downstream period.
        if(linkaddr_cmp(&orchestra_parent_linkaddr, dest)){
           *channel_offset = get_node_channel_offset_us(&linkaddr_node_addr, dest); //child node (upstream)
        }else{
           *channel_offset = get_node_channel_offset_ds(&linkaddr_node_addr, dest); //child node (downstream)
        }
    }

    return 1;
  }
  return 0;
}
/*---------------------------------------------------------------------------*/
static void
new_time_source(const struct tsch_neighbor *old, const struct tsch_neighbor *new)
{
  if(new != old) {   
    const linkaddr_t *new_addr = new != NULL ? &new->addr : NULL;
    if(new_addr != NULL) {
      linkaddr_copy(&orchestra_parent_linkaddr, new_addr);    
    } else {
      linkaddr_copy(&orchestra_parent_linkaddr, &linkaddr_null);
    }
    printf("NEW TIME source\n");
    atria_schedule_unicast_slotframe(new_addr, 0); 
  }
}
/*---------------------------------------------------------------------------*/
static void
init(uint16_t sf_handle)
{
  printf("PERIOD SIZE: ORCHESTRA_UNICAST_PERIOD : %d\n",  ORCHESTRA_UNICAST_PERIOD );
  printf("Buffer num: %d TSCH_MAC_MAX_FRAME_RETRIES=%d \n", QUEUEBUF_CONF_NUM, TSCH_MAC_MAX_FRAME_RETRIES);

  slotframe_handle = sf_handle; //sf_handle=1
  /* Slotframe for unicast transmissions */
  sf_unicast = tsch_schedule_add_slotframe(slotframe_handle, ORCHESTRA_UNICAST_PERIOD);


#ifdef ALICE_TSCH_CALLBACK_SLOTFRAME_START
  asfn_schedule = alice_tsch_schedule_get_current_asfn(sf_unicast);
#else
  asfn_schedule = 0; //sfid (ASN) will not be used.
#endif

}
/*---------------------------------------------------------------------------*/
struct orchestra_rule unicast_per_neighbor_rpl_storing = {
  init,
  new_time_source,
  select_packet,
  child_added,
  child_removed,
};
