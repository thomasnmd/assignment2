#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include "emulator.h"
#include "sr.h"


/* ******************************************************************
   Go Back N protocol.  Adapted from J.F.Kurose
   ALTERNATING BIT AND GO-BACK-N NETWORK EMULATOR: VERSION 1.2  

   Network properties:
   - one way network delay averages five time units (longer if there
   are other messages in the channel for GBN), but can be larger
   - packets can be corrupted (either the header or the data portion)
   or lost, according to user-defined probabilities
   - packets will be delivered in the order in which they were sent
   (although some can be lost).

   Modifications: 
   - removed bidirectional GBN code and other code not used by prac. 
   - fixed C style to adhere to current programming style
   - added GBN implementation
**********************************************************************/

#define RTT  16.0       /* round trip time.  MUST BE SET TO 16.0 when submitting assignment */
#define WINDOWSIZE 6    /* the maximum number of buffered unacked packet */
#define SEQSPACE 7      /* the min sequence space for GBN must be at least windowsize + 1 */
#define NOTINUSE (-1)   /* used to fill header fields that are not being used */

/* generic procedure to compute the checksum of a packet.  Used by both sender and receiver  
   the simulator will overwrite part of your packet with 'z's.  It will not overwrite your 
   original checksum.  This procedure must generate a different checksum to the original if
   the packet is corrupted.
*/
int ComputeChecksum(struct pkt packet)
{
  int checksum = 0;
  int i;
  checksum = packet.seqnum;
  checksum += packet.acknum;
  for ( i=0; i<20; i++ ) 
    checksum += (int)(packet.payload[i]);

  return checksum;
}

bool IsCorrupted(struct pkt packet)
{
  if (packet.checksum == ComputeChecksum(packet))
    return (false);
  else
    return (true);
}


/********* Sender (A) variables and functions ************/

static struct pkt buffer[SEQSPACE];  /* array for storing packets waiting for ACK */
static int windowfirst, windowlast;    /* array indexes of the first/last packet awaiting ACK */
static int windowcount;                /* the number of packets currently awaiting an ACK */
static int A_nextseqnum;               /* the next sequence number to be used by the sender */

static bool acked[SEQSPACE];



/* called from layer 5 (application layer), passed the message to be sent to other side */
void A_output(struct msg message)
{
  int i;
  struct pkt sendpkt;
  /* if not blocked waiting on ACK */
  if ( windowcount < WINDOWSIZE) {
    if (TRACE > 1)
      printf("----A: New message arrives, send window is not full, send new messge to layer3!\n");

    /* create packet */
    sendpkt.seqnum = A_nextseqnum;
    sendpkt.acknum = NOTINUSE;
    for (i = 0; i < 20 ; i++ ) 
      sendpkt.payload[i] = message.data[i];
    sendpkt.checksum = ComputeChecksum(sendpkt); 

    /* put packet in window buffer */
    /* windowlast will always be 0 for alternating bit; but not for GoBackN */
    windowlast = (windowlast + 1) % WINDOWSIZE; 
    buffer[windowlast] = sendpkt;
    windowcount++;


    /* send out packet */
    if (TRACE > 0)
      printf("Sending packet %d to layer 3\n", sendpkt.seqnum);
    tolayer3 (A, sendpkt);

    if (windowcount == 1) {
      starttimer(A, RTT);
  }
    /* get next sequence number, wrap back to 0 */
    A_nextseqnum = (A_nextseqnum + 1) % SEQSPACE;  
  }
  /* if blocked,  window is full */
  else {
    if (TRACE > 0)
      printf("----A: New message arrives, send window is full\n");
    window_full++;
  }
}


/* called from layer 3, when a packet arrives for layer 4 
   In this practical this will always be an ACK as B never sends data.
*/
void A_input(struct pkt packet)
{
  /* if received ACK is not corrupted */ 
  if (!IsCorrupted(packet)) {
    if (TRACE > 0)
      printf("----A: uncorrupted ACK %d is received\n",packet.acknum);
    if (!ACKed[packet.acknum]){
      if (TRACE > 0)
        printf("----A: ACK %d is not a duplicate\n",packet.acknum);
        }
      new_ACKs++;  
      acked[packet.acknum] = true;

      if (packet.acknum == buffer[windowfirst].seqnum) {
        while (wincount  > 0 && acked[buffer[windowfirst].seqnum]) {
          windowfirst = (windowfirst + 1) % WINDOWSIZE;
          windowcount--;
        }
        stoptimer(A);
        if (windowcount > 0) 
        starttimer(A, RTT);
      }

    /*check if wincount bigger than the next*/
    else if (TRACE > 0) 
        printf("A: sliding window, packet %d acknowledged\n", buffer[windowfirst].seqnum);                          
  }
  else if (TRACE > 0)
      printf ("----A: corrupted ACK is received, do nothing!\n");
}

/* called when A's timer goes off */
void A_timerinterrupt(void)
{
  if (TRACE > 0)
    printf("----A: time out,resend packets!\n");
      if (TRACE > 0)
          printf ("---A: resending packet %d\n",  buffer[windowfirst].seqnum);
    
    tolayer3(A,buffer[windowfirst]);
    packets_resent++;

  if (windowcount > 0)
    starttimer(A,RTT);
}       



/* the following routine will be called once (only) before any other */
/* entity A routines are called. You can use it to do any initialization */
void A_init(void)
{
  int i;  
  /* initialise A's window, buffer and sequence number */
  A_nextseqnum = 0;  /* A starts with seq num 0, do not change this */
  windowfirst = 0;
  windowlast = -1;   /* windowlast is where the last packet sent is stored.  
		     new packets are placed in winlast + 1 
		     so initially this is set to -1
		   */
  windowcount = 0;

  for (i = 0; i < SEQSPACE; i++) {
    acked[i] = false;             
  }
}



/********* Receiver (B)  variables and procedures ************/

static int expectedseqnum; /* the sequence number expected next by the receiver */
static int B_nextseqnum;   /* the sequence number for the next packets sent by B */
static struct pkt recv_buffer[SEQSPACE]; /*buffer to store out-of-order packets*/
static bool received[SEQSPACE];    /*track which seqnums have been received*/


/* called from layer 3, when a packet arrives for layer 4 at B*/
void B_input(struct pkt packet)
{
  struct pkt sendpkt;
  int i;
  int last_ack;

  /* Check if packet is not corrupted */
  if (!IsCorrupted(packet)) {

    /* Check if packet is within the receive window */
    int in_window = 0;
    if (expectedseqnum + WINDOWSIZE < SEQSPACE) {
      in_window = (packet.seqnum >= expectedseqnum && packet.seqnum < expectedseqnum + WINDOWSIZE);
    } else {
      in_window = (packet.seqnum >= expectedseqnum || packet.seqnum < (expectedseqnum + WINDOWSIZE) % SEQSPACE);
    }

    if (in_window) {
      if (TRACE > 0)
        printf("----B: packet %d correctly received (within window), sending ACK\n", packet.seqnum);
      packets_received++;

      /* Store the packet and mark as received */
      recv_buffer[packet.seqnum] = packet;
      received[packet.seqnum] = true;

      /* Deliver all in-order packets from expectedseqnum */
      while (received[expectedseqnum]) {
        tolayer5(B, recv_buffer[expectedseqnum].payload);
        received[expectedseqnum] = false;
        expectedseqnum = (expectedseqnum + 1) % SEQSPACE;
      }

      /* Send ACK for this packet */
      sendpkt.acknum = packet.seqnum;
    } else {
      /* Packet is outside window: discard but resend ACK for last valid */
      if (TRACE > 0)
        printf("----B: packet %d outside window, sending duplicate ACK\n", packet.seqnum);
      last_ack = (expectedseqnum == 0) ? SEQSPACE - 1 : expectedseqnum - 1;
      sendpkt.acknum = last_ack;
    }
  } else {
    /* Packet is corrupted: send duplicate ACK */
    if (TRACE > 0)
      printf("----B: packet corrupted, sending duplicate ACK\n");
    last_ack = (expectedseqnum == 0) ? SEQSPACE - 1 : expectedseqnum - 1;
    sendpkt.acknum = last_ack;
  }

  /* create packet */
  sendpkt.seqnum = 0;
    
  /* we don't have any data to send.  fill payload with 0's */
  for ( i=0; i<20 ; i++ ) 
    sendpkt.payload[i] = '0';  

  /* computer checksum */
  sendpkt.checksum = ComputeChecksum(sendpkt); 

  /* send out packet */
  tolayer3 (B, sendpkt);
}

/* the following routine will be called once (only) before any other */
/* entity B routines are called. You can use it to do any initialization */
void B_init(void)
{
  int i;
  expectedseqnum = 0;
  B_nextseqnum = 1;
    for (i = 0; i < SEQSPACE; i++) {
    received[i] = false;
  }
}

/******************************************************************************
 * The following functions need be completed only for bi-directional messages *
 *****************************************************************************/

/* Note that with simplex transfer from a-to-B, there is no B_output() */
void B_output(struct msg message)  
{
}

/* called when B's timer goes off */
void B_timerinterrupt(void)
{
}

