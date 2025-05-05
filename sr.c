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
#define WINDOWSIZE 6    /* the maximum number of buffered unalready_acked packet */
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
static bool already_acked[SEQSPACE];


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
  // Check if the received ACK packet is corrupted
  if (IsCorrupted(packet)) {
    if (TRACE > 0)
      printf("----A: corrupted ACK is received, do nothing!\n");
    return;
  }

  if (TRACE > 0)
    printf("----A: uncorrupted ACK %d is received\n", packet.acknum);

  // If this ACK has not been received before
  if (acked[packet.acknum] == false) {
    acked[packet.acknum] = true;
    new_ACKs++;

    if (TRACE > 0)
      printf("----A: ACK %d is not a duplicate\n", packet.acknum);

    // If this ACK matches the first packet in the current window
    if (packet.acknum == buffer[windowfirst].seqnum) {
      int i = 0;
      // Slide the window forward as long as the packets are acknowledged
      while (i < windowcount && acked[buffer[windowfirst].seqnum]) {
        windowfirst = (windowfirst + 1) % WINDOWSIZE;
        i++;
      }
      windowcount -= i;

      // Stop the timer since the earliest unacked packet is now acked
      stoptimer(A);

      // If there are still unacked packets, restart the timer
      if (windowcount > 0) {
        starttimer(A, RTT);
      }
    }
  } 
  else {
    // If it's a duplicate ACK, ignore it
    if (TRACE > 0)
      printf("----A: duplicate ACK received, do nothing!\n");
  }
}

/* called when A's timer goes off */
void A_timerinterrupt(void)
{
  if (TRACE > 0)
    printf("----A: time out,resend packets!\n");

  if (windowcount > 0) {
    if (TRACE > 0)
      printf ("---A: resending packet %d\n", buffer[windowfirst].seqnum);
    
  tolayer3(A, buffer[windowfirst]);
  packets_resent++;
  starttimer(A,RTT);
    }
}       



/* the following routine will be called once (only) before any other */
/* entity A routines are called. You can use it to do any initialization */
void A_init(void)
{
  /* initialise A's window, buffer and sequence number */
  A_nextseqnum = 0;  /* A starts with seq num 0, do not change this */
  windowfirst = 0;
  windowlast = -1;   /* windowlast is where the last packet sent is stored.  
		     new packets are placed in winlast + 1 
		     so initially this is set to -1
		   */
  windowcount = 0;
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
  int seq = packet.seqnum;
  int corrupted = IsCorrupted(packet);

  /* Ignore corrupted packets */
  if (corrupted) {
    return;
  }

  if (TRACE > 0)
    printf("----B: packet %d is correctly received, send ACK!\n", seq);
  packets_received++;

  // If this packet hasn't been received before
  if (received[seq] == false) {
    received[seq] = true;

    // Copy payload to buffer
    int j;
    for (j = 0; j < 20; j++) {
      recv_buffer[seq].payload[j] = packet.payload[j];
    }
  }
      
  while (true) {
    if (!received[expectedseqnum])
      break;
  
    tolayer5(B, recv_buffer[expectedseqnum].payload);
    received[expectedseqnum] = false;
    expectedseqnum = (expectedseqnum + 1) % SEQSPACE;
    }
  
  sendpkt.seqnum = NOTINUSE;
  sendpkt.acknum = packet.seqnum;

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

  expectedseqnum = 0;

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

