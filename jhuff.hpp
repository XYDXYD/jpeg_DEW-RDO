#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>
#include <iostream>
#include <float.h>

#define ROWS 512
#define COLS 512
#define sqr(x) ((x)*(x))

using namespace std;
/* jhuff.h is the head file to define Huffman table structure */
typedef struct
{
	unsigned char bits[17];  /* bits[k] stores the number of symbols whose codes
						  are k bits long. bits[0] is unused */
	unsigned char huffval[256]; /* The symbols in order of increasing code length */

	/* encode tables */
	unsigned int ehufco[256]; /* Huffman code for each symbol */
	char ehufsi[256];         /* length of each code */

	/* decoding tables (1st element of each array are unused */
	unsigned int mincode[17];
	long maxcode[18];
	short valptr[17]; /*index of 1st symbol of different length in huffval[] */
}HUFF_TBL;

typedef struct
{
	short int r;         // run
	short int s;         // size
	double min_cost;     // minimum cost upto this state
	double dist_cum;        // cumulative distortion to this state
	double rate_cum;     // cumulative rate to this state
	int index;           // the quantizied index that needs to be sent
} statenode;


