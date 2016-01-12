#include "jhuff.hpp"

double eob_cost[63];       // cost of going to EOB from current state
double dist[64][16];        // store pre-calculated distortion
double d[64][11];             // mean square distortion of the 64 coef. quantized to level s
double ending_cost[63]; // cost of ending the block after the current state 
double cost;                       // temporal cost to current state for one path 
double dist_inc;				  // distorting increment from incoming state to current state
double curr_min;               // current minimum cost to present state 
double tempd;
extern double ent_dc[12];						  // entropy of DC size group
extern double ent_ac[256];						  // entropy of each (r,s) pair

double maxnumber = DBL_MAX;

/* gloabl variables */
extern long huff_put_buffer; /* buffer for accumulating the current bits */
extern int huff_put_bits;    /* current number of bits in the buffer */
extern int bytes_in_buffer;  /* current bytes in buffer */
extern char *output_buffer;  /* output buffer which is used to store the Huffman codes for whole image */
extern int recon_index[ROWS][COLS];
extern short int zigzag[8][8];
int final_nzc;
extern int s_min[11], s_max[11];
int c_abs[64];              // absolute values of the DCT coefs. in one block 
extern int qtbl_1d[64], qtbl_1d_thrld[64], Q[64];
int id[64][11];              // the index to send when the coef. is quantized to level s
int indsi[64];                // stort the size of each index

extern double enc_add_cost[64][16][11];
extern double dist_inc_cost[64][16][11];

int zz[64];

// function fake_blockencode() is used to get the statistics for customized Huffman table
void fake_blockencode(int *zz, int *counts, int *totalpair, int *dccounts)
{
	register int temp, nbits;
	register int k, r;

	/* encode DC coefficient */
	temp = zz[0];
	if (temp < 0)
		temp = -temp;   /* temp is the absulate value of input coefficient */

	  /* find the number of bits needed for the magnitude of the coeffcient */
	nbits = 0;
	while (temp)
	{
		nbits++;
		temp >>= 1;
	}
	dccounts[nbits]++;

	/* encode AC coefficients (refer to Figure F.1.2.2 */
	r = 0;   /* r is the run length of zero */
	for (k = 1; k < 64; k++)
	{
		if ((temp = zz[k]) == 0)
			r++;
		else
		{/* if run length is greater than 15, emit special code 0xF0 */
			while (r > 15)
			{
				counts[15 << 4]++;
				*totalpair = *totalpair + 1;
				r = r - 16;
			}
			if (temp < 0)
				temp = -temp;

			/* find the number of bits needed for the magnitude of the coefficient */
			nbits = 1; /* Nonzero AC value  is at least 1 bits long */
			while (temp >>= 1)
				nbits++;

			/* Count Huffman symbol for (run, size) */
			counts[(r << 4) + nbits]++;
			*totalpair = *totalpair + 1;
			r = 0;
		}
	}
	/* if the last coefficients are zero, emit an end-of-block code */
	if (r > 0)
	{
		counts[0]++;
		*totalpair = *totalpair + 1;
	}
}

int customized_table(int *freq, unsigned char *returnbits, unsigned char *val)
{
# define MAX_CODELEN 32 
	unsigned char bits[MAX_CODELEN + 1];
	int codesize[257];		/* codesize[k] = code length of symbol k */
	int others[257];		/* next symbol in current branch of tree */
	int c1, c2;
	int k, i, j;
	int v;

	/* This algorithm is explained in section K.2 of the JPEG standard */
	for (i = 0; i < 33; i++)
		bits[i] = (unsigned char)0;  // '0'

	for (i = 0; i < 257; i++)
	{
		codesize[i] = 0;
		others[i] = -1;		/* init links to empty */
	}

	freq[256] = 1;		/* make sure 256 has a nonzero count */

	// refer Figure K.1 of ISO 10918-1
	for (;;)
	{
		/* Find the smallest nonzero frequency, set c1 = its symbol */
		/* In case of ties, take the larger symbol number */
		c1 = -1;
		v = 1 << 24;
		for (i = 0; i <= 256; i++)
		{
			if (freq[i] && freq[i] <= v)
			{
				v = freq[i];
				c1 = i;
			}
		}

		/* Find the next smallest nonzero frequency, set c2 = its symbol */
		/* In case of ties, take the larger symbol number */
		c2 = -1;
		v = 1 << 24;
		for (i = 0; i <= 256; i++)
		{
			if (freq[i] && freq[i] <= v && i != c1)
			{
				v = freq[i];
				c2 = i;
			}
		}

		/* Done if we've merged everything into one frequency */
		if (c2 < 0)
			break;

		/* Else merge the two counts/trees */
		freq[c1] += freq[c2];
		freq[c2] = 0;

		/* Increment the codesize of everything in c1's tree branch */
		codesize[c1]++;
		while (others[c1] >= 0)
		{
			c1 = others[c1];
			codesize[c1]++;
		}

		others[c1] = c2;		/* chain c2 onto c1's tree branch */

		/* Increment the codesize of everything in c2's tree branch */
		codesize[c2]++;
		while (others[c2] >= 0)
		{
			c2 = others[c2];
			codesize[c2]++;
		}
	}

	/* Now count the number of symbols of each code length */
	// refer to Figure K.2 of ISO 10918-1
	for (i = 0; i <= 256; i++)
		if (codesize[i])
			bits[codesize[i]]++;

	// Adjust the BITS list so that no code is longer than 16 bits
	// refer to Figure K.3 of ISO 10918-1
	for (i = MAX_CODELEN; i > 16; i--)
	{
		while (bits[i] > 0)
		{
			j = i - 2;		/* find length of new prefix to be used */
			while (bits[j] == 0)
				j--;

			bits[i] -= 2;		/* remove two symbols */
			bits[i - 1]++;		/* one goes in this length */
			bits[j + 1] += 2;		/* two new symbols in this length */
			bits[j]--;   		/* symbol of this length is now a prefix */
		}
	}

	/* Remove the count for the pseudo-symbol 256 from the largest codelength */
	while (bits[i] == 0)		/* find largest codelength still in use */
		i--;
	bits[i]--;

	/* Return final symbol counts (only for lengths 0..16) */
	memcpy(returnbits, bits, 17 * sizeof(unsigned char));

	// generate the list HUFFVAL (refer to Figure K.4 of ISO 10918-1
	/* Return a list of the symbols sorted by code length
	   It's not real clear to me why we don't need to consider the codelength
	   changes made above, but the JPEG spec seems to think this works. */
	k = 0;
	for (i = 1; i <= MAX_CODELEN; i++)
	{
		for (j = 0; j <= 255; j++)
		{
			if (codesize[j] == i)
			{
				val[k] = (unsigned char)j;
				k++;
			}
		}
	}

	return(k);
}

int quantize1c(int coef, int posi)
{
	register int temp;
	if (coef < 0)
	{
		tempd = -coef;
		tempd += qtbl_1d[posi] / 2;
		temp = (int)tempd / qtbl_1d[posi];
		return (-temp);
	}
	else
	{
		tempd = coef + qtbl_1d[posi] / 2;
		temp = (int)tempd / qtbl_1d[posi];
		return (temp);
	}
}

// record the state information for the current optimal path
void record_inf(statenode *state, int posi, int rl, int si, int ind, double inc_dist, double cost)
{
	//	curr_min=cost;
	state[posi].r = rl;
	state[posi].s = si;
	state[posi].index = ind;
	state[posi].dist_cum = state[posi - rl - 1].dist_cum + inc_dist;
	state[posi].rate_cum = state[posi - rl - 1].rate_cum + ent_ac[(rl << 4) + si];
	state[posi].min_cost = cost;
}



void update_cost(int i, int j, int size, double dist, double d, int ind, statenode* state)
{
	double dist_inc_f, cost_f;
	dist_inc_f = dist + d;
	cost_f = state[i - j - 1].min_cost + dist_inc_f + ent_ac[(j << 4) + size];
	if (cost_f < curr_min)
	{
		record_inf(state, i, j, size, ind, dist_inc_f, cost_f);
		curr_min = cost_f;
	}
}



void restore_blk(int i, int j, statenode *state, int *stack, int sp)
{
	register int u, v, r, temp;
	int curr;

	//zz[0]=state[0].index;
	if (sp == 0)
		for (u = 1; u < 64; u++)
			zz[u] = 0;
	else
	{
		sp = sp - 1;
		curr = 1;
		while (sp > 0)
		{
			r = state[stack[sp]].r;
			temp = state[stack[sp]].index;
			if (r == 0)
			{
				zz[curr] = temp;
				curr++;
			}
			else
			{
				for (u = curr; u < curr + r; u++)
					zz[u] = 0;
				zz[curr + r] = temp;
				curr = curr + r + 1;
			}
			sp = sp - 1;
		}

		r = state[stack[sp]].r;
		temp = state[stack[sp]].index;
		for (u = curr; u < curr + r; u++)
			zz[u] = 0;
		zz[curr + r] = temp;
		if (stack[sp] != 63)
			curr = curr + r + 1;
		for (u = curr; u < 64; u++)
			zz[u] = 0;
	}

	// change the zigzag sequence zz[] back to 8x8 block 
	// do not restore DC
	for (v = 1; v < 8; v++)
		recon_index[i * 8][j * 8 + v] = zz[zigzag[0][v]];
	for (u = 1; u < 8; u++)
		for (v = 0; v < 8; v++)
			recon_index[i * 8 + u][j * 8 + v] = zz[zigzag[u][v]];
}


/*
void search_min_cost(statenode* state_a0, statenode* state_b0, int i, int j)
{
	int size;
	switch (indsi[i])
	{
	 case 0:
	  for (size=1; size<3; size++)
		update_cost(i,j,size,dist[i][j],d[i][size], id[i][size],state_a0);
	 break;
	 case 1:
	  for (size=1; size<4; size++)
		update_cost(i,j,size,dist[i][j],d[i][size], id[i][size],state_a0);
	 break;
	 case 10:
	  for (size=10; size>8; size--)
		update_cost(i,j,size,dist[i][j],d[i][size], id[i][size],state_a0);
	  break;
	 default: //2~9
	  for (size=indsi[i]-1; size<indsi[i]+2; size++)
		update_cost(i,j,size,dist[i][j],d[i][size], id[i][size],state_a0);
	 } // end of switch


}*/

//optimize each 8x8 block independently 
//(aa[i][j], bb[i][j], zz_coef, state, stack/*64个int*/, &point/*空*/, ac_counts/*全零*/, &total/*totalpair*/, &distortion, &rate_tle, &minimumcost)
void opti_block(int row_b, int col_b, int *dctcoef_1b, statenode *state, int *stack, int *pointer,
	int *counts, int *total, double *distortion_t, double *rate_total, double *cost_t, bool block_type, int c)
{
	register int i, j, k, size;
	int sp;
	register int tmp, ind, s;

	statenode final_state;

	//initialize the first column of dist[][] (SAME for all block, go outside later)
	for (i = 2; i < 64; i++)
		dist[i][0] = 0;

	//for each 8x8 block 
	//use the absolute value instead of MSE as the distortion criterion
	for (i = 0; i < 64; i++)
	{
		c_abs[i] = (dctcoef_1b[i] < 0) ? (-dctcoef_1b[i]) : dctcoef_1b[i];//初始化系数的绝对值数组
		state[i].min_cost = 0;
	}

	//calculate the costs of going to EOB from the ith state
	eob_cost[62] = sqr(c_abs[63]) + ent_ac[0];//	for (int k = 0;k < 256; k++)
												//		ent_ac[k] = sigmasquare[aa[i][j]][bb[i][j]] * ac_r[k];
	for (i = 62; i > 0; i--)  // state 63 does not follow EOB
		eob_cost[i - 1] = eob_cost[i] + sqr(c_abs[i]);
	// initialize for this block
	ending_cost[0] = eob_cost[0];
	final_nzc = 0;

	// calculate the different distortion (squared error) for current block
	for (i = 2; i < 16; i++)     // for i=2~15
		for (j = 1; j < i; j++)   // for j=1~(i-1)
			dist[i][j] = dist[i][j - 1] + sqr(c_abs[i - j]);//计算每个路径的代价
	for (i = 16; i < 64; i++)    // for i=16~63
		for (j = 1; j < 16; j++)  // for j=1~15
			dist[i][j] = dist[i][j - 1] + sqr(c_abs[i - j]);

	// calculate d1(i,s) and id(i,s)
	for (i = 1; i < 64; i++)
	{
		ind = quantize1c(dctcoef_1b[i], i);//每个系数量化
		tmp = ind;
		if (tmp < 0)
			tmp = -tmp;
		s = 0;
		while (tmp)
		{
			s++;
			tmp >>= 1;
		}
		indsi[i] = s;
		d[i][s] = sqr(dctcoef_1b[i] - ind*qtbl_1d[i]);//c-q.id
		id[i][s] = ind;
		switch (s)
		{
		case 0:
			for (size = 1; size < 3; size++)
			{
				d[i][size] = sqr(c_abs[i] - s_min[size] * qtbl_1d[i]);//s_min把size映射到一个具体的系数值
				id[i][size] = (dctcoef_1b[i] < 0) ? (-s_min[size]) : s_min[size];
			}
			break;
		case 1:
			for (size = 2; size < 4; size++)
			{
				d[i][size] = sqr(c_abs[i] - s_min[size] * qtbl_1d[i]);
				id[i][size] = (dctcoef_1b[i] < 0) ? (-s_min[size]) : s_min[size];
			}
			break;
		case 10:
			d[i][9] = sqr(c_abs[i] - s_max[9] * qtbl_1d[i]);
			id[i][9] = (dctcoef_1b[i] < 0) ? (-s_max[9]) : s_max[9];
			break;
		default: //2~9 
			d[i][s - 1] = sqr(c_abs[i] - s_max[s - 1] * qtbl_1d[i]);
			id[i][s - 1] = (dctcoef_1b[i] < 0) ? (-s_max[s - 1]) : s_max[s - 1];
			d[i][s + 1] = sqr(c_abs[i] - s_min[s + 1] * qtbl_1d[i]);
			id[i][s + 1] = (dctcoef_1b[i] < 0) ? (-s_min[s + 1]) : s_min[s + 1];
		}
	}
	// for each state i (1~63), find the minimum cost to this state
	//cout << block_type << endl;
	for (i = 1; i <= (block_type == 0 ? 63 : 63); i++)
	{
		curr_min = maxnumber;   // initialized for each new state

		k = (i > 15) ? 15 : (i - 1);  // first 15 states do not have full incoming states

		if (i >= c && block_type == 1)//k=1就是把他们都不量化为0
		{
			k = 1;
		}
		// for each incoming state j (j is from 0 to maximum incoming states)
		for (j = 0; j <= k; j++)
		{
			switch (indsi[i])
			{
			case 0:
				for (size = 1; size < ((block_type == 0 || i >= c) ? 2 : 3); size++)
				{
					dist_inc = dist[i][j] + d[i][size];
					cost = state[i - j - 1].min_cost + dist_inc + ent_ac[(j << 4) + size];
					if (cost < curr_min)
					{
						record_inf(state, i, j, size, id[i][size], dist_inc, cost);
						curr_min = cost;
					}
				}
				break;
			case 1:
				for (size = 1; size < 4; size++)
				{
					dist_inc = dist[i][j] + d[i][size];
					cost = state[i - j - 1].min_cost + dist_inc + ent_ac[(j << 4) + size];
					if (cost < curr_min)
					{
						record_inf(state, i, j, size, id[i][size], dist_inc, cost);
						curr_min = cost;
					}
				}
				break;
			case 10:
				for (size = 10; size > (block_type == 1 && i >=c ? 9 : 8); size--)
				{
					dist_inc = dist[i][j] + d[i][size];
					cost = state[i - j - 1].min_cost + dist_inc + ent_ac[(j << 4) + size];
					if (cost < curr_min)
					{
						record_inf(state, i, j, size, id[i][size], dist_inc, cost);
						curr_min = cost;
					}
				}
				break;

			default: //2~9 
				for (size = (block_type==1 && i >= c ? indsi[i] : indsi[i] - 1); size < indsi[i] + 2; size++)
				{
					dist_inc = dist[i][j] + d[i][size];
					cost = state[i - j - 1].min_cost + dist_inc + ent_ac[(j << 4) + size];
					if (cost < curr_min)
					{
						record_inf(state, i, j, size, id[i][size], dist_inc, cost);
						curr_min = cost;
					}
				}

			} // end of switch

		} // end of j loop for each one incoming state  

	  // for each state, find the cost of going EOB after this nonzero state
		if (i < block_type == 0 ? c : 63)
		{
			ending_cost[i] = state[i].min_cost + eob_cost[i];
			if (ending_cost[i] < ending_cost[final_nzc])
			{
				final_nzc = i;
				final_state.r = state[i].r;
				final_state.s = state[i].s;
				final_state.index = state[i].index;
				final_state.dist_cum = state[i].dist_cum;
				final_state.rate_cum = state[i].rate_cum;
				final_state.min_cost = state[i].min_cost;
			}
		}
		// consider (15,0) case for i>=16 (consider this AFTER ending-cost calculation!)
		if ((i > 15) && (i < 63) && (i != final_nzc))
		{
			dist_inc = dist[i][15] + sqr(c_abs[i]);
			cost = state[i - 16].min_cost + dist_inc + ent_ac[0xF0];
			if (cost < curr_min)
			{
				record_inf(state, i, 15, 0, 0, dist_inc, cost);
				curr_min = cost;
			}
		}

		if (curr_min < 0)
			printf("row_b=%d, col_b=%d, i=%d\n", row_b, col_b, i);

	} // end of i loop for the calculation of the minimum cost for one state 

	/*for (i = 1; i < 64; i++)
	{
		cout << state[i].r << " " << state[i].s << endl;
	}*/

	// find the optimal path for the current block
	sp = 0;
	if (ending_cost[final_nzc] < state[63].min_cost)  // EOB is the last code of the block
	{
		if (final_nzc != 0)
		{
			state[final_nzc].r = final_state.r;
			state[final_nzc].s = final_state.s;
			state[final_nzc].index = final_state.index;
			state[final_nzc].dist_cum = final_state.dist_cum;
			state[final_nzc].rate_cum = final_state.rate_cum;
			state[final_nzc].min_cost = final_state.min_cost;
		}

		stack[sp] = final_nzc;
		*distortion_t = *distortion_t + state[final_nzc].dist_cum + ending_cost[final_nzc] - state[final_nzc].min_cost - ent_ac[0];
		*rate_total = *rate_total + state[final_nzc].rate_cum + ent_ac[0];
		*cost_t = *cost_t + ending_cost[final_nzc];
		counts[0]++; // number of EOB increments!
		//printf("counts[0]=%d\n",counts[0]);
		*total = *total + 1;
	}
	else if (block_type != 0)        // the 63th AC coef. is the non-zero
	{
		stack[sp] = 63;
		*distortion_t = *distortion_t + state[63].dist_cum;
		*rate_total = *rate_total + state[63].rate_cum;
		*cost_t = *cost_t + state[63].min_cost;
		//printf("One block ending from 63th state!\n");
	}
	else if (block_type == 0)
	{
		if (final_nzc != 0)
		{
			state[final_nzc].r = final_state.r;
			state[final_nzc].s = final_state.s;
			state[final_nzc].index = final_state.index;
			state[final_nzc].dist_cum = final_state.dist_cum;
			state[final_nzc].rate_cum = final_state.rate_cum;
			state[final_nzc].min_cost = final_state.min_cost;
		}

		stack[sp] = final_nzc;
		*distortion_t = *distortion_t + state[final_nzc].dist_cum + ending_cost[final_nzc] - state[final_nzc].min_cost - ent_ac[0];
		*rate_total = *rate_total + state[final_nzc].rate_cum + ent_ac[0];
		*cost_t = *cost_t + ending_cost[final_nzc];
		counts[0]++; // number of EOB increments!
					 //printf("counts[0]=%d\n",counts[0]);
		*total = *total + 1;
	}
	//find the optimal path backward
	while (stack[sp] != 0)
	{
		// count the new (run, size) pair
		counts[(state[stack[sp]].r << 4) + state[stack[sp]].s]++;
		*total = *total + 1;
		sp = sp + 1;
		stack[sp] = stack[sp - 1] - state[stack[sp - 1]].r - 1;
		if (stack[sp] < 0)
		{
			printf("invalid case: not start from DC coef.!\n");
			break;
		}
	}
	if (stack[sp] != 0)
		printf("Wrong path!\n");
	*pointer = sp;


	//restore the optimization image indices based on the run-size pair.
	restore_blk(row_b, col_b, state, stack, sp);
}