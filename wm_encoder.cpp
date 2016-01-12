#include "jhuff.hpp"
#include <math.h>

#define rdt 4
extern double ent_ac[256];
extern int qtbl_1d[64], qtbl_1d_thrld[64], Q[64],recon_index[ROWS][COLS],s_min[11], s_max[11]; 
extern short int zigzag[8][8];
extern void init_jwc_block(int *dctcoef_1b, int *dctcoef_2b);
extern void search_min_cost(statenode* state_a0, statenode* state_b0,int i, int j);
extern void update_cost(int i,int j,int size, double dist, double d, int ind, statenode* state);
extern void update_cost_2(int i,int j,int size, double dist, double d, int ind, statenode* state);
extern void record_inf(statenode *state, int posi, int rl, int si, int ind, double inc_dist, double cost);
extern void restore_blk(int i, int j, statenode *state,int *stack,int sp);
extern void update_qtbl();
extern int  quantize1c(int coef, int posi);

int c_abs[64],c_abs_2[64];                 // absolute values of the DCT coefs. in one block 
int id[64][11], id_2[64][11];              // the index to send when the coef. is quantized to level s
int indsi[64], indsi_2[64];                // stort the size of each index
int final_nzc, final_nzc_2;				   // indicate the position of the final non-zero coefficient
double eob_cost[63], eob_cost_2[63];       // cost of going to EOB from current state
double ending_cost[63], ending_cost_2[63]; // cost of ending the block after the current state 
double cost, cost_2;                       // temporal cost to current state for one path 
double dist[64][16],dist_2[64][16];        // store pre-calculated distortion
double dist_inc, dist_inc_2;               // distorting increment from incoming state to current state
double curr_min, curr_min_2;               // current minimum cost to present state 
double maxnumber=1e20;
double tempd;
double d[64][11], d_2[64][11];             // mean square distortion of the 64 coef. quantized to level s
double enc_add_cost[64][16][11],  enc_add_cost_2[64][16][11];
double dist_inc_cost[64][16][11], dist_inc_cost_2[64][16][11];

struct node_state
{ 
  int block_a_graph_no;
  int block_b_graph_no;
};

//optimize two 8x8 block simultaneously
void opti_two_block(int *wm_bit, int *wm_pos, int wm_len, int row_a, int col_a,int row_b, int col_b,
					int *dctcoef_1b, int *dctcoef_2b, int *stack, int *pointer, int *counts, int *total, 
					double *distortion_t, double *rate_total, double *cost_t, int tr_nod_no,
					tree_node *block_a_tree, tree_node *block_b_tree)
{
 
 int tmp,ind1,ind2,s, i,j,k;
 int run_1[11], run_2[11],size,size2, sp_a,sp_b;
 int Ind_Threshold, x_tmp,x,y,xl,xr,tmp_threshold;
 int final_nzc_a0, final_nzc_b0,kk,end_right,t1;
 int thr,a1,b1,a2,b2,m,mm, k1,t2,nd, sno,jj,kkk,ttt,j1,sp;
 int path_a_no,path_b_no,v1;
 int *path_a_no_1=  new int[wm_len];
 int *path_b_no_1=  new int[wm_len];
 int *wm_nocost_pos=new int[wm_len];
 int **num_comb=new int *[wm_len];

 double tmp_min,tmp_min_2,totalwmcost,tmp_cost, tempcost;
 double a0_cost, b0_cost, totalcost;
 double *part_cost_1=new double[11];
 double *part_cost_2=new double[11];
 double ending_cost_a0[63], ending_cost_b0[63];
 double *tmp_cost_1 = new double[wm_len];
 node_state ***node= new node_state **[wm_len];

 statenode *state_a0= new statenode[64];
 statenode *state_b0= new statenode[64];
  
 for (i=0; i<wm_len; i++)
	 num_comb[i]=new int[4];

 // compute the number of combinaions for each watermarking state
 // watermark state 0
 if(wm_bit[0]==0) 
 {
    num_comb[0][0]=1;  num_comb[0][1]=0;   num_comb[0][2]=0;  	num_comb[0][3]=1;
 }
 else
 {  
	num_comb[0][0]=0;  num_comb[0][1]=1;   num_comb[0][2]=1;   num_comb[0][3]=1;
 }

 // other watermark states
 for(i=1; i<wm_len; i++)
 {
   	if(wm_bit[i]==0) 
	{
	  num_comb[i][0] =num_comb[i-1][0] + num_comb[i-1][1] + num_comb[i-1][2] + num_comb[i-1][3];
	  num_comb[i][1] =0; num_comb[i][2]=0;    num_comb[i][3]=1;
	}
    else
	{
	  num_comb[i][0]=0;   num_comb[i][1]=i+1;  
	  num_comb[i][2]=i+1; num_comb[i][3]=1;
	}
 }
 
 for(i=0; i<wm_len; i++)
 {
	node[i]=new node_state *[4];
	for(j=0;j<4;j++)
	  node[i][j]=new node_state[num_comb[i][j]];
 }

 //initialize watemrarking state
 for(i=0; i<tr_nod_no; i++)
 {
     block_a_tree[i].cost_inwm_status=0;	 block_b_tree[i].cost_inwm_status=0;
	 block_a_tree[i].cost_status_2=0;		 block_b_tree[i].cost_status_2=0;
 }

 //allocate state paths for trellis and tree optimization
 statenode **state_path_a=new statenode * [tr_nod_no];
 statenode **state_path_b=new statenode * [tr_nod_no];

 int *final_nzc_path_a=new int [tr_nod_no];
 int *final_nzc_path_b=new int [tr_nod_no];

 double **state_path_a_end_cost=new double *[tr_nod_no];
 double **state_path_b_end_cost=new double *[tr_nod_no];
  
 for(i=0; i<tr_nod_no; i++)
 {
    state_path_a[i] = new statenode[64];
	state_path_b[i] = new statenode[64];
	state_path_a_end_cost[i] = new double [63];
	state_path_b_end_cost[i] = new double [63];
	
	for(j=0; j<64; j++)
	{
		state_path_a[i][j].min_cost=0;
		state_path_b[i][j].min_cost=0;
	}
 }

 //initilaize watermarking status
 init_jwc_block(dctcoef_1b, dctcoef_2b);

 for (i=0; i<64; i++)
 {
	state_a0[i].min_cost=0;	 
    state_b0[i].min_cost=0;
 }

 state_a0[0].r = 0;  state_b0[0].r = 0;  
 state_a0[0].dist_cum = 0; state_b0[0].dist_cum = 0; 
 state_a0[0].rate_cum = 0; state_b0[0].rate_cum = 0;
 state_a0[0].min_cost = 0; state_b0[0].min_cost = 0; 

 ending_cost_a0[0] = eob_cost[0];		
 ending_cost_b0[0] = eob_cost_2[0];
 final_nzc_a0=0;	final_nzc_b0=0;
 
 // for each state i (1~wm_pos[0]), find the minimum cost to this state
 for (i=1; i<wm_pos[0]; i++)
 {	 
   curr_min = maxnumber;   curr_min_2 = maxnumber; // initialized for each new state

   k=(i>15)?15:(i-1);  // first 15 states do not have full incoming states
   // for each incoming state j (j is from 0 to maximum incoming states)
   for (j=0; j<=k; j++)    search_min_cost(state_a0, state_b0, i, j);
   // for each state, find the cost of going EOB after this nonzero state
   if (i<63)
   {
	 ending_cost_a0[i]=state_a0[i].min_cost + eob_cost[i];
	 if(ending_cost_a0[i]< ending_cost_a0[final_nzc_a0])   	final_nzc_a0=i;
		
	 ending_cost_b0[i]=state_b0[i].min_cost + eob_cost_2[i]; 
	 if(ending_cost_b0[i] < ending_cost_b0[final_nzc_b0])   final_nzc_b0=i;
   } 

   // consider (15,0) case for i>=16 (consider this AFTER ending-cost calculation!)
   if(i>15&&i<63)
   {	
	  if(final_nzc_a0!=i) 	   update_cost(i,15,0,dist[i][15],  sqr(c_abs[i]), 0, state_a0);
	  if(final_nzc_b0!=i)      update_cost_2(i,15,0,dist_2[i][15],sqr(c_abs_2[i]),0,state_b0);  
   }

   if ((curr_min<0)||(curr_min_2<0))  printf("row_b=%d, col_b=%d, i=%d\n", row_b, col_b, i);
 } // end of i loop for the calculation of the minimum cost for one state 

//The first watemarking state status
 for(i=0;i<3;i++)
 {
	memcpy(state_path_a[i], state_a0, wm_pos[0]*sizeof(statenode));
	memcpy(state_path_b[i], state_b0, wm_pos[0]*sizeof(statenode));
	final_nzc_path_a[i]=final_nzc_a0;  	final_nzc_path_b[i]=final_nzc_b0;
	state_path_a_end_cost[i][final_nzc_path_a[i]]=ending_cost_a0[final_nzc_a0];
	state_path_b_end_cost[i][final_nzc_path_b[i]]=ending_cost_b0[final_nzc_b0];
 }

 // compute the first wm embedding point to next embedding point
 kk=0;
 if(kk==wm_len-1) end_right=64;
 else 
 {
    if(wm_pos[kk+1]==wm_pos[kk]+1)  end_right=wm_pos[kk]+1;
	else 	end_right=wm_pos[kk+1];
 }

 if(wm_bit[kk]==0)
 {   // watermarking computing
	curr_min=maxnumber;   	curr_min_2=maxnumber;    i=wm_pos[kk];
	//compute the cost in the case wm_coeffs are quantized to 0 0 
	if(i>15 && i<63)
	{	
	   update_cost(i,15,0,dist[i][15],  sqr(c_abs[i]), 0, state_path_a[0]);
	   update_cost_2(i,15,0,dist_2[i][15],sqr(c_abs_2[i]),0,state_path_b[0]);  
	}
	node[0][0][0].block_a_graph_no=0;		node[0][0][0].block_b_graph_no=0;
	block_a_tree[0].cost_inwm_status=1;		block_b_tree[0].cost_inwm_status=1;

    // compute the first watemrarking state to next watermarking sate-1
	for (i=wm_pos[kk]+1; i<end_right; i++)
	{
	   curr_min=maxnumber;			 curr_min_2=maxnumber;
	   k=(i>15)?15:(i-1);  // first 15 states do not have full incoming states
       // for each incoming state j (j is from 0 to maximum incoming states)
	   for(j=0; j<=k; j++)
	   { //wm_pos[kk]<=15, no cost exists for watermarking state
		 if((j!=(i-wm_pos[kk]-1))||(wm_pos[kk]>15))
		    search_min_cost(state_path_a[0], state_path_b[0],i,j);
	   }  // end of j loop for each one incoming state  
   
	   // for each state, find the cost of going EOB after this nonzero state
	   if (i<63)
	   {
		 state_path_a_end_cost[0][i]=state_path_a[0][i].min_cost+eob_cost[i];
	     if (state_path_a_end_cost[0][i]<state_path_a_end_cost[0][final_nzc_path_a[0]])
		    final_nzc_path_a[0]=i;
		 state_path_b_end_cost[0][i]=state_path_b[0][i].min_cost+eob_cost_2[i];
	     if (state_path_b_end_cost[0][i]<state_path_b_end_cost[0][final_nzc_path_b[0]])
		    final_nzc_path_b[0]=i;
	   } 

	   // consider (15,0) case for i>=16 (consider this AFTER ending-cost calculation!)
	   if (i>15&&i<63)
	   {
		 if(((i-16)!=wm_pos[kk])||(wm_pos[kk]>15))
		 {
		  if(final_nzc_path_a[0]!=i) update_cost(i,15,0,dist[i][15],  sqr(c_abs[i]), 0, state_path_a[0]);
		  if(final_nzc_path_b[0]!=i) update_cost_2(i,15,0,dist_2[i][15],sqr(c_abs_2[i]),0,state_path_b[0]);  
		 }
	   }
       if ((curr_min<0)||(curr_min_2<0))  printf("row_b=%d, col_b=%d, i=%d\n", row_b, col_b, i);
    } // end of i loop for the calculation of the minimum cost for one state 
	block_a_tree[0].cost_status_2=1;			block_b_tree[0].cost_status_2=1;
	/* the above part used for computing the cost a0 and b0*/
  
	/* The next used for computing the cost for a2 and b2 */
 	i=wm_pos[kk];
	for(size=1; size<11; size++)
	{
		 tmp_min=maxnumber;     tmp_min_2=maxnumber;
		 k=(i>15)?15:(i-1);  // first 15 states do not have full incoming states
	     // for each incoming state j (j is from 0 to maximum incoming states)
	     for (j=0; j<=k; j++)
		 {
	       cost=state_path_a[2][i-j-1].min_cost+dist[i][j]+ent_ac[(j<<4)+size];
		   if (cost<tmp_min)
		   {
			   tmp_min=cost;      run_1[size]=j;
		   }
		   cost_2=state_path_b[2][i-j-1].min_cost+dist_2[i][j]+ent_ac[(j<<4)+size];
		   if (cost_2<tmp_min_2)
		   {
			   tmp_min_2=cost_2;   run_2[size]=j;
		   }
		 }//end of j
         
         part_cost_1[size]=tmp_min;    part_cost_2[size]=tmp_min_2;
	}//end of size loop

	ind1=quantize1c(dctcoef_1b[i],i);  ind2=quantize1c(dctcoef_2b[i],i);

	int cross_point=(ind1+ind2)/2;     
	totalwmcost=maxnumber;
    for (size=1; size<11; size++)
	{ 
		 if(cross_point>=0)     
		 {
		    if (s_min[size]>=cross_point)      id[i][size]=s_min[size];
	        else if (s_max[size]<=cross_point) id[i][size]=s_max[size];
	             else id[i][size]=cross_point;
			id_2[i][size]=id[i][size];
	        d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
			d_2[i][size]=sqr(double(dctcoef_2b[i]-id_2[i][size]*qtbl_1d[i]));
		 }
         else 
		 {
		    if (-s_min[size]<=cross_point)     id[i][size]=-s_min[size];
		    else if(-s_max[size]>=cross_point) id[i][size]=-s_max[size];
		         else 	id[i][size]=cross_point;
            id_2[i][size]=id[i][size];
	        d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
		    d_2[i][size]=sqr(double(dctcoef_2b[i]-id_2[i][size]*qtbl_1d[i]));
		 }

          cost=part_cost_1[size]+d[i][size];         cost_2=part_cost_2[size]+d_2[i][size];
		  dist_inc=dist[i][run_1[size]]+d[i][size];  dist_inc_2=dist_2[i][run_2[size]]+d_2[i][size];

		  if((cost+cost_2)<totalwmcost)
		  {
			 totalwmcost=cost+cost_2;
			 record_inf(state_path_a[2],i,run_1[size],size,   id[i][size],    dist_inc,   cost);
			 record_inf(state_path_b[2],i,run_2[size],size, id_2[i][size], dist_inc_2, cost_2);
		  }
	}

	state_path_a_end_cost[2][i]=state_path_a[2][i].min_cost+eob_cost[i];    final_nzc_path_a[2]=i;
	state_path_b_end_cost[2][i]=state_path_b[2][i].min_cost+eob_cost_2[i];  final_nzc_path_b[2]=i; 
	node[0][3][0].block_a_graph_no=2;   node[0][3][0].block_b_graph_no=2;
	block_a_tree[2].cost_inwm_status=1; block_b_tree[2].cost_inwm_status=1;

	for (i=wm_pos[kk]+1; i<end_right; i++)
	{
	   curr_min=maxnumber;    curr_min_2=maxnumber;
	   k=((i-wm_pos[kk])>15)?15:(i-wm_pos[kk]-1);  // first 15 states do not have full incoming states
	   // for each incoming state j (j is from 0 to maximum incoming states)
	   for (j=0; j<=k; j++)
	   	  	search_min_cost(state_path_a[2], state_path_b[2], i,j);
    
	   // for each state, find the cost of going EOB after this nonzero state
	   if (i<63)
	   {
		 state_path_a_end_cost[2][i]=state_path_a[2][i].min_cost+eob_cost[i];
		 if (state_path_a_end_cost[2][i]<state_path_a_end_cost[2][final_nzc_path_a[2]])
	        final_nzc_path_a[2]=i;
	     state_path_b_end_cost[2][i]=state_path_b[2][i].min_cost+eob_cost_2[i];
		 if (state_path_b_end_cost[2][i]<state_path_b_end_cost[2][final_nzc_path_b[2]])
	        final_nzc_path_b[2]=i; 
	   } 
	   // consider (15,0) case for i>=16 (consider this AFTER ending-cost calculation!)
	   if ((i-wm_pos[kk])>15&&i<63)
	   {
		 if(final_nzc_path_a[2]!=i) update_cost(i,15,0,dist[i][15],  sqr(c_abs[i]), 0, state_path_a[2]);
		 if(final_nzc_path_b[2]!=i) update_cost_2(i,15,0,dist_2[i][15],sqr(c_abs_2[i]),0,state_path_b[2]); 
	   }
       if ((curr_min<0)||(curr_min_2<0))  printf("row_b=%d, col_b=%d, i=%d\n", row_b, col_b, i);
    } // end of i loop for the calculation of the minimum cost for one state 
	
	block_a_tree[2].cost_status_2=1; 	 block_b_tree[2].cost_status_2=1;    
}//end if(wm==0)
else
{  
    curr_min=maxnumber;  curr_min_2=maxnumber;

    i=wm_pos[kk];   //compute the cost in the case wm_coeffs are quantized to 0 0 
	if(i>15 && i<63)
	{	
	   update_cost(i,15,0,dist[i][15],  sqr(c_abs[i]), 0, state_path_a[0]);
	   update_cost_2(i,15,0,dist_2[i][15],sqr(c_abs_2[i]),0,state_path_b[0]);  
	}

 	block_a_tree[0].cost_inwm_status=1;  block_b_tree[0].cost_inwm_status=1;

	for (i = wm_pos[kk]+1; i < end_right; i++)
	{
	   curr_min=maxnumber;   curr_min_2=maxnumber;
	   k= (i>15) ? 15:(i-1);  // first 15 states do not have full incoming states
       
	   // for each incoming state j (j is from 0 to maximum incoming states)
	   for(j=0; j<=k; j++)
	   {
	      if((j!=(i-(wm_pos[kk]+1)))||(wm_pos[kk]>15)) //???
		    search_min_cost(state_path_a[0], state_path_b[0], i,j);
	   } 

   	   // for each state, find the cost of going EOB after this nonzero state
	   if (i<63)
	   {
		  state_path_a_end_cost[0][i]=state_path_a[0][i].min_cost+eob_cost[i];
	      if (state_path_a_end_cost[0][i]<state_path_a_end_cost[0][final_nzc_path_a[0]])
		    final_nzc_path_a[0]=i;
	      state_path_b_end_cost[0][i]=state_path_b[0][i].min_cost+eob_cost_2[i];
	      if (state_path_b_end_cost[0][i]<state_path_b_end_cost[0][final_nzc_path_b[0]])
		    final_nzc_path_b[0]=i;
       } 
	   
       // consider (15,0) case for i>=16 (consider this AFTER ending-cost calculation!)
	   if (i>15&&i<63)
	   {
	 	  if(((i-16)!=wm_pos[kk])||(wm_pos[kk]>15))
		  {
		   if(final_nzc_path_a[0]!=i) update_cost(i,15,0,dist[i][15],  sqr(c_abs[i]),  0,state_path_a[0]);
		   if(final_nzc_path_b[0]!=i) update_cost_2(i,15,0,dist_2[i][15],sqr(c_abs_2[i]),0,state_path_b[0]);  
		  }
	   }

       if ((curr_min<0)||(curr_min_2<0))
		 printf("row_b=%d, col_b=%d, i=%d\n", row_b, col_b, i);
    } // end of i loop for the calculation of the minimum cost for one state 

    block_a_tree[0].cost_status_2=1; 	block_b_tree[0].cost_status_2=1;
	// The above is used for computing the cost for a0 and b0

	//Next compute the cost for a1 and b1
	i=wm_pos[kk];      Ind_Threshold=(int)ceil((double)(Q[i]+rdt)/(double)qtbl_1d[i]);
	tmp=Ind_Threshold; 	size=0;
    while(tmp)
	{
	   size++;      tmp>>=1;
    }

	s=size;   	ind1=quantize1c(dctcoef_1b[i],i);    curr_min = maxnumber;
	if(ind1<=0)
	{
	  if(-Ind_Threshold<=ind1)      id[i][size]=-Ind_Threshold;
      else if(-s_max[size]>=ind1)   id[i][size]=-s_max[size];
	  else   id[i][size]=ind1;

	  d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
	  for (size=s+1; size<11; size++)
	  {
	    if (-s_min[size]<=ind1)      id[i][size]=-s_min[size];
	    else if(-s_max[size]>=ind1)  id[i][size]=-s_max[size];
	    else  id[i][size]=ind1;

	    d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
	  }
	}
	else
	{
	  if(ind1<=Ind_Threshold)     id[i][size]=Ind_Threshold;
	  else if(s_max[size]<=ind1)  id[i][size]=s_max[size];
	  else  id[i][size]=ind1;

      d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
	  for (size=s+1; size<11; size++)
	  {
		 if (ind1<=s_min[size])      id[i][size]=s_min[size];
		 else if(s_max[size]<=ind1)  id[i][size]=s_max[size];
		      else  id[i][size]=ind1;
		 d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
	  }
	}
		
    k=(i>15)?15:(i-1);  // first 15 states do not have full incoming states
    // for each incoming state j (j is from 0 to maximum incoming states)
	for (j=0; j<=k; j++)
	  for (size=s; size<11; size++)
	   update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[1]);  
	  	     
	ind2=quantize1c(dctcoef_2b[i],i); 	curr_min_2=maxnumber;
    size=s;
	if(ind2<=0)
	{
	  if(-Ind_Threshold<=ind2)      id_2[i][size]=-Ind_Threshold;
      else if(-s_max[size]>=ind2)   id_2[i][size]=-s_max[size];
	       else   id_2[i][size]=ind2;
	  d_2[i][size]=sqr(double(dctcoef_2b[i]-id_2[i][size]*qtbl_1d[i]));
	 
	  for (size=s+1; size<11; size++)
	  {
	    if (-s_min[size]<=ind2)       id_2[i][size]=-s_min[size];
	      else if(-s_max[size]>=ind2) id_2[i][size]=-s_max[size];
	           else  id_2[i][size]=ind2;
	   d_2[i][size]=sqr(double(dctcoef_2b[i]-id_2[i][size]*qtbl_1d[i]));
	  }
	}
	else
	{
	  if(ind2<=Ind_Threshold)    id_2[i][size]=Ind_Threshold;
	  else if(s_max[size]<=ind2) id_2[i][size]=s_max[size];
	       else id_2[i][size]=ind2;
      d_2[i][size]=sqr(double(dctcoef_2b[i]-id_2[i][size]*qtbl_1d[i]));

	  for (size=s+1; size<11; size++)
	  {
		 if (ind2<=s_min[size])      id_2[i][size]=s_min[size];
		 else if(s_max[size]<=ind2)  id_2[i][size]=s_max[size];
		      else  id_2[i][size]=ind2;
		 d_2[i][size]=sqr(double(dctcoef_2b[i]-id_2[i][size]*qtbl_1d[i]));
	  }
	}
		
    k=(i>15)?15:(i-1);  // first 15 states do not have full incoming states
	// for each incoming state j (j is from 0 to maximum incoming states)
	for (j=0; j<=k; j++)
	   for (size=s; size<11; size++)
	     update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[1]); 
		   
    state_path_a_end_cost[1][i]=state_path_a[1][i].min_cost+eob_cost[i]; 	 final_nzc_path_a[1]=i;
	state_path_b_end_cost[1][i]=state_path_b[1][i].min_cost+eob_cost_2[i];   final_nzc_path_b[1]=i;

	node[0][1][0].block_a_graph_no=0; 	node[0][1][0].block_b_graph_no=1;
	node[0][2][0].block_a_graph_no=1;   node[0][2][0].block_b_graph_no=0;
	block_a_tree[1].cost_inwm_status=1; block_b_tree[1].cost_inwm_status=1;

	for (i=wm_pos[kk]+1; i<end_right; i++)
	{
      curr_min=maxnumber;     curr_min_2=maxnumber;
	  k=((i-wm_pos[kk])>15)?15:(i-wm_pos[kk]-1);  // first 15 states do not have full incoming states
	  // for each incoming state j (j is from 0 to maximum incoming states)
	  for (j=0; j<=k; j++) 
		   search_min_cost(state_path_a[1], state_path_b[1], i,j);
      if (i<63)
	  {
		 state_path_a_end_cost[1][i]=state_path_a[1][i].min_cost+eob_cost[i];
		 if (state_path_a_end_cost[1][i]<state_path_a_end_cost[1][final_nzc_path_a[1]])
	     final_nzc_path_a[1]=i;
	     state_path_b_end_cost[1][i]=state_path_b[1][i].min_cost+eob_cost_2[i];
		 if (state_path_b_end_cost[1][i]<state_path_b_end_cost[1][final_nzc_path_b[1]])
	     final_nzc_path_b[1]=i;
	  } 
	  // consider (15,0) case for i>=16 (consider this AFTER ending-cost calculation!)
	  if (( i-wm_pos[kk])>15 && i<63)
	  {
		 update_cost(i,15,0,dist[i][15],sqr(c_abs[i]),0,state_path_a[1]);
		 update_cost_2(i,15,0,dist_2[i][15],sqr(c_abs_2[i]),0,state_path_b[1]);
      }
	
	  block_a_tree[1].cost_status_2=1;  	 block_b_tree[1].cost_status_2=1;
      if ((curr_min<0)||(curr_min_2<0))  		 printf("row_b=%d, col_b=%d, i=%d\n", row_b, col_b, i);
    } // end of i loop for the calculation of the minimum cost for one state 
      
    // The above used for computing the cost for a1 and b1    // The next compute the cost for a2 and b2.     
    i=wm_pos[kk];
	for (size=1; size<11; size++)
	{
		tmp_min=maxnumber;   		tmp_min_2=maxnumber;
		k=(i>15)?15:(i-1);  // first 15 states do not have full incoming states
	    // for each incoming state j (j is from 0 to maximum incoming states)
	    for (j=0; j<=k; j++)
		{
	       cost=state_path_a[2][i-j-1].min_cost+dist[i][j]+ent_ac[(j<<4)+size];
		   if (cost<tmp_min)
		   {
			   tmp_min=cost;		run_1[size]=j;
		   }
		   cost_2=state_path_b[2][i-j-1].min_cost+dist_2[i][j]+ent_ac[(j<<4)+size];
		   if (cost_2<tmp_min_2)
		   {
			   tmp_min_2=cost_2;    run_2[size]=j;
		   }
		}
		part_cost_1[size]=tmp_min;    part_cost_2[size]=tmp_min_2;
	}

	int ind1_temp,ind2_temp;
	ind1_temp=quantize1c(dctcoef_1b[i],i);
	ind2_temp=quantize1c(dctcoef_2b[i],i);
    if(ind1_temp>=ind2_temp)
	{
		 ind1=ind1_temp; 	ind2=ind2_temp;
	}
	else
    {
		 ind1=-ind1_temp; 	ind2=-ind2_temp;
	}

	totalwmcost=maxnumber;
	for(size=1;size<11;size++) //siz
	{
	     for(size2=1;size2<size;size2++)
		 {
          if((s_max[size2]+s_max[size])*qtbl_1d[i]>=(Q[i]+rdt))
		  {
			if((s_min[size]-s_max[size2])*qtbl_1d[i]>=(Q[i]+rdt))//2
			{
			   if (-s_min[size] <= ind1) 	   id[i][size]=-s_min[size];
			   else if(-s_max[size] >= ind1)   id[i][size]=-s_max[size];
			   else							   id[i][size]=ind1;
					
   	           if(ind2>=0)
			   {
		        if (s_min[size2]>=ind2)        id_2[i][size2]=s_min[size2];
		        else if(s_max[size2]<=ind2)    id_2[i][size2]=s_max[size2];
		        else						   id_2[i][size2]=ind2;
			   }
		       else
			   { 
		        if (-s_min[size2]<=ind2)       id_2[i][size2]=-s_min[size2];
		        else if(-s_max[size2]>=ind2)   id_2[i][size2]=-s_max[size2];
		        else       		               id_2[i][size2]=ind2;
			   }
               
			   if(ind1_temp>=ind2_temp)
			   {
		          d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
		          d_2[i][size2]=sqr(double(dctcoef_2b[i]-id_2[i][size2]*qtbl_1d[i]));
			   }
			   else
			   {
                  d[i][size]=sqr(double(dctcoef_1b[i]+id[i][size]*qtbl_1d[i]));
		          d_2[i][size2]=sqr(double(dctcoef_2b[i]+id_2[i][size2]*qtbl_1d[i]));
			   }
			}
			else //2
			{ 
			  tmp_cost=maxnumber;
			  if((s_max[size]-s_min[size2])*qtbl_1d[i]>=(Q[i]+rdt))//3
			  {
			      if (-s_min[size]<=ind1) 		   x=-s_min[size];
				  else if(-s_max[size]>=ind1)      x=-s_max[size];
			      else     				           x=ind1;

				  if (-s_min[size2]<=ind2)         y=-s_min[size2];
		          else if(-s_max[size2]>=ind2)     y=-s_max[size2];
		          else         					   y=ind2;

				  if((y-x)*qtbl_1d[i]<(Q[i]+rdt))
				  {
					 xl=-s_max[size];  		 xr=-s_min[size];
    				 if((xl+Ind_Threshold)<-s_max[size2]) 	xl=-s_max[size2]-Ind_Threshold;
					 if((xr+Ind_Threshold)>-s_min[size2]) 	xr=-s_min[size2]-Ind_Threshold;

					 x_tmp=ind1+ind2-Ind_Threshold;       x_tmp=(x_tmp>0)?(x_tmp+1)/2:(-(-x_tmp-1)/2);
					 if(x_tmp>xr) id[i][size]=xr;
					 else if (x_tmp<xl) id[i][size]=xl;
					 else id[i][size]=x_tmp;
					 id_2[i][size2]=id[i][size]+Ind_Threshold;
				  }
     			  else
				  {
					  id[i][size]=x;   	 id_2[i][size2]=y;
				  }
		
				  if(ind1_temp>=ind2_temp)
				  {
		           d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
		           d_2[i][size2]=sqr(double(dctcoef_2b[i]-id_2[i][size2]*qtbl_1d[i]));
				  }
			      else
				  {
                   d[i][size]=sqr(double(dctcoef_1b[i]+id[i][size]*qtbl_1d[i]));
		           d_2[i][size2]=sqr(double(dctcoef_2b[i]+id_2[i][size2]*qtbl_1d[i]));
				  }
				  tmp_cost=d[i][size]+d_2[i][size2];
			  }//3

			  if (-s_min[size]<=ind1)      x=-s_min[size];
			  else if(-s_max[size]>=ind1)  x=-s_max[size];
			  else						   x=ind1;
					
   	          if (s_min[size2]>=ind2)      y=s_min[size2];
		      else if(s_max[size2]<=ind2)  y=s_max[size2];
		      else     					   y=ind2;

			  if((y-x)*qtbl_1d[i]<(Q[i]+rdt))
			  {
					  xl=-s_max[size];         xr=-s_min[size];
					  if((xl+Ind_Threshold)<s_min[size2]) 	xl=s_min[size2]-Ind_Threshold;
					  if((xr+Ind_Threshold)>s_max[size2])   xr=s_max[size2]-Ind_Threshold;

					  x_tmp=ind1+ind2-Ind_Threshold;        x_tmp=(x_tmp>0)?(x_tmp+1)/2:(-(-x_tmp-1)/2);
					  if(x_tmp>xr) x=xr;
					  else if (x_tmp<xl) x=xl;
					  else x=x_tmp;

					  y=x+Ind_Threshold;
			  }

			  if(ind1_temp>=ind2_temp)
			  {
				    if(sqr(double(dctcoef_1b[i]-x*qtbl_1d[i]))+sqr(double(dctcoef_2b[i]-y*qtbl_1d[i])<tmp_cost))
					{
					  id[i][size]=x;   		  id_2[i][size2]=y;
				      d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
		              d_2[i][size2]=sqr(double(dctcoef_2b[i]-id_2[i][size2]*qtbl_1d[i]));
					}
			  }
			  else
			  {
				   if(sqr(double(dctcoef_1b[i]+x*qtbl_1d[i]))+sqr(double(dctcoef_2b[i]+y*qtbl_1d[i])<tmp_cost))
					{
					  id[i][size]=x;          id_2[i][size2]=y;
				      d[i][size]=sqr(double(dctcoef_1b[i]+id[i][size]*qtbl_1d[i]));
		              d_2[i][size2]=sqr(double(dctcoef_2b[i]+id_2[i][size2]*qtbl_1d[i]));
					}
			  }
		   }//2
		 	    
		   cost=part_cost_1[size]+d[i][size];       cost_2=part_cost_2[size]+d_2[i][size2];
		   dist_inc=dist[i][j]+d[i][size];           dist_inc_2=dist_2[i][j]+d_2[i][size2];

		   if((cost+cost_2)<totalwmcost)
		   {
			 totalwmcost=cost+cost_2;
			 if(ind1_temp>=ind2_temp)
			 {
			   record_inf(state_path_a[2],i,run_1[size],size,   id[i][size],   dist_inc,   cost);
			   record_inf(state_path_b[2],i,run_2[size2],size2, id_2[i][size2], dist_inc_2, cost_2);
			 }
			 else
			 { 
			   record_inf(state_path_a[2],i,run_1[size],size,   -id[i][size],   dist_inc,   cost);
			   record_inf(state_path_b[2],i,run_2[size2],size2, -id_2[i][size2], dist_inc_2, cost_2);
			 }
		   }
		}//1
	}//end size2

    //size=size2
    if((s_max[size]+s_max[size])*qtbl_1d[i]>=(Q[i]+rdt))//1
	{			
			 tmp_cost=maxnumber;
			 if((s_max[size]-s_min[size])*qtbl_1d[i]>=(Q[i]+rdt))//2
			 {
			    if(ind2>-ind1)//3
				{
				  if (s_min[size]>=ind1)       x=s_min[size];
				  else if(s_max[size]<=ind1)   x=s_max[size];
			      else     			   x=ind1;
					
   	              if (s_min[size]>=ind2)       y=s_min[size];
		          else if(s_max[size]<=ind2)   y=s_max[size];
		          else     		       y=ind2;
					
				  if((y-x)*qtbl_1d[i]<(Q[i]+rdt))
				  {
					  xl=s_min[size];                  xr=s_max[size]-Ind_Threshold;
					  x_tmp=ind1+ind2-Ind_Threshold;   x_tmp=(x_tmp>0)?(x_tmp+1)/2:(-(-x_tmp-1)/2);

					  if(x_tmp>xr)       id[i][size]=xr;
					  else if (x_tmp<xl) id[i][size]=xl;
			    	       else          id[i][size]=x_tmp;
					  id_2[i][size]=id[i][size]+Ind_Threshold;
				  }
				}
				else//3
				{
				   if (-s_min[size]<=ind1)      x=-s_min[size];
				   else if(-s_max[size]>=ind1)  x=-s_max[size];
			            else                    x=ind1;
				   if (-s_min[size]<=ind2)      y=-s_min[size];
		           else if(-s_max[size]>=ind2)  y=-s_max[size];
		                else                    y=ind2;
					
				    if((y-x)*qtbl_1d[i]<(Q[i]+rdt))
					{
					  xl=-s_max[size];                 xr=-s_min[size]-Ind_Threshold;
					  x_tmp=ind1+ind2-Ind_Threshold;   x_tmp=(x_tmp>0)?(x_tmp+1)/2:(-(-x_tmp-1)/2);

					  if(x_tmp>xr)       id[i][size]=xr;
					  else if (x_tmp<xl) id[i][size]=xl;
					       else          id[i][size]=x_tmp;
					  id_2[i][size]=id[i][size]+Ind_Threshold;
					}
				}//3
                  
				if(ind1_temp>=ind2_temp)
				{
				  d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
		          d_2[i][size]=sqr(double(dctcoef_2b[i]-id_2[i][size]*qtbl_1d[i]));
				}
				else
				{ 
				  d[i][size]=sqr(double(dctcoef_1b[i]+id[i][size]*qtbl_1d[i]));
		          d_2[i][size]=sqr(double(dctcoef_2b[i]+id_2[i][size]*qtbl_1d[i]));
				}
			   tmp_cost=d[i][size]+d_2[i][size];
			 }//2

     		 if (-s_min[size]<=ind1)      x=-s_min[size];
			 else if(-s_max[size]>=ind1)  x=-s_max[size];
			 else                    x=ind1;
					
   	         if (s_min[size]>=ind2)       y=s_min[size];
		     else if(s_max[size]<=ind2)   y=s_max[size];
		     else                    y=ind2;
					 
			 if((y-x)*qtbl_1d[i]<(Q[i]+rdt)) 
			 {
				  xl=-s_max[size]; 		  xr=-s_min[size];
				  if((xl+Ind_Threshold)<s_min[size]) xl=s_min[size2]-Ind_Threshold;
				  if((xr+Ind_Threshold)>s_max[size]) xr=s_max[size]-Ind_Threshold;

				  x_tmp=ind1+ind2-Ind_Threshold;
				  x_tmp=(x_tmp>0)?(x_tmp+1)/2:(-(-x_tmp-1)/2);
				  if(x_tmp>xr)       x=xr;
				  else if (x_tmp<xl) x=xl;
				  else               x=x_tmp;

				  y=x+Ind_Threshold;
			 }

			 if(ind1_temp>=ind2_temp)
			 {
				  if(sqr(double(dctcoef_1b[i]-x*qtbl_1d[i]))+sqr(double(dctcoef_2b[i]-y*qtbl_1d[i]))<tmp_cost)
				  {
					 id[i][size]=x;    id_2[i][size]=y;
				     d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
		             d_2[i][size]=sqr(double(dctcoef_2b[i]-id_2[i][size]*qtbl_1d[i]));
				  }
			 }
			 else
			 {
				  if(sqr(double(dctcoef_1b[i]+x*qtbl_1d[i]))+sqr(double(dctcoef_2b[i]+y*qtbl_1d[i]))<tmp_cost)
				  {
					 id[i][size]=x;   		 id_2[i][size]=y;
				     d[i][size]=sqr(double(dctcoef_1b[i]+id[i][size]*qtbl_1d[i]));
		             d_2[i][size]=sqr(double(dctcoef_2b[i]+id_2[i][size]*qtbl_1d[i]));
				  }
			 }
				
		     cost=part_cost_1[size]+d[i][size];   	   cost_2=part_cost_2[size]+d_2[i][size];
		     dist_inc=dist[i][j]+d[i][size];    		   dist_inc_2=dist_2[i][j]+d_2[i][size];

		     if((cost+cost_2)<totalwmcost)
		     {
			   totalwmcost=cost+cost_2;
			   if(ind1_temp>=ind2_temp)
			   {
			     record_inf(state_path_a[2],i,run_1[size],size, id[i][size],   dist_inc,   cost);
			     record_inf(state_path_b[2],i,run_2[size],size, id_2[i][size], dist_inc_2, cost_2);
    		   }
			   else
			   {
			     record_inf(state_path_a[2],i,run_1[size],size, -id[i][size],   dist_inc,   cost);
			     record_inf(state_path_b[2],i,run_2[size],size, -id_2[i][size], dist_inc_2, cost_2);
			   }
			 }
		 }//1
	
         for(size2=size+1;size2<11;size2++)
		 {
   		   if((s_max[size2]+s_max[size])*qtbl_1d[i]>=(Q[i]+rdt))//1
		   {
			if((s_min[size2]-s_max[size])*qtbl_1d[i]>=(Q[i]+rdt))//2
			{
			   if (s_min[size2]>=ind2)      id_2[i][size2]=s_min[size2];
			   else if(s_max[size2]<=ind2)  id_2[i][size2]=s_max[size2];
			   else     				    id_2[i][size]=ind2;
					
   	           if(ind1>=0)
			   {
		        if (s_min[size]>=ind1)      id[i][size]=s_min[size];
		        else if(s_max[size]<=ind1)  id[i][size]=s_max[size];
		        else                        id[i][size]=ind1;
			   }
		       else
			   {
		        if (-s_min[size]<=ind1)     id[i][size]=-s_min[size];
		        else if(-s_max[size]>=ind1) id[i][size]=-s_max[size];
		        else                        id[i][size]=ind1;
			   }
             
			   if(ind1_temp>=ind2_temp)
			   {
		        d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
		        d_2[i][size2]=sqr(double(dctcoef_2b[i]-id_2[i][size2]*qtbl_1d[i]));
			   }
			   else
			   {
		        d[i][size]=sqr(double(dctcoef_1b[i]+id[i][size]*qtbl_1d[i]));
		        d_2[i][size2]=sqr(double(dctcoef_2b[i]+id_2[i][size2]*qtbl_1d[i]));
			   }
			}//2
			else 
			{ 
			  tmp_cost=maxnumber;
			  if((s_max[size2]-s_min[size])*qtbl_1d[i]>=(Q[i]+rdt))//3
			  {
			      if (s_min[size]>=ind1)       x=s_min[size];
				  else if(s_max[size]<=ind1)   x=s_max[size];
			      else          			   x=ind1;
					
   	              if (s_min[size2]>=ind2)      y=s_min[size2];
		          else if(s_max[size2]<=ind2)  y=s_max[size2];
		          else          		       y=ind2;

				  if((y-x)*qtbl_1d[i]<(Q[i]+rdt))
				  {
					  xl=s_min[size];     xr=s_max[size];
					  if((xl+Ind_Threshold)<s_min[size2])  xl=s_min[size2]-Ind_Threshold;
					  if((xr+Ind_Threshold)>s_max[size2])  xr=s_max[size2]-Ind_Threshold;

					  x_tmp=ind1+ind2-Ind_Threshold;   x_tmp=(x_tmp>0)?(x_tmp+1)/2:(-(-x_tmp-1)/2);
					  if(x_tmp>xr)       id[i][size]=xr;
					  else if (x_tmp<xl) id[i][size]=xl;
					  else               id[i][size]=x_tmp;

					  id_2[i][size2]=id[i][size]+Ind_Threshold;
				  }
				  else
				  {
					  id[i][size]=x;    id_2[i][size2]=y;
				  }
				  
				  if(ind1_temp>=ind2_temp)
				  {
  				    d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
		            d_2[i][size2]=sqr(double(dctcoef_2b[i]-id_2[i][size2]*qtbl_1d[i]));
				  }
				  else
				  {
  				    d[i][size]=sqr(double(dctcoef_1b[i]+id[i][size]*qtbl_1d[i]));
		            d_2[i][size2]=sqr(double(dctcoef_2b[i]+id_2[i][size2]*qtbl_1d[i]));
				  }
				  tmp_cost=d[i][size]+d_2[i][size2];
			  }//3

			  if (-s_min[size]<=ind1)    	   x=-s_min[size];
			  else if(-s_max[size]>=ind1)      x=-s_max[size];
			  else          				   x=ind1;
					
   	          if (s_min[size2]>=ind2)          y=s_min[size2];
		      else if(s_max[size2]<=ind2)      y=s_max[size2];
		      else          			       y=ind2;

			  if((y-x)*qtbl_1d[i]<(Q[i]+rdt))
			  {
				  xl=-s_max[size];						xr=-s_min[size];
				  if((xl+Ind_Threshold)<s_min[size2]) 	xl=s_min[size2]-Ind_Threshold;
				  if((xr+Ind_Threshold)>s_max[size2])  	xr=s_max[size2]-Ind_Threshold;
				  x_tmp=ind1+ind2-Ind_Threshold;   		x_tmp=(x_tmp>0)?(x_tmp+1)/2:(-(-x_tmp-1)/2);

				  if(x_tmp>xr)       x=xr;  
				  else if (x_tmp<xl) x=xl;
				  else               x=x_tmp;
				  y=x+Ind_Threshold;
			  }

			  if(ind1_temp>=ind1_temp)
			  {
				   if(sqr(double(dctcoef_1b[i]-x*qtbl_1d[i]))+sqr(double(dctcoef_2b[i]-y*qtbl_1d[i])<tmp_cost))
				   {
					id[i][size]=x;  				id_2[i][size2]=y;
			        d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
		            d_2[i][size2]=sqr(double(dctcoef_2b[i]-id_2[i][size2]*qtbl_1d[i]));
				   }
			   }
			   else
			   {
				   if(sqr(double(dctcoef_1b[i]+x*qtbl_1d[i]))+sqr(double(dctcoef_2b[i]+y*qtbl_1d[i])<tmp_cost))
				   {
					id[i][size]=x;  		id_2[i][size2]=y;
				    d[i][size]=sqr(double(dctcoef_1b[i]+id[i][size]*qtbl_1d[i]));
		            d_2[i][size2]=sqr(double(dctcoef_2b[i]+id_2[i][size2]*qtbl_1d[i]));
				   }
			   }
			  				
			}//2
		 		   
		    cost=part_cost_1[size]+d[i][size];  	   cost_2=part_cost_2[size]+d_2[i][size2];
		    dist_inc=dist[i][j]+d[i][size];         dist_inc_2=dist_2[i][j]+d_2[i][size2];

		    if((cost+cost_2)<totalwmcost)
		    {
			  totalwmcost=cost+cost_2;
              if(ind1_temp>=ind1_temp)
			  {
			     record_inf(state_path_a[2],i,run_1[size],size, id[i][size],   dist_inc,   cost);
			     record_inf(state_path_b[2],i,run_2[size2],size2, id_2[i][size2], dist_inc_2, cost_2);
			  }
			  else
			  {
			     record_inf(state_path_a[2],i,run_1[size],size, -id[i][size],   dist_inc,   cost);
			     record_inf(state_path_b[2],i,run_2[size2],size2, -id_2[i][size2], dist_inc_2, cost_2);
			  }
		   }
		}//1
	  }//end size2
	}//end size

	state_path_a_end_cost[2][i]=state_path_a[2][i].min_cost+eob_cost[i];  	  final_nzc_path_a[2]=i;
	state_path_b_end_cost[2][i]=state_path_b[2][i].min_cost+eob_cost_2[i];      final_nzc_path_b[2]=i; 
	node[0][3][0].block_a_graph_no=2;   	  node[0][3][0].block_b_graph_no=2;
	block_a_tree[2].cost_inwm_status=1;	  block_b_tree[2].cost_inwm_status=1;

    for (i=wm_pos[kk]+1; i<end_right; i++)
	{
	   curr_min=maxnumber;   	   curr_min_2=maxnumber;

	   k=((i-wm_pos[kk])>15)?15:(i-wm_pos[kk]-1);  // first 15 states do not have full incoming states
	   // for each incoming state j (j is from 0 to maximum incoming states)
	   for (j=0; j<=k; j++)
	        search_min_cost(state_path_a[2], state_path_b[2], i,j); // end of j loop for each one incoming state  
   	   // for each state, find the cost of going EOB after this nonzero state
	   if (i<63)
	   {
		 state_path_a_end_cost[2][i]=state_path_a[2][i].min_cost+eob_cost[i];
		 if (state_path_a_end_cost[2][i]<state_path_a_end_cost[2][final_nzc_path_a[2]])  final_nzc_path_a[2]=i;
	     state_path_b_end_cost[2][i]=state_path_b[2][i].min_cost+eob_cost_2[i];
		 if (state_path_b_end_cost[2][i]<state_path_b_end_cost[2][final_nzc_path_b[2]])  final_nzc_path_b[2]=i; 
	   } 

	   // consider (15,0) case for i>=16 (consider this AFTER ending-cost calculation!)
	   if ((i-wm_pos[kk])>15&&i<63)
	   {
		 update_cost(i,15,0,dist[i][15],  sqr(c_abs[i]),  0,state_path_a[2]);
		 update_cost_2(i,15,0,dist_2[i][15],sqr(c_abs_2[i]),0,state_path_b[2]); 
	   }

       if ((curr_min<0)||(curr_min_2<0))  printf("row_b=%d, col_b=%d, i=%d\n", row_b, col_b, i);
    } // end of i loop for the calculation of the minimum cost for one state
    block_a_tree[2].cost_status_2=1;    block_b_tree[2].cost_status_2=1;
 } //end of else

 for(kk=1;kk<wm_len;kk++)
 {
   if(kk==wm_len-1) end_right=64;
   else 
   {
	 if(wm_pos[kk+1]==wm_pos[kk]+1)  	end_right=wm_pos[kk]+1;
	 else                       		end_right=wm_pos[kk+1];
   }
		
   if(wm_bit[kk]==0)
   { 
	 kkk=0;
	 for(ttt=0;ttt<4;ttt++)
	 { 
	   for(jj=0;jj<num_comb[kk-1][ttt];jj++)
	   {
	     a1=node[kk-1][ttt][jj].block_a_graph_no;  b1=node[kk-1][ttt][jj].block_b_graph_no;
  		 int nkj=kkk+jj;
	     node[kk][0][nkj].block_a_graph_no = block_a_tree[a1].next_level_node_value[0];
	     node[kk][0][nkj].block_b_graph_no = block_b_tree[b1].next_level_node_value[0]; 

		 a2=node[kk][0][nkj].block_a_graph_no;     b2=node[kk][0][nkj].block_b_graph_no;
		 block_a_tree[a2].wm_nozero_no=block_a_tree[a1].wm_nozero_no;
		 block_b_tree[b2].wm_nozero_no=block_b_tree[b1].wm_nozero_no;

		 if(block_a_tree[a2].cost_inwm_status==0)
		 { 
		   memcpy(state_path_a[a2], state_path_a[a1],wm_pos[kk]*sizeof(statenode));
		   final_nzc_path_a[a2]=final_nzc_path_a[a1];
		   state_path_a_end_cost[a2][final_nzc_path_a[a2]]=state_path_a_end_cost[a1][final_nzc_path_a[a1]];
            // This part is used to compute the number of watermark points which have no cost in the graph
		   i=wm_pos[kk];    curr_min=maxnumber;     t1=0;    t2=0; // t1 is used when distance <=15, t2 otherwise
		   if(block_a_tree[a2].wm_nozero_no>=0)
		   { 
			 if((i-wm_pos[block_a_tree[a2].wm_nozero_no])>15 && i<63) 
			 {
			   for(j1=block_a_tree[a2].wm_nozero_no+1;j1<kk;j1++)
			   {	
				if((wm_pos[j1]-wm_pos[block_a_tree[a2].wm_nozero_no])<=15)
				{ 
				  wm_nocost_pos[t1]=wm_pos[j1];    t1++;    t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				      if(wm_pos[j1]-wm_nocost_pos[k1]==16) 	wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			   }//end of j1 loop
			
			  thr=0;
			  for(m=0;m<t2;m++)
			  {
				if((i-16 )==wm_nocost_pos[m])
				{
				  thr=1;
				  break;
				}
			  }
			  if(thr==0)  update_cost(i,15,0,dist[i][15], sqr(c_abs[i]), 0,state_path_a[a2]);
		   }//end of if >15 <63
		 }//end of if(block_a_tree[a2].wm_nozero_no>=0)
		 else
		 {
		     if(i>15 && i<63)  
			 {
			  for(j1=0;j1<kk;j1++)
			  {	
				if(wm_pos[j1]<=15)
				{ wm_nocost_pos[t1]=wm_pos[j1];   t1++;    t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				     if(wm_pos[j1]-wm_nocost_pos[k1]==16) 	wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				}
			  }
			  thr=0;
			  for(m=0;m<t2;m++)
			  {
				if((i-16 )==wm_nocost_pos[m])
				{
				  thr=1;
				  break;
				}
			  }
			  if(thr==0)  update_cost(i,15,0,dist[i][15], sqr(c_abs[i]), 0,state_path_a[a2]);
		 }//end of if(i>15 && i<63)
	   }// //end of else(block_a_tree[a2].wm_nozero_no>=0)
	  block_a_tree[a2].cost_inwm_status=1;
	} //end of  if(block_a_tree[a2].cost_inwm_status==0)

	 if(block_b_tree[b2].cost_inwm_status==0)
	 {
		  memcpy(state_path_b[b2], state_path_b[b1],wm_pos[kk]*sizeof(statenode));
		  final_nzc_path_b[b2]=final_nzc_path_b[b1];
		  state_path_b_end_cost[b2][final_nzc_path_b[b2]]=state_path_b_end_cost[b1][final_nzc_path_b[b1]];
          // This part is used to compute the number of watermark points which have no cost in the graph
		  i=wm_pos[kk];   curr_min_2=maxnumber;   t1=0; t2=0;  // t1 is used when distance <=15, t2 otherwise
		  if(block_b_tree[b2].wm_nozero_no>=0)
		   { 
			 if((i-wm_pos[block_b_tree[b2].wm_nozero_no])>15 && i<63) 
			 {
			  for(j1=block_b_tree[b2].wm_nozero_no+1;j1<kk;j1++)
			  {	
				if((wm_pos[j1]-wm_pos[block_b_tree[b2].wm_nozero_no])<=15)
				{ wm_nocost_pos[t1]=wm_pos[j1];   t1++;   t2=t1;
				}
				else 
				{ 
				  for(k1=0; k1<t2; k1++)
				    if(wm_pos[j1]-wm_nocost_pos[k1]==16) 	wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			  }
			  thr=0;
			  for(m=0;m<t2;m++)
			  {
				if((i-16)==wm_nocost_pos[m])
				{
				  thr=1;
				  break;
				}
			  }
			  if(thr==0)  update_cost_2(i,15,0,dist_2[i][15], sqr(c_abs_2[i]),0, state_path_b[b2]);
		   	 }
		  }//end of if(block_b_tree[b2].wm_nozero_no>=0)
		  else
		  {
		     if(i>15 && i<63)  //????
			 {			  
			  for(j1=0;j1<kk;j1++)
			  {	
				if(wm_pos[j1]<=15)
				{ wm_nocost_pos[t1]=wm_pos[j1];   t1++;   	  t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				     if(wm_pos[j1]-wm_nocost_pos[k1]==16) 	wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			  }
			  thr=0;
			  for(m=0;m<t2;m++)
			  {
				if((i-16 )==wm_nocost_pos[m])
				{
				  thr=1;
				  break;
				}
			  }
			  if(thr==0)  update_cost_2(i,15,0,dist_2[i][15], sqr(c_abs_2[i]), 0,state_path_b[b2]);
			 }
		   }//end of else(block_b_tree[b2].wm_nozero_no>=0)
		  block_b_tree[b2].cost_inwm_status=1;  
		 } // end of if block_b_tree[b2].cost_inwm_status==1
        
	  //inwm_status used to detect if the watermarking state is computed
	  //cost_status used to detect if the fllowing state is computed
		if(block_a_tree[a2].cost_status_2==0)
		{
	      for(i=wm_pos[kk]+1;i<end_right;i++)
		  { 
		    t1=0; t2=0;  curr_min=maxnumber;
		    if(block_a_tree[a2].wm_nozero_no>=0)
			{
			  k=(i-wm_pos[block_a_tree[a2].wm_nozero_no]>15)?15:(i-wm_pos[block_a_tree[a2].wm_nozero_no]-1);
			  // This part is used to count the number of watemrark poistions which has no cost and will afffect this state
			  for(j1=block_a_tree[a2].wm_nozero_no+1;j1<=kk;j1++)
			  {	
				if((wm_pos[j1]-wm_pos[block_a_tree[a2].wm_nozero_no])<=15)
				{ 
				  wm_nocost_pos[t1]=wm_pos[j1];   t1++;   t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				  if(wm_pos[j1]-wm_nocost_pos[k1]==16)  wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			  }
			}//end of if(block_a_tree[a2].wm_nozero_no>=0)
            else	  
			{
			  k=(i>15)?15:(i-1);  // first 15 states do not have full incoming states
                // for each incoming state j (j is from 0 to maximum incoming states)
			  for(j1=0;j1<=kk;j1++)
			  {	
				if(wm_pos[j1]<=15)
				{ 
					wm_nocost_pos[t1]=wm_pos[j1];   t1++;   t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				        if(wm_pos[j1]-wm_nocost_pos[k1]==16) wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			  }
			}//end of else (block_a_tree[a2].wm_nozero_no>=0)
	           
	        for(j=0; j<=k; j++)
			{
			  thr=0;
			  for(m=0;m<t2;m++)
			  {
				if(j==(i-wm_nocost_pos[m]-1))
				{
				  thr=1;
				  break;
				}
			  }
			  if(thr==0)
			  {
		        switch (indsi[i])
				{
	             case 0:
		          for(size=1; size<3; size++)  update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
                 break;
                 case 1:
		          for(size=1; size<4; size++)  update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
                 break; 
	             case 10:
                  for (size=10; size>8; size--) update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
                 break;
		         default: //2~9 
                 for (size=indsi[i]-1; size<indsi[i]+2; size++)
		          update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
				} // end of switch
               }//end of if thr
			 }//end of j loop
	
	         // for each state, find the cost of going EOB after this nonzero state
	        if (i<63)
			{
				 state_path_a_end_cost[a2][i]=state_path_a[a2][i].min_cost+eob_cost[i];
				 if (state_path_a_end_cost[a2][i]<state_path_a_end_cost[a2][final_nzc_path_a[a2]])
				 final_nzc_path_a[a2]=i;
			} 

	        // consider (15,0) case for i>=16 (consider this AFTER ending-cost calculation!)
	        if(block_a_tree[a2].wm_nozero_no>=0)  v1=i-wm_pos[block_a_tree[a2].wm_nozero_no];
			else v1=i;
			if (v1>15&&i<63)
			{
			  thr=0;
			  for(m=0;m<t2;m++)
			  {
				if((i-16 )==wm_nocost_pos[m])
				{
				  thr=1;
				  break;
				}
			  }
			  // The above part is to detect if the state-16 has no cost				
			  if((thr==0)&&(final_nzc_path_a[a2]!=i)) 
				  update_cost(i,15,0,dist[i][15],sqr(c_abs[i]),0,state_path_a[a2]);
			}//end of if if (v1>15&&i<63)

			if (curr_min<0)
 	            printf("row_b=%d, col_b=%d, i=%d\n", row_b, col_b, i);
		  } // end of i loop for the calculation of the minimum cost for one state   
	      block_a_tree[a2].cost_status_2=1;
		 }//end if block_a_tree[a2].cost_status_2==0
				  
		 if(block_b_tree[b2].cost_status_2==0)
		  {
	        for(i=wm_pos[kk]+1;i<end_right;i++)
			{ 
			  t1=0; t2=0;      curr_min_2=maxnumber;
			  if(block_b_tree[b2].wm_nozero_no>=0)
			  {
				k=(i-wm_pos[block_b_tree[b2].wm_nozero_no]>15)?15:(i-wm_pos[block_b_tree[b2].wm_nozero_no]-1);
			    // This part is used to count the number of watermarking state having no cost
				for(j1=block_b_tree[b2].wm_nozero_no+1;j1<=kk;j1++)
				{	
				 if((wm_pos[j1]-wm_pos[block_b_tree[b2].wm_nozero_no])<=15)
				 { 
					 wm_nocost_pos[t1]=wm_pos[j1];  t1++; 	  t2=t1;
				 }
				 else 
				 { 
				  for(k1=0;k1<t2;k1++)
				  if(wm_pos[j1]-wm_nocost_pos[k1]==16)
						wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
				} //end og j1 loop
			  }
              else	  
			  {
			    k=(i>15)?15:(i-1);  // first 15 states do not have full incoming states
                // for each incoming state j (j is from 0 to maximum incoming states)
			    for(j1=0;j1<=kk;j1++)
				{	
				  if(wm_pos[j1]<=15)
				  {
					  wm_nocost_pos[t1]=wm_pos[j1];    t1++;       t2=t1;
				  }
			      else 
				  { 
				    for(k1=0;k1<t2;k1++)
				      if(wm_pos[j1]-wm_nocost_pos[k1]==16) 	wm_nocost_pos[t2]=wm_pos[j1];
				    t2++;
				  }
				}//end of k1 loop
			}// end of if(block_b_tree[b2].wm_nozero_no>=0)
	           
	        for(j=0; j<=k; j++)
			{
			  thr=0;
			  for(m=0;m<t2;m++)
			  {
				if(j==(i-wm_nocost_pos[m]-1))
				{
				  thr=1;
				  break;
				}
			  }
			  if(thr==0)
			   {
		        switch (indsi_2[i])
				{
	             case 0:
		          for(size=1; size<3; size++) update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
                 break;
                 case 1:
		          for(size=1; size<4; size++) update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
                 break;
	             case 10:
                  for (size=10; size>8; size--) update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
                 break;
		         default: //2~9 
                 for (size=indsi_2[i]-1; size<indsi_2[i]+2; size++)
		           update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
				} // end of switch
			   }//end if thr
			 }//end of j loop
	
	          // for each state, find the cost of going EOB after this nonzero state
	         if (i<63)
			 {
				state_path_b_end_cost[b2][i]=state_path_b[b2][i].min_cost+eob_cost_2[i];
				if (state_path_b_end_cost[b2][i]<state_path_b_end_cost[b2][final_nzc_path_b[b2]])
				final_nzc_path_b[b2]=i;
				} 
             // consider (15,0) case for i>=16 (consider this AFTER ending-cost calculation!)
	         if(block_b_tree[b2].wm_nozero_no>=0)  v1=i-wm_pos[block_b_tree[b2].wm_nozero_no];
		     else v1=i;
			 if (v1>15&&i<63)
			 {
			  thr=0;
			  for(m=0;m<t2;m++)
			  {
				if((i-16 )==wm_nocost_pos[m])
				{
				  thr=1;
				  break;
				}
			  }
			  // The above paprt is to detect if the state-16 has no codt	
			  if((thr==0)&&(final_nzc_path_b[b2]!=i))  update_cost_2(i,15,0,dist_2[i][15],sqr(c_abs_2[i]),0,state_path_b[b2]);
			 }

			 if (curr_min_2<0)  printf("row_b=%d, col_b=%d, i=%d\n", row_b, col_b, i);
			} // end of i loop for the calculation of the minimum cost for one state   
			block_b_tree[b2].cost_status_2=1;
		}//end of  if block_b_tree[b2].cost_status_2

	}//end of jj loop
	kkk +=num_comb[kk-1][ttt];
   }//end of ttt
 
  //No need to update node[kk][1] & node[kk][2], The following is used to update node[kk][3]
   tempcost=maxnumber;    path_a_no=0;    path_b_no=0;
   for(ttt=0;ttt<4;ttt++)
	 { 
	   for(jj=0;jj<num_comb[kk-1][ttt];jj++)
		{
	      a1=node[kk-1][ttt][jj].block_a_graph_no;   	      b1=node[kk-1][ttt][jj].block_b_graph_no;
		  a2=block_a_tree[a1].next_level_node_value[2];  	  b2=block_b_tree[b1].next_level_node_value[2];
		  block_a_tree[a2].wm_nozero_no=block_a_tree[a1].wm_nozero_no;
		  block_b_tree[b2].wm_nozero_no=block_b_tree[b1].wm_nozero_no;

		  memcpy(state_path_a[a2], state_path_a[a1],wm_pos[kk]*sizeof(statenode));
		  final_nzc_path_a[a2]=final_nzc_path_a[a1];
		  state_path_a_end_cost[a2][final_nzc_path_a[a2]]=state_path_a_end_cost[a1][final_nzc_path_a[a1]];

		  memcpy(state_path_b[b2], state_path_b[b1],wm_pos[kk]*sizeof(statenode));
		  final_nzc_path_b[b2]=final_nzc_path_b[b1];
		  state_path_b_end_cost[b2][final_nzc_path_b[b2]]=state_path_b_end_cost[b1][final_nzc_path_b[b1]];

		  i=wm_pos[kk];
          for(size=1; size<11; size++)
		  {
		   tmp_min=maxnumber; 	   tmp_min_2=maxnumber;      t1=0; t2=0;
		    if(block_b_tree[b2].wm_nozero_no>=0)
			{  // The following counts the number of watermarking sates having no cost related to this state
		 	   k=(i-wm_pos[block_b_tree[b2].wm_nozero_no]>15)?15:(i-wm_pos[block_b_tree[b2].wm_nozero_no]-1);
			   for(j1=block_b_tree[b2].wm_nozero_no+1;j1<kk;j1++)
			   {	
				 if((wm_pos[j1]-wm_pos[block_b_tree[b2].wm_nozero_no])<=15)
				 {
					 wm_nocost_pos[t1]=wm_pos[j1];   t1++;  	  t2=t1;
				 }
				 else 
				 { 
				  for(k1=0;k1<t2;k1++)
				  if(wm_pos[j1]-wm_nocost_pos[k1]==16)  wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			   }
			 }
             else	  
			 {
			  k=(i>15)?15:(i-1);  // first 15 states do not have full incoming states
                // for each incoming state j (j is from 0 to maximum incoming states)
			    for(j1=0;j1<kk;j1++)
				{	
				  if(wm_pos[j1]<=15)
				  { 
					wm_nocost_pos[t1]=wm_pos[j1];      t1++;    t2=t1;
				  }
				  else 
				  { 
				    for(k1=0;k1<t2;k1++)
				       if(wm_pos[j1]-wm_nocost_pos[k1]==16) wm_nocost_pos[t2]=wm_pos[j1];
				    t2++;
				 }
				}
			 }
	          
	        for(j=0; j<=k; j++)
			{
			  thr=0; 
			  for(m=0;m<t2;m++)
			  {
				if(j==(i-wm_nocost_pos[m]-1))
				{
				  thr=1;
				  break;
				}
			  }
			 if(thr==0) 
			 {
		      cost_2=state_path_b[b2][i-j-1].min_cost+dist_2[i][j]+ent_ac[(j<<4)+size];
		      if (cost_2<tmp_min_2)
			  {
			   tmp_min_2=cost_2;     run_2[size]=j;
			  }
			 }
			}//end of j loop

		  t1=0; t2=0;
          if(block_a_tree[a2].wm_nozero_no>=0)
		  {  // count the number of watermarking states having no cost
		 	 k=(i-wm_pos[block_a_tree[a2].wm_nozero_no]>15)?15:(i-wm_pos[block_a_tree[a2].wm_nozero_no]-1);
			 for(j1=block_a_tree[a2].wm_nozero_no+1;j1<kk;j1++)
			 {	
				if((wm_pos[j1]-wm_pos[block_a_tree[a2].wm_nozero_no])<=15)
				{ 
					wm_nocost_pos[t1]=wm_pos[j1]; 	  t1++;  	  t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				    if(wm_pos[j1]-wm_nocost_pos[k1]==16)  wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			  }
		  }
          else	  
		  {
			  k=(i>15)?15:(i-1);  // first 15 states do not have full incoming states
                // for each incoming state j (j is from 0 to maximum incoming states)
			  for(j1=0;j1<kk;j1++)
			  {	
				if(wm_pos[j1]<=15)
				{ 
					wm_nocost_pos[t1]=wm_pos[j1];    t1++;    t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				     if(wm_pos[j1]-wm_nocost_pos[k1]==16)  wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			  } 
			}
	           
	         for(j=0; j<=k; j++)
			 {
			   thr=0;
			   for(m=0;m<t2;m++)
			   {
				  if(j==(i-wm_nocost_pos[m]-1))
				  {
				   thr=1;
				   break;
				  }
			   }
					  
               if(thr==0)
			   {
		          cost=state_path_a[a2][i-j-1].min_cost+dist[i][j]+ent_ac[(j<<4)+size];
		          if (cost<tmp_min)
				  {
			       tmp_min=cost;   run_1[size]=j;
				  }
			   }
			 }//end of j

		   part_cost_1[size]=tmp_min;   part_cost_2[size]=tmp_min_2;
		  } //end of size loop

	  i=wm_pos[kk];  ind1=quantize1c(dctcoef_1b[i],i);    ind2=quantize1c(dctcoef_2b[i],i);
	  int cross_point=(ind1+ind2)/2;     totalwmcost=maxnumber;
      for (size=1; size<11; size++)
	  {
	     if(cross_point>=0)     
		 {
		    if (s_min[size]>=cross_point)               id[i][size]=s_min[size];
	        else if (s_max[size]<=cross_point)          id[i][size]=s_max[size];
	        else                                        id[i][size]=cross_point;
			id_2[i][size]=id[i][size];
	        d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
			d_2[i][size]=sqr(double(dctcoef_2b[i]-id_2[i][size]*qtbl_1d[i]));
		 }
         else 
		 {
		   if (-s_min[size]<=cross_point)    		    id[i][size]=-s_min[size];
		   else if(-s_max[size]>=cross_point) 		    id[i][size]=-s_max[size];
		   else                              			id[i][size]=cross_point;
     	   id_2[i][size]=id[i][size];
	       d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
		   d_2[i][size]=sqr(double(dctcoef_2b[i]-id_2[i][size]*qtbl_1d[i]));
		 }

          cost=part_cost_1[size]+d[i][size];  		  cost_2=part_cost_2[size]+d_2[i][size];
		  dist_inc=dist[i][run_1[size]]+d[i][size];   dist_inc_2=dist_2[i][run_2[size]]+d_2[i][size];

		  if((cost+cost_2)<totalwmcost)
		  {
			 totalwmcost=cost+cost_2;
			 record_inf(state_path_a[a2],i,run_1[size],size,   id[i][size],    dist_inc,   cost);
			 record_inf(state_path_b[b2],i,run_2[size],size, id_2[i][size], dist_inc_2, cost_2);
		   }
		 }

 	    if(i<63)
		{
	     state_path_a_end_cost[a2][i]=state_path_a[a2][i].min_cost+eob_cost[i];    final_nzc_path_a[a2]=i;
	     state_path_b_end_cost[b2][i]=state_path_b[b2][i].min_cost+eob_cost_2[i];  final_nzc_path_b[b2]=i; 
		}
		 block_b_tree[b2].cost_inwm_status=1; 		 block_a_tree[a2].cost_inwm_status=1;
        		 
		 if(state_path_b[b2][i].min_cost+state_path_a[a2][i].min_cost<tempcost)
		 {
			tempcost=state_path_b[b2][i].min_cost+state_path_a[a2][i].min_cost;
			path_a_no=a2;  			path_b_no=b2;
		 }
		}//end of jj
    }//end of ttt
			 
	node[kk][3][0].block_a_graph_no = path_a_no; 	node[kk][3][0].block_b_graph_no = path_b_no; 
	a2=path_a_no;                                   b2=path_b_no;
	block_b_tree[b2].wm_nozero_no=kk;            	block_a_tree[a2].wm_nozero_no=kk;
   // The above for the computing the cost for watermarking state, the following is used for the following states	
    if(block_b_tree[b2].cost_status_2==0)
	 {  
	    for(i=wm_pos[kk]+1;i<end_right;i++)
		{ 
          curr_min_2=maxnumber;
	      k=(i-wm_pos[block_b_tree[b2].wm_nozero_no]>15)?15:(i-wm_pos[block_b_tree[b2].wm_nozero_no]-1);
	      for(j=0; j<=k; j++)
		  {
		    switch (indsi_2[i])
			{
             case 0:
	          for(size=1; size<3; size++)  update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
             break;
             case 1:
	          for(size=1; size<4; size++)  update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
             break;
             case 10:
              for (size=10; size>8; size--) update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
             break;
	         default: //2~9 
             for (size=indsi_2[i]-1; size<indsi_2[i]+2; size++)
	           update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
			} // end of switch
           }//end of j loop
	
         // for each state, find the cost of going EOB after this nonzero state
         if (i<63)
		 {
			 state_path_b_end_cost[b2][i]=state_path_b[b2][i].min_cost+eob_cost_2[i];
			 if (state_path_b_end_cost[b2][i]<state_path_b_end_cost[b2][final_nzc_path_b[b2]])
			 final_nzc_path_b[b2]=i;
		 } 
          // consider (15,0) case for i>=16 (consider this AFTER ending-cost calculation!)
          if((i-wm_pos[block_b_tree[b2].wm_nozero_no]>15)&&(i<63)&&(final_nzc_path_b[b2]!=i))
		  	  update_cost_2(i,15,0,dist_2[i][15],  sqr(c_abs_2[i]), 0, state_path_b[b2]);
		 
		  if (curr_min_2<0)  printf("row_b=%d, col_b=%d, i=%d\n", row_b, col_b, i);
		} // end of i loop for the calculation of the minimum cost for one state   
		
	    block_b_tree[b2].cost_status_2=1;
	}//end if block_a_tree[a2].cost_status_2==0
		  
    if(block_a_tree[a2].cost_status_2==0)
	{
	  for(i=wm_pos[kk]+1;i<end_right;i++)
	  { 
		  curr_min=maxnumber;
		  k=(i-wm_pos[block_a_tree[a2].wm_nozero_no]>15)?15:(i-wm_pos[block_a_tree[a2].wm_nozero_no]-1);
	      for(j=0; j<=k; j++)
		  {
		    switch (indsi[i])
			{
	          case 0:
		      for(size=1; size<3; size++) update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
              break;
              case 1:
		      for(size=1; size<4; size++) update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
              break;
	          case 10:
              for (size=10; size>8; size--) update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
              break;
		      default: //2~9 
              for (size=indsi[i]-1; size<indsi[i]+2; size++)
		         update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
			} // end of switch
		   }//end of j loop
	
	     // for each state, find the cost of going EOB after this nonzero state
	     if (i<63)
		 {
			state_path_a_end_cost[a2][i]=state_path_a[a2][i].min_cost+eob_cost[i];
			if (state_path_a_end_cost[a2][i]<state_path_a_end_cost[a2][final_nzc_path_a[a2]])
			final_nzc_path_a[a2]=i;
		 } 
         // consider (15,0) case for i>=16 (consider this AFTER ending-cost calculation!)
         if ((i-wm_pos[block_a_tree[a2].wm_nozero_no]>15)&&(i<63)&&(final_nzc_path_a[a2]!=i))
		 	        update_cost(i,15,0,dist[i][15],sqr(c_abs[i]),0,state_path_a[a2]);
		
		 if (curr_min<0)   printf("row_b=%d, col_b=%d, i=%d\n", row_b, col_b, i);
		} // end of i loop for the calculation of the minimum cost for one state   
		block_a_tree[a2].cost_status_2=1;
	}//end of  if block_b_tree[b2].cost_status_2
  }	 //end of if(wm[kk]==0)      
 else // (wm[kk]==1) update node 1,2,3
 { 
   //The following is used to update node[kk][1]
   tempcost=maxnumber;     path_a_no=0;      path_b_no=0;
   for(ttt=2;ttt<4;ttt++)
	 { 
	   for(jj=0;jj<num_comb[kk-1][ttt];jj++)
		{
	      a1=node[kk-1][ttt][jj].block_a_graph_no;      b1=node[kk-1][ttt][jj].block_b_graph_no;
		  a2=block_a_tree[a1].next_level_node_value[0]; b2=block_b_tree[b1].next_level_node_value[1];
		  block_b_tree[b2].wm_nozero_no=block_b_tree[b1].wm_nozero_no;

		  memcpy(state_path_b[b2], state_path_b[b1],wm_pos[kk]*sizeof(statenode));
		  final_nzc_path_b[b2]=final_nzc_path_b[b1];
		  state_path_b_end_cost[b2][final_nzc_path_b[b2]]=state_path_b_end_cost[b1][final_nzc_path_b[b1]];
          // The following is used for watermarking
		  i=wm_pos[kk];  	  Ind_Threshold=(int)ceil((double)(Q[i]+rdt)/(double)qtbl_1d[i]); 
		  tmp=Ind_Threshold;  size=0;
          while(tmp)
		  {
	        size++;             tmp>>=1;
		   }
		  s=size;
          
	 	  ind2=quantize1c(dctcoef_2b[i],i);     curr_min_2=maxnumber;   	size=s;
    	  if(ind2<=0)
		  {
	       if(-Ind_Threshold<=ind2)  	       id_2[i][size]=-Ind_Threshold;
           else if(-s_max[size]>=ind2)  	       id_2[i][size]=-s_max[size];
	       else                      	       id_2[i][size]=ind2;
	       d_2[i][size]=sqr(double(dctcoef_2b[i]-id_2[i][size]*qtbl_1d[i]));
	 
	       for (size=s+1; size<11; size++)
		   {
	        if (-s_min[size]<=ind2)             id_2[i][size]=-s_min[size];
	        else if(-s_max[size]>=ind2)         id_2[i][size]=-s_max[size];
	        else                                id_2[i][size]=ind2;
   	        d_2[i][size]=sqr(double(dctcoef_2b[i]-id_2[i][size]*qtbl_1d[i]));
		   }
		  }
	      else
		  {
	       if(ind2<=Ind_Threshold)              id_2[i][size]=Ind_Threshold;
	       else if(s_max[size]<=ind2)           id_2[i][size]=s_max[size];
	       else                                 id_2[i][size]=ind2;
           d_2[i][size]=sqr(double(dctcoef_2b[i]-id_2[i][size]*qtbl_1d[i]));

	       for (size=s+1; size<11; size++)
		   {
		    if (ind2<=s_min[size])             id_2[i][size]=s_min[size];
		    else if(s_max[size]<=ind2)         id_2[i][size]=s_max[size];
		    else                               id_2[i][size]=ind2;
            d_2[i][size]=sqr(double(dctcoef_2b[i]-id_2[i][size]*qtbl_1d[i]));
		   }
		  }

        // first 15 states do not have full incoming states
		 t1=0; t2=0;
	     if(block_b_tree[b2].wm_nozero_no>=0)
		 { // count the number of watermarking states having no cost
		 	k=(i-wm_pos[block_b_tree[b2].wm_nozero_no]>15)?15:(i-wm_pos[block_b_tree[b2].wm_nozero_no]-1);
			for(j1=block_b_tree[b2].wm_nozero_no+1;j1<kk;j1++)
			{	
				 if((wm_pos[j1]-wm_pos[block_b_tree[b2].wm_nozero_no])<=15)
				 { wm_nocost_pos[t1]=wm_pos[j1];      t1++;      t2=t1;
				 }
				 else 
				 { 
				  for(k1=0;k1<t2;k1++)
				    if(wm_pos[j1]-wm_nocost_pos[k1]==16) wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			}
		 }
         else	  
		 {
			  k=(i>15)?15:(i-1);  // first 15 states do not have full incoming states
                // for each incoming state j (j is from 0 to maximum incoming states)
		      for(j1=0;j1<kk;j1++)
			  {	
				if(wm_pos[j1]<=15)
				{ wm_nocost_pos[t1]=wm_pos[j1];  	  t1++;       t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				     if(wm_pos[j1]-wm_nocost_pos[k1]==16)  wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				}
			  }
		 }
	          
	     for(j=0; j<=k; j++)
		 {
			  thr=0; 
			  for(m=0;m<t2;m++)
			  {
				if(j==(i-wm_nocost_pos[m]-1))
				{
				  thr=1;
				  break;
				}
			  }
		      if(thr==0)
			   {
		         for(size=s; size<11; size++)
				   update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
			   }
		 }//end of j

         if (i<63)
		 {
			state_path_b_end_cost[b2][i]=state_path_b[b2][i].min_cost+eob_cost_2[i];
		    final_nzc_path_b[b2]=i;
		 } 
		 block_b_tree[b2].cost_inwm_status=1;
         if(state_path_b[b2][i].min_cost+state_path_a_end_cost[a1][final_nzc_path_a[a1]]<tempcost)
		 {
			tempcost=state_path_b[b2][i].min_cost+state_path_a_end_cost[a1][final_nzc_path_a[a1]];
			path_a_no=a2;  			path_b_no=b2;
		 }
	   }//end of jj
   }//end of ttt
			 
	node[kk][1][kk].block_a_graph_no = path_a_no;  	node[kk][1][kk].block_b_graph_no = path_b_no; 
	a2=path_a_no;   	b2=path_b_no;
	block_b_tree[b2].wm_nozero_no=kk;  	a1=block_a_tree[a2].parent_node_number;

	block_a_tree[a2].wm_nozero_no=block_a_tree[a1].wm_nozero_no; 	curr_min=maxnumber;
	if(block_a_tree[a2].cost_inwm_status==0)
	{ 
	  memcpy(state_path_a[a2], state_path_a[a1],wm_pos[kk]*sizeof(statenode));
	  final_nzc_path_a[a2]=final_nzc_path_a[a1];
	  state_path_a_end_cost[a2][final_nzc_path_a[a2]]=state_path_a_end_cost[a1][final_nzc_path_a[a1]];

	  i=wm_pos[kk];  	  t1=0; t2=0;
	  if(block_a_tree[a2].wm_nozero_no>=0)
	  { //count the number of watermarking sates having no cost
		if((i-wm_pos[block_a_tree[a2].wm_nozero_no])>15 && i<63) 
		 {
			for(j1=block_a_tree[a2].wm_nozero_no+1;j1<kk;j1++)
			{	
				if((wm_pos[j1]-wm_pos[block_a_tree[a2].wm_nozero_no])<=15)
				{ 
					wm_nocost_pos[t1]=wm_pos[j1];   t1++;    t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				    if(wm_pos[j1]-wm_nocost_pos[k1]==16) wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			 }
			 thr=0;
			 for(m=0;m<t2;m++)
			 {
				if((i-16 )==wm_nocost_pos[m])
				{
				  thr=1;
				  break;
				}
			 }
			 if(thr==0) 
		         update_cost(i,15,0,dist[i][15], sqr(c_abs[i]),0, state_path_a[a2]);
		   }
	  }
	  else
	  {
	     if(i>15 && i<63)  //wm_nozero_no<=0
		 {
			  for(j1=0;j1<kk;j1++)
			  {	
				if(wm_pos[j1]<=15)
				{ 
					wm_nocost_pos[t1]=wm_pos[j1]; 	  t1++;    t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				  if(wm_pos[j1]-wm_nocost_pos[k1]==16)
						wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			  }
			  thr=0;
			  for(m=0;m<t2;m++)
			  {
				if((i-16 )==wm_nocost_pos[m])
				{
				  thr=1;
				  break;
				}
			  }
			  if(thr==0)  update_cost(i,15,0,dist[i][15], sqr(c_abs[i]),0, state_path_a[a2]); 
			}
		 }
	  block_a_tree[a2].cost_inwm_status=1;
	 }
    // The above computed for the watermarking state, next for the following states
	 if(block_b_tree[b2].cost_status_2==0)
	 {
	    for(i=wm_pos[kk]+1;i<end_right;i++)
		{ 
		  curr_min_2=maxnumber;
		  k=(i-wm_pos[block_b_tree[b2].wm_nozero_no]>15)?15:(i-wm_pos[block_b_tree[b2].wm_nozero_no]-1);
		  for(j=0; j<=k; j++)
		  {
		    switch (indsi_2[i])
			{
             case 0:
	          for(size=1; size<3; size++)   update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
             break;
             case 1:
	          for(size=1; size<4; size++)   update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
             break;
             case 10:
              for (size=10; size>8; size--) update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
             break;
	         default: //2~9 
             for (size=indsi_2[i]-1; size<indsi_2[i]+2; size++)
	           update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
			} // end of switch
         }//end of j loop
	
         // for each state, find the cost of going EOB after this nonzero state
         if (i<63)
		 {
			 state_path_b_end_cost[b2][i]=state_path_b[b2][i].min_cost+eob_cost_2[i];
			 if (state_path_b_end_cost[b2][i]<state_path_b_end_cost[b2][final_nzc_path_b[b2]])
			 final_nzc_path_b[b2]=i;
		 } 
          // consider (15,0) case for i>=16 (consider this AFTER ending-cost calculation!)
         if ((i-wm_pos[block_b_tree[b2].wm_nozero_no]>15)&&(i<63)&&(final_nzc_path_b[b2]!=i))
		  	  update_cost_2(i,15,0,dist_2[i][15],  sqr(c_abs_2[i]), 0, state_path_b[b2]);
		 
		 if (curr_min_2<0)  printf("row_b=%d, col_b=%d, i=%d\n", row_b, col_b, i);
		} // end of i loop for the calculation of the minimum cost for one state   
		
	    block_b_tree[b2].cost_status_2=1;
	}//end if block_a_tree[a2].cost_status_2==0
		  
    if(block_a_tree[a2].cost_status_2==0)
	{
	  for(i=wm_pos[kk]+1;i<end_right;i++)
	  { 
		  t1=0; t2=0;     curr_min=maxnumber;
		  if(block_a_tree[a2].wm_nozero_no>=0)
		  {
			k=(i-wm_pos[block_a_tree[a2].wm_nozero_no]>15)?15:(i-wm_pos[block_a_tree[a2].wm_nozero_no]-1);
		    for(j1=block_a_tree[a2].wm_nozero_no+1;j1<=kk;j1++)
			 {	
				if((wm_pos[j1]-wm_pos[block_a_tree[a2].wm_nozero_no])<=15)
				{ 
					wm_nocost_pos[t1]=wm_pos[j1];   t1++;    t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				    if(wm_pos[j1]-wm_nocost_pos[k1]==16) wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			 }
		  }
          else	  
		  {
			  k=(i>15)?15:(i-1);  // first 15 states do not have full incoming states
                // for each incoming state j (j is from 0 to maximum incoming states)
		      for(j1=0;j1<=kk;j1++)
			  {	
				if(wm_pos[j1]<=15)
				{ 
					wm_nocost_pos[t1]=wm_pos[j1]; 	  t1++;  	  t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				     if(wm_pos[j1]-wm_nocost_pos[k1]==16) 	wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			  }
		  }
	           
	      for(j=0; j<=k; j++)
		  {
			  thr=0;
			  for(m=0;m<t2;m++)
			  {
				if(j==(i-wm_nocost_pos[m]-1))
				{
				  thr=1;
				  break;
				}
			  }
			  if(thr==0)
			  {
		         switch (indsi[i])
				 {
	               case 0:
		           for(size=1; size<3; size++) update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
                   break;
                   case 1:
		           for(size=1; size<4; size++) update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
                   break;
	               case 10:
                   for (size=10; size>8; size--) update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
                   break;
		           default: //2~9 
                   for (size=indsi[i]-1; size<indsi[i]+2; size++) 
					   update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
				   } // end of switch
			  }//end if thr
		 }//end of j loop
	
	     // for each state, find the cost of going EOB after this nonzero state
	     if (i<63)
		 {
			state_path_a_end_cost[a2][i]=state_path_a[a2][i].min_cost+eob_cost[i];
			if (state_path_a_end_cost[a2][i]<state_path_a_end_cost[a2][final_nzc_path_a[a2]])
			final_nzc_path_a[a2]=i;
		 } 
        
		 // consider (15,0) case for i>=16 (consider this AFTER ending-cost calculation!)
         if(block_a_tree[a2].wm_nozero_no>=0)       v1=i-wm_pos[block_a_tree[a2].wm_nozero_no];
		 else v1=i; //The following compute the number of watermarking states having no cost
		 if (v1>15&&i<63)
		 {
			thr=0;
			for(m=0;m<t2;m++)
			{
				if((i-16 )==wm_nocost_pos[m])
				{
				  thr=1;
				  break;
				}
			}
	    	if((thr==0)&&(final_nzc_path_a[a2]!=i))
			  update_cost(i,15,0,dist[i][15],sqr(c_abs[i]),0,state_path_a[a2]);
		 }

		 if (curr_min<0)  printf("row_b=%d, col_b=%d, i=%d\n", row_b, col_b, i);
		} // end of i loop for the calculation of the minimum cost for one state   
	   block_a_tree[a2].cost_status_2=1;
	}//end of  if block_b_tree[b2].cost_status_2
	       
   for(i=0;i<kk;i++)
   {
	   tmp_cost_1[i]=maxnumber;   path_a_no_1[i]=0;    path_b_no_1[i]=0;
   }
	   
   for(ttt=0;ttt<=1;ttt=ttt+1)
   { 
	  for(jj=0;jj<num_comb[kk-1][ttt];jj++)
	  {
	     a1=node[kk-1][ttt][jj].block_a_graph_no;   	 b1=node[kk-1][ttt][jj].block_b_graph_no;
		 a2=block_a_tree[a1].next_level_node_value[0];   b2=block_b_tree[b1].next_level_node_value[1];
		 block_b_tree[b2].wm_nozero_no=block_b_tree[b1].wm_nozero_no;

		 memcpy(state_path_b[b2], state_path_b[b1],wm_pos[kk]*sizeof(statenode));
		 final_nzc_path_b[b2]=final_nzc_path_b[b1];
		 state_path_b_end_cost[b2][final_nzc_path_b[b2]]=state_path_b_end_cost[b1][final_nzc_path_b[b1]];

		 i=wm_pos[kk];   		 Ind_Threshold=(int)ceil((double)((Q[i]+rdt))/(double)qtbl_1d[i]);
	     tmp=Ind_Threshold;      size=0;
         while(tmp)
		 {
	       size++;     tmp>>=1;
		 }
		 s=size;

		 ind2=quantize1c(dctcoef_2b[i],i);      curr_min_2=maxnumber;     	size=s;
         if(ind2<=0)
		 {
	      if(-Ind_Threshold<=ind2)         id_2[i][size]=-Ind_Threshold;
          else if(-s_max[size]>=ind2)      id_2[i][size]=-s_max[size];
	      else                             id_2[i][size]=ind2;
	      d_2[i][size]=sqr(double(dctcoef_2b[i]-id_2[i][size]*qtbl_1d[i]));
	 
	      for (size=s+1; size<11; size++)
		  {
	       if (-s_min[size]<=ind2)         id_2[i][size]=-s_min[size];
	       else if(-s_max[size]>=ind2)     id_2[i][size]=-s_max[size];
	       else                            id_2[i][size]=ind2;
           d_2[i][size]=sqr(double(dctcoef_2b[i]-id_2[i][size]*qtbl_1d[i]));
		  }
		 }
	     else
		 {
	      if(ind2<=Ind_Threshold)  	       id_2[i][size]=Ind_Threshold;
	      else if(s_max[size]<=ind2)       id_2[i][size]=s_max[size];
	      else                             id_2[i][size]=ind2;
          d_2[i][size]=sqr(double(dctcoef_2b[i]-id_2[i][size]*qtbl_1d[i]));

	      for (size=s+1; size<11; size++)
		  {
		    if (ind2<=s_min[size])         id_2[i][size]=s_min[size];
		    else if(s_max[size]<=ind2)     id_2[i][size]=s_max[size];
		    else                           id_2[i][size]=ind2;
            d_2[i][size]=sqr(double(dctcoef_2b[i]-id_2[i][size]*qtbl_1d[i]));
		  }
		 }

         t1=0; t2=0;
         if(block_b_tree[b2].wm_nozero_no>=0)
		 {  // compute the number of watermaring states having no cost
		 	k=(i-wm_pos[block_b_tree[b2].wm_nozero_no]>15)?15:(i-wm_pos[block_b_tree[b2].wm_nozero_no]-1);
			for(j1=block_b_tree[b2].wm_nozero_no+1;j1<kk;j1++)
			{	
				 if((wm_pos[j1]-wm_pos[block_b_tree[b2].wm_nozero_no])<=15)
				 { 
					 wm_nocost_pos[t1]=wm_pos[j1]; 	  t1++;     t2=t1;
				 }
				 else 
				 { 
				  for(k1=0;k1<t2;k1++)
				    if(wm_pos[j1]-wm_nocost_pos[k1]==16)  wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			}
		 }
         else	  
		 {
		    k=(i>15)?15:(i-1);  // first 15 states do not have full incoming states
            // for each incoming state j (j is from 0 to maximum incoming states)
		    for(j1=0;j1<kk;j1++)
			{	
				if(wm_pos[j1]<=15)
				{ 
					wm_nocost_pos[t1]=wm_pos[j1];    t1++;    t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++) 
				     if(wm_pos[j1]-wm_nocost_pos[k1]==16)   wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			 }
		 }
	          
	      for(j=0; j<=k; j++)
		  {
			  thr=0; 
			  for(m=0;m<t2;m++)
			  {
				if(j==(i-wm_nocost_pos[m]-1))
				{
				  thr=1;
				  break;
				}
			  }
			  if(thr==0)
			  {
		        for(size=s; size<11; size++)
				  update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
			  }
		  }//end of j

         if (i<63)
		 {
			state_path_b_end_cost[b2][i]=state_path_b[b2][i].min_cost+eob_cost_2[i];
		    final_nzc_path_b[b2]=i;
		 } 

		 block_b_tree[b2].cost_inwm_status=1;
	     mm=block_a_tree[a1].wm_nozero_no+1;
         if(state_path_b[b2][i].min_cost+state_path_a_end_cost[a1][final_nzc_path_a[a1]]<tmp_cost_1[mm])
		 {
		  tmp_cost_1[mm]=state_path_b[b2][i].min_cost+state_path_a_end_cost[a1][final_nzc_path_a[a1]];
		  path_a_no_1[mm]=a2;      path_b_no_1[mm]=b2;
		}
	   }//end of jj
   }//end of ttt
			 
   for(mm=0;mm<kk;mm++)	
   {   
     node[kk][1][mm].block_a_graph_no = path_a_no_1[mm];  node[kk][1][mm].block_b_graph_no = path_b_no_1[mm]; 
     a2=node[kk][1][mm].block_a_graph_no ;                b2=node[kk][1][mm].block_b_graph_no ;
     block_b_tree[b2].wm_nozero_no=kk;

     a1=block_a_tree[a2].parent_node_number;      block_a_tree[a2].wm_nozero_no=block_a_tree[a1].wm_nozero_no;
	
     if(block_a_tree[a2].cost_inwm_status==0)
	 { 
	  memcpy(state_path_a[a2], state_path_a[a1],wm_pos[kk]*sizeof(statenode));
	  final_nzc_path_a[a2]=final_nzc_path_a[a1];
	  state_path_a_end_cost[a2][final_nzc_path_a[a2]]=state_path_a_end_cost[a1][final_nzc_path_a[a1]];

	  i=wm_pos[kk];    curr_min=maxnumber;   	  t1=0; t2=0;
	  if(block_a_tree[a2].wm_nozero_no>=0)
	  {  //compute the number of watermarking states having no cost
		 if((i-wm_pos[block_a_tree[a2].wm_nozero_no])>15 && i<63) 
		 {
			 for(j1=block_a_tree[a2].wm_nozero_no+1;j1<kk;j1++)
			  {	
				if((wm_pos[j1]-wm_pos[block_a_tree[a2].wm_nozero_no])<=15)
				{
					wm_nocost_pos[t1]=wm_pos[j1]; 	  t1++;    t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				  if(wm_pos[j1]-wm_nocost_pos[k1]==16)
						wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				}
			  }
			
			  thr=0;
			  for(m=0;m<t2;m++)
			  {
				if((i-16 )==wm_nocost_pos[m])
				{
				  thr=1;
				  break;
				}
			  }
			  if(thr==0)   update_cost(i,15,0,dist[i][15], sqr(c_abs[i]), 0,state_path_a[a2]);
		  }
		}
		else
		{
		    if(i>15 && i<63)  //????
			{
			  for(j1=0;j1<kk;j1++)
			  {	
				if(wm_pos[j1]<=15)
				{ 
					wm_nocost_pos[t1]=wm_pos[j1];   t1++;  	  t2=t1;
				}
			    else 
				{ 
				  for(k1=0;k1<t2;k1++)
				     if(wm_pos[j1]-wm_nocost_pos[k1]==16)
						wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			  }
			
			  thr=0;
			  for(m=0;m<t2;m++)
			  {
				if((i-16 )==wm_nocost_pos[m])
				{
				  thr=1;
				  break;
				}
			  }
			  if(thr==0)  update_cost(i,15,0,dist[i][15], sqr(c_abs[i]), 0, state_path_a[a2]);
			 }
		 }
	  block_a_tree[a2].cost_inwm_status=1;
	 }
     // The above compute the watermarking state, next compute the following states
	 if(block_b_tree[b2].cost_status_2==0)
	 {
		for(i=wm_pos[kk]+1;i<end_right;i++)
		{ 
		  curr_min_2=maxnumber;
		  k=(i-wm_pos[block_b_tree[b2].wm_nozero_no]>15)?15:(i-wm_pos[block_b_tree[b2].wm_nozero_no]-1);
			           
	      for(j=0; j<=k; j++)
		  {
		    switch (indsi_2[i])
			{
             case 0:
	          for(size=1; size<3; size++) update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
             break;
             case 1:
	          for(size=1; size<4; size++) update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
             break;
             case 10:
              for (size=10; size>8; size--) update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
             break;
	         default: //2~9 
              for (size=indsi_2[i]-1; size<indsi_2[i]+2; size++)
	           update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
			} // end of switch
           }//end of j loop
	
         // for each state, find the cost of going EOB after this nonzero state
         if (i<63)
		 {
			 state_path_b_end_cost[b2][i]=state_path_b[b2][i].min_cost+eob_cost_2[i];
			 if (state_path_b_end_cost[b2][i]<state_path_b_end_cost[b2][final_nzc_path_b[b2]])
			     final_nzc_path_b[b2]=i;
		 } 
          // consider (15,0) case for i>=16 (consider this AFTER ending-cost calculation!)
         if ((i-wm_pos[block_b_tree[b2].wm_nozero_no])>15&&(i<63)&&(final_nzc_path_b[b2]!=i))
		  	  update_cost_2(i,15,0,dist_2[i][15],sqr(c_abs_2[i]),0,state_path_b[b2]);

		 if(curr_min_2<0)   printf("row_b=%d, col_b=%d, i=%d\n", row_b, col_b, i);
		} // end of i loop for the calculation of the minimum cost for one state   
	    block_b_tree[b2].cost_status_2=1;
	}//end if block_a_tree[a2].cost_status_2==0
		  
    if(block_a_tree[a2].cost_status_2==0)
	{
	  for(i=wm_pos[kk]+1;i<end_right;i++)
	  { 
		  t1=0; t2=0; 	      curr_min=maxnumber;
		  if(block_a_tree[a2].wm_nozero_no>=0)
		  {  //compute the number of watermarking states having no cost 
			 k=(i-wm_pos[block_a_tree[a2].wm_nozero_no]>15)?15:(i-wm_pos[block_a_tree[a2].wm_nozero_no]-1);
		     for(j1=block_a_tree[a2].wm_nozero_no+1;j1<=kk;j1++)
			 {	
				if((wm_pos[j1]-wm_pos[block_a_tree[a2].wm_nozero_no])<=15)
				{ 
					wm_nocost_pos[t1]=wm_pos[j1]; 	  t1++;     t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				     if(wm_pos[j1]-wm_nocost_pos[k1]==16)
						wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			 }
		  }
          else	  
		  {
			  k=(i>15)?15:(i-1);  // first 15 states do not have full incoming states
              // for each incoming state j (j is from 0 to maximum incoming states)
			  for(j1=0;j1<=kk;j1++)
			  {	
				if(wm_pos[j1]<=15)
				{
				  wm_nocost_pos[t1]=wm_pos[j1];    t1++;  	  t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				     if(wm_pos[j1]-wm_nocost_pos[k1]==16)
						wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				}
			  }
			}
	           
	        for(j=0; j<=k; j++)
			{
			  thr=0;
			  for(m=0;m<t2;m++)
			  {
				if(j==(i-wm_nocost_pos[m]-1))
				{
				  thr=1;
				  break;
				}
			  }
			  if(thr==0)
			  {
		        switch (indsi[i])
				{
	             case 0:
		         for(size=1; size<3; size++)  update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
                 break;
                 case 1:
		         for(size=1; size<4; size++)  update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
                 break;
	             case 10:
                 for (size=10; size>8; size--) update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
                 break;
		         default: //2~9 
                 for (size=indsi[i]-1; size<indsi[i]+2; size++)
		           update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
				} // end of switch
			  }//end if thr
			}//end of j loop
	
	     // for each state, find the cost of going EOB after this nonzero state
	     if (i<63)
		 {
			state_path_a_end_cost[a2][i]=state_path_a[a2][i].min_cost+eob_cost[i];
			if (state_path_a_end_cost[a2][i]<state_path_a_end_cost[a2][final_nzc_path_a[a2]])
			final_nzc_path_a[a2]=i;
		} 
         // consider (15,0) case for i>=16 (consider this AFTER ending-cost calculation!)
		 if(block_a_tree[a2].wm_nozero_no>=0)   v1=i-wm_pos[block_a_tree[a2].wm_nozero_no];
		 else v1=i;
         if (v1>15&&i<63)
		 {
		   thr=0;
		   for(m=0;m<t2;m++)
		   {
				if((i-16 )==wm_nocost_pos[m])
				{
				  thr=1;
				  break;
				}
			}
		    if((thr==0)&&(final_nzc_path_a[a2]!=i))  
			  update_cost(i,15,0,dist[i][15],sqr(c_abs[i]),0,state_path_a[a2]);
		 }

		 if (curr_min<0)    printf("row_b=%d, col_b=%d, i=%d\n", row_b, col_b, i);
		
	  } // end of i loop for the calculation of the minimum cost for one state   
	 block_a_tree[a2].cost_status_2=1;
	}//end of  if block_b_tree[b2].cost_status_2
   }//end of mm
   
   // Next is used to updata node[kk][2]
   tempcost=maxnumber;     path_a_no=0;      path_b_no=0;
   for(ttt=1;ttt<4;ttt=ttt+2)
	{ 
	   for(jj=0;jj<num_comb[kk-1][ttt];jj++)
	   {
	      a1=node[kk-1][ttt][jj].block_a_graph_no; 	      b1=node[kk-1][ttt][jj].block_b_graph_no;
		  a2=block_a_tree[a1].next_level_node_value[1];   b2=block_b_tree[b1].next_level_node_value[0];

		  block_a_tree[a2].wm_nozero_no=block_a_tree[a1].wm_nozero_no;
		  memcpy(state_path_a[a2], state_path_a[a1],wm_pos[kk]*sizeof(statenode));
		  final_nzc_path_a[a2]=final_nzc_path_a[a1];
		  state_path_a_end_cost[a2][final_nzc_path_a[a2]]=state_path_a_end_cost[a1][final_nzc_path_a[a1]];

		  i=wm_pos[kk];
		  Ind_Threshold=(int)ceil((double)(Q[i]+rdt)/(double)qtbl_1d[i]);
	      tmp=Ind_Threshold; 	      size=0;
          while(tmp)
		  {
	         size++;
             tmp>>=1;
		   }

		  s=size;  	  ind1=quantize1c(dctcoef_1b[i],i);      curr_min=maxnumber;
          if(ind1<=0)
		  {
	       if(-Ind_Threshold<=ind1)   	         id[i][size]=-Ind_Threshold;
           else if(-s_max[size]>=ind1) 	         id[i][size]=-s_max[size];
	       else                      	         id[i][size]=ind1;
	       d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
	 
	       for (size=s+1; size<11; size++)
		   {
	         if (-s_min[size]<=ind1) 	           id[i][size]=-s_min[size];
	         else if(-s_max[size]>=ind1) 	       id[i][size]=-s_max[size];
	         else                   		       id[i][size]=ind1;
	         d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
		   }
		  }
	      else
		  {
	       if(ind1<=Ind_Threshold)        	        id[i][size]=Ind_Threshold;
	       else if(s_max[size]<=ind1)     		    id[i][size]=s_max[size];
	       else                         		    id[i][size]=ind1;
           d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));

	       for (size=s+1; size<11; size++)
		   {
		     if (ind1<=s_min[size])    		       id[i][size]=s_min[size];
		     else if(s_max[size]<=ind1)		       id[i][size]=s_max[size];
		     else                   			   id[i][size]=ind1;
             d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
		   }
		  }
			  
		  t1=0; t2=0;
          if(block_a_tree[a2].wm_nozero_no>=0)
		  {  // compute the number of watermarking states having no cost
		 	 k=(i-wm_pos[block_a_tree[a2].wm_nozero_no]>15)?15:(i-wm_pos[block_a_tree[a2].wm_nozero_no]-1);
			 for(j1=block_a_tree[a2].wm_nozero_no+1;j1<kk;j1++)
			 {	
				if((wm_pos[j1]-wm_pos[block_a_tree[a2].wm_nozero_no])<=15)
				{
					wm_nocost_pos[t1]=wm_pos[j1];  	  t1++;    t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				    if(wm_pos[j1]-wm_nocost_pos[k1]==16)
						wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			 }
		  }
          else	  
		  {
			  k=(i>15)?15:(i-1);  // first 15 states do not have full incoming states
                // for each incoming state j (j is from 0 to maximum incoming states)
			  for(j1=0;j1<kk;j1++)
			  {	
				if(wm_pos[j1]<=15)
				{ 
					wm_nocost_pos[t1]=wm_pos[j1];   t1++;    t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				    if(wm_pos[j1]-wm_nocost_pos[k1]==16)
						wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			  }
			}
	           
	        for(j=0; j<=k; j++)
			{
			  thr=0;
			  for(m=0;m<t2;m++)
			  {
				if(j==(i-wm_nocost_pos[m]-1))
				{
				  thr=1;
				  break;
				}
			  }
					  
              if(thr==0)
			  {
		        for(size=s; size<11; size++)   update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
			  }
		   }//end of j

          if (i<63)
		  {
			state_path_a_end_cost[a2][i]=state_path_a[a2][i].min_cost+eob_cost[i];
			final_nzc_path_a[a2]=i;
		  } 
		 block_a_tree[a2].cost_inwm_status=1;
         if(state_path_a[a2][i].min_cost+state_path_b_end_cost[b1][final_nzc_path_b[b1]]<tempcost)
		 {
			tempcost=state_path_a[a2][i].min_cost+state_path_b_end_cost[b1][final_nzc_path_b[b1]];
			path_a_no=a2; 			path_b_no=b2;
		 }
	   }//end of jj
   }//end of ttt
			 
	node[kk][2][kk].block_a_graph_no=path_a_no;  	node[kk][2][kk].block_b_graph_no=path_b_no; 
	a2=path_a_no; 	b2=path_b_no;        
	block_a_tree[a2].wm_nozero_no=kk;    	b1=block_b_tree[b2].parent_node_number;
	block_b_tree[b2].wm_nozero_no=block_b_tree[b1].wm_nozero_no;
	
	if(block_b_tree[b2].cost_inwm_status==0)
	{ 
	  memcpy(state_path_b[b2], state_path_b[b1],wm_pos[kk]*sizeof(statenode));
	  final_nzc_path_b[b2]=final_nzc_path_b[b1];
	  state_path_b_end_cost[b2][final_nzc_path_b[b2]]=state_path_b_end_cost[b1][final_nzc_path_b[b1]];

	  i=wm_pos[kk];  	  curr_min_2=maxnumber;  	  t1=0; t2=0;
	  if(block_b_tree[b2].wm_nozero_no>=0)
	  { 
		if((i-wm_pos[block_b_tree[b2].wm_nozero_no])>15 && i<63) 
		{    //compute the number of watermarking states having no cost  
			  for(j1=block_b_tree[b2].wm_nozero_no+1;j1<kk;j1++)
			  {	
				if((wm_pos[j1]-wm_pos[block_b_tree[b2].wm_nozero_no])<=15)
				{ 
					wm_nocost_pos[t1]=wm_pos[j1];   t1++;     t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				     if(wm_pos[j1]-wm_nocost_pos[k1]==16)
						wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			  }
			  thr=0;
			  for(m=0;m<t2;m++)
			  {
				if((i-16 )==wm_nocost_pos[m])
				{
				  thr=1;
				  break;
				}
			  }
			  if(thr==0)   update_cost_2(i,15,0,dist_2[i][15], sqr(c_abs_2[i]), 0,state_path_b[b2]);
		  }
		}
		else
		{
		   if(i>15 && i<63)  
		   {
			 for(j1=0;j1<kk;j1++)
			 {	
				if(wm_pos[j1]<=15)
				{ 
					wm_nocost_pos[t1]=wm_pos[j1]; 	  t1++;     t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				     if(wm_pos[j1]-wm_nocost_pos[k1]==16)
						wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			  }
			
			  thr=0;
			  for(m=0;m<t2;m++)
			  {
				if((i-16 )==wm_nocost_pos[m])
				{
				  thr=1;
				  break;
				}
			  }
			  if(thr==0)     update_cost_2(i,15,0,dist_2[i][15], sqr(c_abs_2[i]), 0,state_path_b[b2]); 
			 }
		  }
	  block_b_tree[b2].cost_inwm_status=1;
	 }

	 if(block_a_tree[a2].cost_status_2==0)
	 {
	   	for(i=wm_pos[kk]+1;i<end_right;i++)
		{ 
		  curr_min=maxnumber;
		  k=(i-wm_pos[block_a_tree[a2].wm_nozero_no]>15)?15:(i-wm_pos[block_a_tree[a2].wm_nozero_no]-1);
		  for(j=0; j<=k; j++)
		  {
		    switch (indsi[i])
			{
             case 0:
	         for(size=1; size<3; size++)  update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
             break;
             case 1:
	         for(size=1; size<4; size++)  update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
             break;
             case 10:
             for (size=10; size>8; size--) update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
             break;
	         default: //2~9 
             for (size=indsi[i]-1; size<indsi[i]+2; size++)
	           update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
			} // end of switch
           }//end of j loop
	
           // for each state, find the cost of going EOB after this nonzero state
           if (i<63)
		   {
			 state_path_a_end_cost[a2][i]=state_path_a[a2][i].min_cost+eob_cost[i];
			 if (state_path_a_end_cost[a2][i]<state_path_a_end_cost[a2][final_nzc_path_a[a2]])
			    final_nzc_path_a[a2]=i;
		   } 
           // consider (15,0) case for i>=16 (consider this AFTER ending-cost calculation!)
           if ((i-wm_pos[block_a_tree[a2].wm_nozero_no]>15)&&(i<63)&&(final_nzc_path_a[a2]!=i))
		      update_cost(i,15,0,dist[i][15],  sqr(c_abs[i]), 0, state_path_a[a2]);
		 
		   if (curr_min<0)    printf("row_b=%d, col_b=%d, i=%d\n", row_b, col_b, i);
		} // end of i loop for the calculation of the minimum cost for one state   
	    block_a_tree[a2].cost_status_2=1;
	}//end if block_a_tree[a2].cost_status_2==0
		  
    if(block_b_tree[b2].cost_status_2==0)
	{
	  for(i=wm_pos[kk]+1;i<end_right;i++)
	  { 
		  t1=0; t2=0;  curr_min_2=maxnumber;
		  if(block_b_tree[b2].wm_nozero_no>=0)
		  { // compute the number of watermarking states having no cost
			k=(i-wm_pos[block_b_tree[b2].wm_nozero_no]>15)?15:(i-wm_pos[block_b_tree[b2].wm_nozero_no]-1);
			for(j1=block_b_tree[b2].wm_nozero_no+1;j1<=kk;j1++)
			{	
				 if((wm_pos[j1]-wm_pos[block_b_tree[b2].wm_nozero_no])<=15)
				 {
					 wm_nocost_pos[t1]=wm_pos[j1];     t1++;   	  t2=t1;
				 }
				 else 
				 { 
				  for(k1=0;k1<t2;k1++)
				     if(wm_pos[j1]-wm_nocost_pos[k1]==16)
						wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			}
		  }
          else	  
		  {
			  k=(i>15)?15:(i-1);  // first 15 states do not have full incoming states
                // for each incoming state j (j is from 0 to maximum incoming states)
		      for(j1=0;j1<=kk;j1++)
			  {	
				if(wm_pos[j1]<=15)
				{ 
					wm_nocost_pos[t1]=wm_pos[j1];    	  t1++;   		  t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				    if(wm_pos[j1]-wm_nocost_pos[k1]==16)
						wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			  }
		  }
	          
	      for(j=0; j<=k; j++)
		  {
			  thr=0; 
			  for(m=0;m<t2;m++)
			  {
				if(j==(i-wm_nocost_pos[m]-1))
				{
				  thr=1;
				  break;
				}
			  }
					  
		      if(thr==0)
			  {
		         switch (indsi_2[i])
				 {
	               case 0:
		           for(size=1; size<3; size++)  update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
                   break;
                   case 1:
		           for(size=1; size<4; size++)  update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
                   break;
	               case 10:
                   for (size=10; size>8; size--) update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
                   break;
		           default: //2~9 
                   for (size=indsi_2[i]-1; size<indsi_2[i]+2; size++)
		            update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
				 } // end of switch
			  }//end if thr
		  }//end of j loop
	
	     // for each state, find the cost of going EOB after this nonzero state
	     if (i<63)
		 {
			state_path_b_end_cost[b2][i]=state_path_b[b2][i].min_cost+eob_cost_2[i];
			if (state_path_b_end_cost[b2][i]<state_path_b_end_cost[b2][final_nzc_path_b[b2]])
			final_nzc_path_b[b2]=i;
		} 
         // consider (15,0) case for i>=16 (consider this AFTER ending-cost calculation!)
		if(block_b_tree[b2].wm_nozero_no>=0)       v1=i-wm_pos[block_b_tree[b2].wm_nozero_no];
		else v1=i;
        if (v1>15&&i<63)
		{
			thr=0;
			for(m=0;m<t2;m++)
			{
				if((i-16 )==wm_nocost_pos[m])
				{
				  thr=1;
				  break;
				}
			}
				
			if((thr==0)&& (final_nzc_path_b[b2]=i))
			  update_cost_2(i,15,0,dist_2[i][15],sqr(c_abs_2[i]),0,state_path_b[b2]);
		 }

		 if (curr_min_2<0)    printf("row_b=%d, col_b=%d, i=%d\n", row_b, col_b, i);
		} // end of i loop for the calculation of the minimum cost for one state   
		block_b_tree[b2].cost_status_2=1;
	}//end of  if block_b_tree[b2].cost_status_2
  
   for(i=0;i<kk;i++)
   {
	   tmp_cost_1[i]=maxnumber;
	   path_a_no_1[i]=0;
	   path_b_no_1[i]=0;
   }
	   
   for(ttt=0;ttt<4;ttt=ttt+2)
	{ 
	  for(jj=0;jj<num_comb[kk-1][ttt];jj++)
	  {
	     a1=node[kk-1][ttt][jj].block_a_graph_no;  b1=node[kk-1][ttt][jj].block_b_graph_no;
		 a2=block_a_tree[a1].next_level_node_value[1]; 	 b2=block_b_tree[b1].next_level_node_value[0];

		 block_a_tree[a2].wm_nozero_no=block_a_tree[a1].wm_nozero_no;
		 memcpy(state_path_a[a2], state_path_a[a1],wm_pos[kk]*sizeof(statenode));
		 final_nzc_path_a[a2]=final_nzc_path_a[a1];
		 state_path_a_end_cost[a2][final_nzc_path_a[a2]]=state_path_a_end_cost[a1][final_nzc_path_a[a1]];

		 i=wm_pos[kk];	 Ind_Threshold=(int)ceil((double)(Q[i]+rdt)/(double)qtbl_1d[i]);
	     tmp=Ind_Threshold; 	     size=0;
         while(tmp)
		 {
	         size++;
             tmp>>=1;
		 }
		 
		 s=size;   ind1=quantize1c(dctcoef_1b[i],i);      curr_min=maxnumber;
	     if(ind1<=0)
		 {
	       if(-Ind_Threshold<=ind1)   	        id[i][size]=-Ind_Threshold;
           else if(-s_max[size]>=ind1) 	        id[i][size]=-s_max[size];
	       else                     	        id[i][size]=ind1;
	       d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
	 
	       for (size=s+1; size<11; size++)
		   {
	         if (-s_min[size]<=ind1)            id[i][size]=-s_min[size];
	         else if(-s_max[size]>=ind1)        id[i][size]=-s_max[size];
	         else                               id[i][size]=ind1;
	         d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
		   }
		 }
	     else
		 {
	       if(ind1<=Ind_Threshold)     	        id[i][size]=Ind_Threshold;
	       else if(s_max[size]<=ind1)		    id[i][size]=s_max[size];
	       else                      		    id[i][size]=ind1;
           d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));

	       for (size=s+1; size<11; size++)
		   {
		     if (ind1<=s_min[size])		        id[i][size]=s_min[size];
		     else if(s_max[size]<=ind1)         id[i][size]=s_max[size];
		     else                			    id[i][size]=ind1;
             d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
		   }
		 }
		
		 t1=0; t2=0;
         if(block_a_tree[a2].wm_nozero_no>=0)
		 {  //compute the number of watermarking states having no cost
		 	k=(i-wm_pos[block_a_tree[a2].wm_nozero_no]>15)?15:(i-wm_pos[block_a_tree[a2].wm_nozero_no]-1);
		    for(j1=block_a_tree[a2].wm_nozero_no+1;j1<kk;j1++)
			{	
				if((wm_pos[j1]-wm_pos[block_a_tree[a2].wm_nozero_no])<=15)
				{ 
					wm_nocost_pos[t1]=wm_pos[j1]; 	  t1++;    t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				    if(wm_pos[j1]-wm_nocost_pos[k1]==16)
						wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			 }
		 }
         else	  
		 {
			  k=(i>15)?15:(i-1);  // first 15 states do not have full incoming states
                // for each incoming state j (j is from 0 to maximum incoming states)
			  for(j1=0;j1<kk;j1++)
			  {	
				if(wm_pos[j1]<=15)
				{
					wm_nocost_pos[t1]=wm_pos[j1];    t1++;    t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				    if(wm_pos[j1]-wm_nocost_pos[k1]==16)
						wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			  }
		}
	           
	    for(j=0; j<=k; j++)
		{
		  thr=0;
		  for(m=0;m<t2;m++)
		  {
				if(j==(i-wm_nocost_pos[m]-1))
				{
				  thr=1;
				  break;
				}
		  }
					        
		  if(thr==0)
		  {
		       for(size=s; size<11; size++)
				  update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
		  }
		}//end of j

        if (i<63)
		{
			state_path_a_end_cost[a2][i]=state_path_a[a2][i].min_cost+eob_cost[i];
	       	final_nzc_path_a[a2]=i;
		} 

		block_a_tree[a2].cost_inwm_status=1; 		mm=block_b_tree[b1].wm_nozero_no+1;
        if(state_path_a[a2][i].min_cost+state_path_b_end_cost[b1][final_nzc_path_b[b1]]<tmp_cost_1[mm])
		{
		  tmp_cost_1[mm]=state_path_a[a2][i].min_cost+state_path_b_end_cost[b1][final_nzc_path_b[b1]];
		  path_a_no_1[mm]=a2; 		  path_b_no_1[mm]=b2;
		}

	   }//end of jj
   }//end of ttt
			 
   for(mm=0;mm<kk;mm++)	
   {   
     node[kk][2][mm].block_a_graph_no = path_a_no_1[mm];  	 node[kk][2][mm].block_b_graph_no = path_b_no_1[mm]; 
  	 a2=node[kk][2][mm].block_a_graph_no ;   	             b2=node[kk][2][mm].block_b_graph_no ;
     block_a_tree[a2].wm_nozero_no=kk;       b1=block_b_tree[b2].parent_node_number;
     block_b_tree[b2].wm_nozero_no=block_b_tree[b1].wm_nozero_no;
	
     if(block_b_tree[b2].cost_inwm_status==0)
	 { 
	  memcpy(state_path_b[b2], state_path_b[b1],wm_pos[kk]*sizeof(statenode));
	  final_nzc_path_b[b2]=final_nzc_path_b[b1];
	  state_path_b_end_cost[b2][final_nzc_path_b[b2]]=state_path_b_end_cost[b1][final_nzc_path_b[b1]];

	  i=wm_pos[kk];   	  curr_min_2=maxnumber;  	  t1=0; t2=0;
	  if(block_b_tree[b2].wm_nozero_no>=0)
	  { 
	     if((i-wm_pos[block_b_tree[b2].wm_nozero_no])>15 && i<63) 
		 {
			 for(j1=block_b_tree[b2].wm_nozero_no+1;j1<kk;j1++)
			  {	
				if((wm_pos[j1]-wm_pos[block_b_tree[b2].wm_nozero_no])<=15)
				{ 
					wm_nocost_pos[t1]=wm_pos[j1]; 	  t1++;  	  t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				     if(wm_pos[j1]-wm_nocost_pos[k1]==16)
						wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			  }
			
			  thr=0;
			  for(m=0;m<t2;m++)
			  {
				if((i-16 )==wm_nocost_pos[m])
				{
				  thr=1;
				  break;
				}
			  }
			  if(thr==0)   update_cost_2(i,15,0,dist_2[i][15], sqr(c_abs_2[i]),0, state_path_b[b2]);
		  }
		}
		else
		{
		   if(i>15 && i<63)  //????
		   {
			   for(j1=0;j1<kk;j1++)
			  {	
				if(wm_pos[j1]<=15)
				{
				  wm_nocost_pos[t1]=wm_pos[j1];   t1++; 		  t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				    if(wm_pos[j1]-wm_nocost_pos[k1]==16)
						wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			  }
			  thr=0;
			  for(m=0;m<t2;m++)
			  {
				if((i-16 )==wm_nocost_pos[m])
				{
				  thr=1;
				  break;
				}
			  }
			  if(thr==0)  update_cost_2(i,15,0,dist_2[i][15], sqr(c_abs_2[i]), 0,state_path_b[b2]);
			 }
		  }
	  block_b_tree[b2].cost_inwm_status=1;
	 }

	 if(block_a_tree[a2].cost_status_2==0)
	 {  
	    for(i=wm_pos[kk]+1;i<end_right;i++)
		{ 
	      curr_min=maxnumber;
		  k=(i-wm_pos[block_a_tree[a2].wm_nozero_no]>15)?15:(i-wm_pos[block_a_tree[a2].wm_nozero_no]-1);
			           
	      for(j=0; j<=k; j++)
		  {
		    switch (indsi[i])
			{
             case 0:
	          for(size=1; size<3; size++)    update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
             break;
             case 1:
	          for(size=1; size<4; size++)    update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
             break;
             case 10:
              for (size=10; size>8; size--)  update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
             break;
	         default: //2~9 
             for (size=indsi[i]-1; size<indsi[i]+2; size++)
	           update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
			} // end of switch
     	 }//end of j loop
	
         // for each state, find the cost of going EOB after this nonzero state
         if (i<63)
		 {
			 state_path_a_end_cost[a2][i]=state_path_a[a2][i].min_cost+eob_cost[i];
			 if (state_path_a_end_cost[a2][i]<state_path_a_end_cost[a2][final_nzc_path_a[a2]])
			 final_nzc_path_a[a2]=i;
		 } 
          // consider (15,0) case for i>=16 (consider this AFTER ending-cost calculation!)
         if ((i-wm_pos[block_a_tree[a2].wm_nozero_no]>15)&&(i<63) &&final_nzc_path_a[a2]!=i)
		      update_cost(i,15,0,dist[i][15], sqr(c_abs[i]),0,state_path_a[a2]);
		  
		  if (curr_min<0)       printf("row_b=%d, col_b=%d, i=%d\n", row_b, col_b, i);
		} // end of i loop for the calculation of the minimum cost for one state   
	    block_a_tree[a2].cost_status_2=1;
	}//end if block_a_tree[a2].cost_status_2==0
		  
    if(block_b_tree[b2].cost_status_2==0)
	{
	  for(i=wm_pos[kk]+1;i<end_right;i++)
	  { 
		  t1=0; t2=0;  	      curr_min_2=maxnumber;
		  if(block_b_tree[b2].wm_nozero_no>=0)
		  {
			k=(i-wm_pos[block_b_tree[b2].wm_nozero_no]>15)?15:(i-wm_pos[block_b_tree[b2].wm_nozero_no]-1);
			for(j1=block_b_tree[b2].wm_nozero_no+1;j1<=kk;j1++)
			{	
				 if((wm_pos[j1]-wm_pos[block_b_tree[b2].wm_nozero_no])<=15)
				 {
					 wm_nocost_pos[t1]=wm_pos[j1]; 	  t1++;    t2=t1;
				 }
				 else 
				 { 
				  for(k1=0;k1<t2;k1++)
				    if(wm_pos[j1]-wm_nocost_pos[k1]==16)
						wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			}
		 }
         else	  
		 {
		    k=(i>15)?15:(i-1);  // first 15 states do not have full incoming states
            // for each incoming state j (j is from 0 to maximum incoming states)
		    for(j1=0;j1<=kk;j1++)
			{	
				if(wm_pos[j1]<=15)
				{ 
					wm_nocost_pos[t1]=wm_pos[j1];    t1++;     t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				    if(wm_pos[j1]-wm_nocost_pos[k1]==16)
						wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			  }
		 }
	          
	     for(j=0; j<=k; j++)
		 {
		    thr=0; 
		    for(m=0;m<t2;m++)
			{
			   if(j==(i-wm_nocost_pos[m]-1))
			   {
				  thr=1;
				  break;
			   }
			 }
					  
		    if(thr==0)
			{
		      switch (indsi_2[i])
			  {
	          case 0:
		      for(size=1; size<3; size++)   update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
              break;
              case 1:
		      for(size=1; size<4; size++)   update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
              break;
	          case 10:
              for (size=10; size>8; size--) update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
              break;
		      default: //2~9 
              for (size=indsi_2[i]-1; size<indsi_2[i]+2; size++)
		       update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
			  } // end of switch
			}//end if thr
		 }//end of j loop
	
	     // for each state, find the cost of going EOB after this nonzero state
	     if (i<63)
		 {
			state_path_b_end_cost[b2][i]=state_path_b[b2][i].min_cost+eob_cost_2[i];
			if (state_path_b_end_cost[b2][i]<state_path_b_end_cost[b2][final_nzc_path_b[b2]])
			final_nzc_path_b[b2]=i;
		 } 
         // consider (15,0) case for i>=16 (consider this AFTER ending-cost calculation!)
         if(block_b_tree[b2].wm_nozero_no>=0)      v1=i-wm_pos[block_b_tree[b2].wm_nozero_no];
		 else v1=i;
				 
		 if (v1>15&&i<63)
		 {
			thr=0;
			for(m=0;m<t2;m++)
			{
				if((i-16 )==wm_nocost_pos[m])
				{
				  thr=1;
				  break;
				}
			  }
				
			if((thr==0)&&(final_nzc_path_b[b2]!=i))
			  update_cost_2(i,15,0,dist_2[i][15],sqr(c_abs_2[i]),0,state_path_b[b2]);
		 }

		 if (curr_min_2<0)  printf("row_b=%d, col_b=%d, i=%d\n", row_b, col_b, i);
		} // end of i loop for the calculation of the minimum cost for one state   
		block_b_tree[b2].cost_status_2=1;
	}//end of  if block_b_tree[b2].cost_status_2		 
 }	//end of mm	 
			 
	//The following is used to update node[kk][3]
   tempcost=maxnumber;    path_a_no=0;     path_b_no=0;
   for(ttt=0;ttt<4;ttt++)
   { 
      for(jj=0;jj<num_comb[kk-1][ttt];jj++)
	  {
	    a1=node[kk-1][ttt][jj].block_a_graph_no;      b1=node[kk-1][ttt][jj].block_b_graph_no;
		a2=block_a_tree[a1].next_level_node_value[2]; b2=block_b_tree[b1].next_level_node_value[2];
		block_a_tree[a2].wm_nozero_no=block_a_tree[a1].wm_nozero_no;
		block_b_tree[b2].wm_nozero_no=block_b_tree[b1].wm_nozero_no;

		memcpy(state_path_a[a2], state_path_a[a1],wm_pos[kk]*sizeof(statenode));
		final_nzc_path_a[a2]=final_nzc_path_a[a1];
		state_path_a_end_cost[a2][final_nzc_path_a[a2]]=state_path_a_end_cost[a1][final_nzc_path_a[a1]];

		memcpy(state_path_b[b2], state_path_b[b1],wm_pos[kk]*sizeof(statenode));
		final_nzc_path_b[b2]=final_nzc_path_b[b1];
		state_path_b_end_cost[b2][final_nzc_path_b[b2]]=state_path_b_end_cost[b1][final_nzc_path_b[b1]];

		i=wm_pos[kk];
        for(size=1; size<11; size++)
		{
		   tmp_min=maxnumber;  		   tmp_min_2=maxnumber;             t1=0; t2=0;
		   if(block_b_tree[b2].wm_nozero_no>=0)
		   {
		     k=(i-wm_pos[block_b_tree[b2].wm_nozero_no]>15)?15:(i-wm_pos[block_b_tree[b2].wm_nozero_no]-1);
			 for(j1=block_b_tree[b2].wm_nozero_no+1;j1<kk;j1++)
			 {	
				 if((wm_pos[j1]-wm_pos[block_b_tree[b2].wm_nozero_no])<=15)
				 {
					 wm_nocost_pos[t1]=wm_pos[j1]; 				  t1++;  				  t2=t1;
				 }
				 else 
				 { 
				  for(k1=0;k1<t2;k1++)
				     if(wm_pos[j1]-wm_nocost_pos[k1]==16)
						wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			 }
		   }
           else	  
		   {
			  k=(i>15)?15:(i-1);  // first 15 states do not have full incoming states
                // for each incoming state j (j is from 0 to maximum incoming states)
		      for(j1=0;j1<kk;j1++)
			  {	
				if(wm_pos[j1]<=15)
				{ 
				  wm_nocost_pos[t1]=wm_pos[j1];  	  t1++;   			  t2=t1;
				}
				else 
				{ 
				  for(k1=0;k1<t2;k1++)
				    if(wm_pos[j1]-wm_nocost_pos[k1]==16)
						wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				 }
			  }
			}
	          
	        for(j=0; j<=k; j++)
			{
			  thr=0; 
			  for(m=0;m<t2;m++)
			  {
				if(j==(i-wm_nocost_pos[m]-1))
				{
				  thr=1;
				  break;
				}
			  }
			  if(thr==0)
			  {
		         cost_2=state_path_b[b2][i-j-1].min_cost+dist_2[i][j]+ent_ac[(j<<4)+size];
		         if(cost_2<tmp_min_2)
				 {
			       tmp_min_2=cost_2;          run_2[size]=j;
				 }
			  }
			}//end of j

		 t1=0;t2=0;
         if(block_a_tree[a2].wm_nozero_no>=0)
		 {
		 	k=(i-wm_pos[block_a_tree[a2].wm_nozero_no]>15)?15:(i-wm_pos[block_a_tree[a2].wm_nozero_no]-1);
			for(j1=block_a_tree[a2].wm_nozero_no+1;j1<kk;j1++)
			{	
				if((wm_pos[j1]-wm_pos[block_a_tree[a2].wm_nozero_no])<=15)
				{
					wm_nocost_pos[t1]=wm_pos[j1];    t1++;    t2=t1;
				}
		        else 
				{ 
				  for(k1=0;k1<t2;k1++)
				     if(wm_pos[j1]-wm_nocost_pos[k1]==16)
						wm_nocost_pos[t2]=wm_pos[j1];
				  t2++;
				}
			}
		 }
         else	  
		 {
		  k=(i>15)?15:(i-1);  // first 15 states do not have full incoming states
          // for each incoming state j (j is from 0 to maximum incoming states)
		  for(j1=0;j1<kk;j1++)
		  {	
			if(wm_pos[j1]<=15)
			{
				wm_nocost_pos[t1]=wm_pos[j1]; 	t1++;  	t2=t1;
			}
			else 
			{ 
			    for(k1=0;k1<t2;k1++)
			      if(wm_pos[j1]-wm_nocost_pos[k1]==16)
						wm_nocost_pos[t2]=wm_pos[j1];
			    t2++;
			}
		  }
		}
	           
	    for(j=0; j<=k; j++)
		{
			  thr=0;
			  for(m=0;m<t2;m++)
			  {
				if(j==(i-wm_nocost_pos[m]-1))
				{
				  thr=1;
				  break;
				}
			  }
             
			  if(thr==0)
			  {
		       cost=state_path_a[a2][i-j-1].min_cost+dist[i][j]+ent_ac[(j<<4)+size];
		       if (cost<tmp_min)
			   {
			    tmp_min=cost; 			    run_1[size]=j;
			   }
			  }
		 }//end of j
		 part_cost_1[size]=tmp_min;  	 part_cost_2[size]=tmp_min_2;
	  } //end od size

	 int ind1_temp,ind2_temp;
	 ind1_temp=quantize1c(dctcoef_1b[i],i);   	 ind2_temp=quantize1c(dctcoef_2b[i],i);
     if(ind1_temp>=ind2_temp)
	 {
		 ind1=ind1_temp;  		 ind2=ind2_temp;
	 }
	 else
     {
		 ind1=-ind1_temp;  		 ind2=-ind2_temp;
	 }

	 totalwmcost=maxnumber;
	 for(size=1;size<11;size++) //siz
	  {
	     for(size2=1;size2<size;size2++)
		 {
          if((s_max[size2]+s_max[size])*qtbl_1d[i]>=(Q[i]+rdt))
		  {
			if((s_min[size]-s_max[size2])*qtbl_1d[i]>=(Q[i]+rdt))//2
			{
			   if (-s_min[size]<=ind1)   				 id[i][size]=-s_min[size];  
			   else if(-s_max[size]>=ind1)   			 id[i][size]=-s_max[size];
			   else                          			 id[i][size]=ind1;
					
   	           if(ind2>=0)
			   {
		        if (s_min[size2]>=ind2)      	         id_2[i][size2]=s_min[size2];
		        else if(s_max[size2]<=ind2)  	         id_2[i][size2]=s_max[size2];
		        else                    			     id_2[i][size2]=ind2;
			   }
		       else
			   {
		        if (-s_min[size2]<=ind2)     	         id_2[i][size2]=-s_min[size2];
		        else if(-s_max[size2]>=ind2)             id_2[i][size2]=-s_max[size2];
		        else                    			     id_2[i][size2]=ind2;
			   }
               
			   if(ind1_temp>=ind2_temp)
			   {
		          d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
		          d_2[i][size2]=sqr(double(dctcoef_2b[i]-id_2[i][size2]*qtbl_1d[i]));
			   }
			   else
			   {
                  d[i][size]=sqr(double(dctcoef_1b[i]+id[i][size]*qtbl_1d[i]));
		          d_2[i][size2]=sqr(double(dctcoef_2b[i]+id_2[i][size2]*qtbl_1d[i]));
			   }
			}
			else //2
			{ 
			  tmp_cost=maxnumber;
			  if((s_max[size]-s_min[size2])*qtbl_1d[i]>=(Q[i]+rdt))//3
			  {
			      if (-s_min[size]<=ind1)    				   x=-s_min[size];
				  else if(-s_max[size]>=ind1) 				   x=-s_max[size];
			      else                      				   x=ind1;
					
   	              if (-s_min[size2]<=ind2)   		           y=-s_min[size2];
		          else if(-s_max[size2]>=ind2) 		           y=-s_max[size2];
		          else                      			       y=ind2;

				  if((y-x)*qtbl_1d[i]<(Q[i]+rdt))
				  {
					 xl=-s_max[size];     					 xr=-s_min[size];
					 if((xl+Ind_Threshold)<-s_max[size2])    xl=-s_max[size2]-Ind_Threshold;
					 if((xr+Ind_Threshold)>-s_min[size2])    xr=-s_min[size2]-Ind_Threshold;

					 x_tmp=ind1+ind2-Ind_Threshold;   		 x_tmp=(x_tmp>0)?(x_tmp+1)/2:(-(-x_tmp-1)/2);
					 if(x_tmp>xr)       id[i][size]=xr;
					 else if (x_tmp<xl) id[i][size]=xl;
					 else               id[i][size]=x_tmp;

					 id_2[i][size2]=id[i][size]+Ind_Threshold;
				  }
     			  else
				  {
					  id[i][size]=x;      			  id_2[i][size2]=y;
				   }
		
				  if(ind1_temp>=ind2_temp)
				  {
		           d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
		           d_2[i][size2]=sqr(double(dctcoef_2b[i]-id_2[i][size2]*qtbl_1d[i]));
				  }
			      else
				  {
                   d[i][size]=sqr(double(dctcoef_1b[i]+id[i][size]*qtbl_1d[i]));
		           d_2[i][size2]=sqr(double(dctcoef_2b[i]+id_2[i][size2]*qtbl_1d[i]));
				  }
				
				  tmp_cost=d[i][size]+d_2[i][size2];
			  }//3

			      if (-s_min[size]<=ind1)   				   x=-s_min[size];
				  else if(-s_max[size]>=ind1)   			   x=-s_max[size];
			      else                          			   x=ind1;
					
   	              if (s_min[size2]>=ind2)   		           y=s_min[size2];
		          else if(s_max[size2]<=ind2)		           y=s_max[size2];
		          else                      			       y=ind2;

				  if((y-x)*qtbl_1d[i]<(Q[i]+rdt))
				  {
					  xl=-s_max[size];      				   xr=-s_min[size];
					  if((xl+Ind_Threshold)<s_min[size2])      xl=s_min[size2]-Ind_Threshold;
					  if((xr+Ind_Threshold)>s_max[size2])      xr=s_max[size2]-Ind_Threshold;

					  x_tmp=ind1+ind2-Ind_Threshold;           x_tmp=(x_tmp>0)?(x_tmp+1)/2:(-(-x_tmp-1)/2);
					  if(x_tmp>xr)       x=xr;
					  else if (x_tmp<xl) x=xl;
					  else               x=x_tmp;
					  y=x+Ind_Threshold;
				  }

				  if(ind1_temp>=ind2_temp)
				  {
				  
				    if(sqr(double(dctcoef_1b[i]-x*qtbl_1d[i]))+sqr(double(dctcoef_2b[i]-y*qtbl_1d[i])<tmp_cost))
					{
					  id[i][size]=x;     					  id_2[i][size2]=y;
  				      d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
		              d_2[i][size2]=sqr(double(dctcoef_2b[i]-id_2[i][size2]*qtbl_1d[i]));
					}
				  }
				  else
				  {
				   if(sqr(double(dctcoef_1b[i]+x*qtbl_1d[i]))+sqr(double(dctcoef_2b[i]+y*qtbl_1d[i])<tmp_cost))
					{
					  id[i][size]=x;                   id_2[i][size2]=y;
				      d[i][size]=sqr(double(dctcoef_1b[i]+id[i][size]*qtbl_1d[i]));
		              d_2[i][size2]=sqr(double(dctcoef_2b[i]+id_2[i][size2]*qtbl_1d[i]));
					}
				  }

			}//2
		 	    
		   cost=part_cost_1[size]+d[i][size];     	   cost_2=part_cost_2[size]+d_2[i][size2];
		   dist_inc=dist[i][j]+d[i][size];       	   dist_inc_2=dist_2[i][j]+d_2[i][size2];

		   if((cost+cost_2)<totalwmcost)
		   {
			 totalwmcost=cost+cost_2;
			 if(ind1_temp>=ind2_temp)
			 {
			   record_inf(state_path_a[a2],i,run_1[size],size,   id[i][size],   dist_inc,   cost);
			   record_inf(state_path_b[b2],i,run_2[size2],size2, id_2[i][size2], dist_inc_2, cost_2);
			 }
			 else
			 { 
			   record_inf(state_path_a[a2],i,run_1[size],size,   -id[i][size],   dist_inc,   cost);
			   record_inf(state_path_b[b2],i,run_2[size2],size2, -id_2[i][size2], dist_inc_2, cost_2);
			 }
		   }

		}//1
	  }//end size2

       //size=size2
       if((s_max[size]+s_max[size])*qtbl_1d[i]>=(Q[i]+rdt))//1
	   {			
			 tmp_cost=maxnumber;
			 if((s_max[size]-s_min[size])*qtbl_1d[i]>=(Q[i]+rdt))//2
			  {
			   if(ind2>-ind1)//3
				{
				  if (s_min[size]>=ind1)  				   x=s_min[size];
				  else if(s_max[size]<=ind1)  			   x=s_max[size]; 
			      else                  				   x=ind1;
					
   	              if (s_min[size]>=ind2) 		           y=s_min[size];
		          else if(s_max[size]<=ind2)	           y=s_max[size];
		          else                      		       y=ind2;
					
				  if((y-x)*qtbl_1d[i]<(Q[i]+rdt))
				  {
					  xl=s_min[size];       			   xr=s_max[size]-Ind_Threshold;
					  x_tmp=ind1+ind2-Ind_Threshold;
					  x_tmp=(x_tmp>0)?(x_tmp+1)/2:(-(-x_tmp-1)/2);

					  if(x_tmp>xr)        id[i][size]=xr;
					  else if (x_tmp<xl)  id[i][size]=xl;
					  else                id[i][size]=x_tmp;

					  id_2[i][size]=id[i][size]+Ind_Threshold;
				  }
				}
				else//3
				{
				   if (-s_min[size]<=ind1)   				 x=-s_min[size];
				   else if(-s_max[size]>=ind1) 				 x=-s_max[size];
			       else                     				 x=ind1;
					
   	               if (-s_min[size]<=ind2)  		         y=-s_min[size];
		           else if(-s_max[size]>=ind2)		         y=-s_max[size];
		           else                     			     y=ind2;
					
				    if((y-x)*qtbl_1d[i]<(Q[i]+rdt))
					{
					  xl=-s_max[size];       		  xr=-s_min[size]-Ind_Threshold;

					  x_tmp=ind1+ind2-Ind_Threshold;  x_tmp=(x_tmp>0)?(x_tmp+1)/2:(-(-x_tmp-1)/2);

					  if(x_tmp>xr)        id[i][size]=xr;
					  else if (x_tmp<xl)  id[i][size]=xl;
					  else                id[i][size]=x_tmp;

					  id_2[i][size]=id[i][size]+Ind_Threshold;
					}
				}//3
                  
				if(ind1_temp>=ind2_temp)
				{
				  d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
		          d_2[i][size]=sqr(double(dctcoef_2b[i]-id_2[i][size]*qtbl_1d[i]));
				}
				else
				{ 
				  d[i][size]=sqr(double(dctcoef_1b[i]+id[i][size]*qtbl_1d[i]));
		          d_2[i][size]=sqr(double(dctcoef_2b[i]+id_2[i][size]*qtbl_1d[i]));
				}
				  tmp_cost=d[i][size]+d_2[i][size];
			  }//2

     			  if (-s_min[size]<=ind1)   				    x=-s_min[size];
				  else if(-s_max[size]>=ind1) 				    x=-s_max[size];
			      else                      				    x=ind1;
					
   	              if (s_min[size]>=ind2)     		            y=s_min[size];
		          else if(s_max[size]<=ind2) 		            y=s_max[size];
		          else                       			        y=ind2;
					 
				  if((y-x)*qtbl_1d[i]<(Q[i]+rdt))
				  {
					  xl=-s_max[size];      					xr=-s_min[size];
					  if((xl+Ind_Threshold)<s_min[size])  		xl=s_min[size2]-Ind_Threshold;
					  if((xr+Ind_Threshold)>s_max[size])   		xr=s_max[size]-Ind_Threshold;

					  x_tmp=ind1+ind2-Ind_Threshold;
					  x_tmp=(x_tmp>0)?(x_tmp+1)/2:(-(-x_tmp-1)/2);

					  if(x_tmp>xr)       x=xr;
					  else if (x_tmp<xl) x=xl;
					  else               x=x_tmp;

					  y=x+Ind_Threshold;
				  }

				  if(ind1_temp>=ind2_temp)
				  {
				    if(sqr(double(dctcoef_1b[i]-x*qtbl_1d[i]))+sqr(double(dctcoef_2b[i]-y*qtbl_1d[i]))<tmp_cost)
					{
					 id[i][size]=x;   				 id_2[i][size]=y;
				     d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
		             d_2[i][size]=sqr(double(dctcoef_2b[i]-id_2[i][size]*qtbl_1d[i]));
					}
				  }
				  else
				  {
				    if(sqr(double(dctcoef_1b[i]+x*qtbl_1d[i]))+sqr(double(dctcoef_2b[i]+y*qtbl_1d[i]))<tmp_cost)
					{
					 id[i][size]=x;    				 id_2[i][size]=y;
				     d[i][size]=sqr(double(dctcoef_1b[i]+id[i][size]*qtbl_1d[i]));
		             d_2[i][size]=sqr(double(dctcoef_2b[i]+id_2[i][size]*qtbl_1d[i]));
					}
				  }
				
		   cost=part_cost_1[size]+d[i][size];  		   cost_2=part_cost_2[size]+d_2[i][size];
		   dist_inc=dist[i][j]+d[i][size];             dist_inc_2=dist_2[i][j]+d_2[i][size];

		   if((cost+cost_2)<totalwmcost)
		   {
			 totalwmcost=cost+cost_2;
			 if(ind1_temp>=ind2_temp)
			 {
			    record_inf(state_path_a[a2],i,run_1[size],size, id[i][size],   dist_inc,   cost);
			    record_inf(state_path_b[b2],i,run_2[size],size, id_2[i][size], dist_inc_2, cost_2);
			 }
			 else
			 {
			    record_inf(state_path_a[a2],i,run_1[size],size, -id[i][size],   dist_inc,   cost);
			    record_inf(state_path_b[b2],i,run_2[size],size, -id_2[i][size], dist_inc_2, cost_2);
			 }
			 
		   }
         }//1
	
         for(size2=size+1;size2<11;size2++)
		 {
   		   if((s_max[size2]+s_max[size])*qtbl_1d[i]>=(Q[i]+rdt))//1
		   {
			if((s_min[size2]-s_max[size])*qtbl_1d[i]>=(Q[i]+rdt))//2
			{
			   if (s_min[size2]>=ind2)   			 id_2[i][size2]=s_min[size2];
			   else if(s_max[size2]<=ind2)  		 id_2[i][size2]=s_max[size2];
			   else                 				 id_2[i][size]=ind2;
					
   	           if(ind1>=0)
			   {
		        if (s_min[size]>=ind1)    	         id[i][size]=s_min[size];
		        else if(s_max[size]<=ind1) 	         id[i][size]=s_max[size];
		        else                			     id[i][size]=ind1;
			   }
		       else
			   {
		        if (-s_min[size]<=ind1) 	         id[i][size]=-s_min[size];
		        else if(-s_max[size]>=ind1)	         id[i][size]=-s_max[size];
		        else                 			     id[i][size]=ind1;
			   }
             
			  if(ind1_temp>=ind2_temp)
			  {
		        d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
		        d_2[i][size2]=sqr(double(dctcoef_2b[i]-id_2[i][size2]*qtbl_1d[i]));
			  }
			  else
			  {
		        d[i][size]=sqr(double(dctcoef_1b[i]+id[i][size]*qtbl_1d[i]));
		        d_2[i][size2]=sqr(double(dctcoef_2b[i]+id_2[i][size2]*qtbl_1d[i]));
			  }
			  
			}//2
			else 
			{ 
			  tmp_cost=maxnumber;
			  if((s_max[size2]-s_min[size])*qtbl_1d[i]>=(Q[i]+rdt))//3
			  {
			      if (s_min[size]>=ind1)   				   x=s_min[size];
				  else if(s_max[size]<=ind1)			   x=s_max[size];
			      else                  				   x=ind1;
					
   	              if (s_min[size2]>=ind2)   	           y=s_min[size2];
		          else if(s_max[size2]<=ind2) 	           y=s_max[size2];
		          else                      		       y=ind2;

				  if((y-x)*qtbl_1d[i]<(Q[i]+rdt))
				  {
					  xl=s_min[size];   				    xr=s_max[size];
   					  if((xl+Ind_Threshold)<s_min[size2])   xl=s_min[size2]-Ind_Threshold;
					  if((xr+Ind_Threshold)>s_max[size2])  	xr=s_max[size2]-Ind_Threshold;

					  x_tmp=ind1+ind2-Ind_Threshold;  	    x_tmp=(x_tmp>0)?(x_tmp+1)/2:(-(-x_tmp-1)/2);

					  if(x_tmp>xr)       id[i][size]=xr;
					  else if (x_tmp<xl) id[i][size]=xl;
					  else               id[i][size]=x_tmp;
					  id_2[i][size2]=id[i][size]+Ind_Threshold;
				  }
				   else
				   {
					  id[i][size]=x;    				  id_2[i][size2]=y;
				   }
				  
				  if(ind1_temp>=ind2_temp)
				  {
  				    d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
		            d_2[i][size2]=sqr(double(dctcoef_2b[i]-id_2[i][size2]*qtbl_1d[i]));
				  }
				  else
				  {
  				    d[i][size]=sqr(double(dctcoef_1b[i]+id[i][size]*qtbl_1d[i]));
		            d_2[i][size2]=sqr(double(dctcoef_2b[i]+id_2[i][size2]*qtbl_1d[i]));
				  }
				
				  tmp_cost=d[i][size]+d_2[i][size2];
			  }//3

			      if (-s_min[size]<=ind1)   		   x=-s_min[size];
				  else if(-s_max[size]>=ind1)    	   x=-s_max[size];
			      else               				   x=ind1;
					
   	              if (s_min[size2]>=ind2)              y=s_min[size2];
		          else if(s_max[size2]<=ind2)          y=s_max[size2];
		          else              			       y=ind2;

				  if((y-x)*qtbl_1d[i]<(Q[i]+rdt))
				  {
					  xl=-s_max[size];  					xr=-s_min[size];
					  if((xl+Ind_Threshold)<s_min[size2])   xl=s_min[size2]-Ind_Threshold;
					  if((xr+Ind_Threshold)>s_max[size2])   xr=s_max[size2]-Ind_Threshold;

					  x_tmp=ind1+ind2-Ind_Threshold;
					  x_tmp=(x_tmp>0)?(x_tmp+1)/2:(-(-x_tmp-1)/2);

					  if(x_tmp>xr)         x=xr;
					  else if (x_tmp<xl)   x=xl;
					  else                 x=x_tmp;

					  y=x+Ind_Threshold;
				  }

				  if(ind1_temp>=ind1_temp)
				  {
				   if(sqr(double(dctcoef_1b[i]-x*qtbl_1d[i]))+sqr(double(dctcoef_2b[i]-y*qtbl_1d[i])<tmp_cost))
				   {
					id[i][size]=x;      			id_2[i][size2]=y;
				    d[i][size]=sqr(double(dctcoef_1b[i]-id[i][size]*qtbl_1d[i]));
		            d_2[i][size2]=sqr(double(dctcoef_2b[i]-id_2[i][size2]*qtbl_1d[i]));
				   }
				  }
				  else
				  {
				   if(sqr(double(dctcoef_1b[i]+x*qtbl_1d[i]))+sqr(double(dctcoef_2b[i]+y*qtbl_1d[i])<tmp_cost))
				   {
					id[i][size]=x;             		id_2[i][size2]=y;
				    d[i][size]=sqr(double(dctcoef_1b[i]+id[i][size]*qtbl_1d[i]));
		            d_2[i][size2]=sqr(double(dctcoef_2b[i]+id_2[i][size2]*qtbl_1d[i]));
				   }
				  }
				}//2
		 		   
		   cost=part_cost_1[size]+d[i][size];     	   cost_2=part_cost_2[size]+d_2[i][size2];
		   dist_inc=dist[i][j]+d[i][size];    		   dist_inc_2=dist_2[i][j]+d_2[i][size2];

		   if((cost+cost_2)<totalwmcost)
		   {
			 totalwmcost=cost+cost_2;
             if(ind1_temp>=ind1_temp)
			 {
			   record_inf(state_path_a[a2],i,run_1[size],size, id[i][size],   dist_inc,   cost);
			   record_inf(state_path_b[b2],i,run_2[size2],size2, id_2[i][size2], dist_inc_2, cost_2);
			 }
			 else
			 {
			   record_inf(state_path_a[a2],i,run_1[size],size, -id[i][size],   dist_inc,   cost);
			   record_inf(state_path_b[b2],i,run_2[size2],size2, -id_2[i][size2], dist_inc_2, cost_2);
			 }
		   }
		}//1
	  }//end size2
	 }//end size

    if(i<63)
	 {
	       state_path_a_end_cost[a2][i]=state_path_a[a2][i].min_cost+eob_cost[i];
	       final_nzc_path_a[a2]=i;
           state_path_b_end_cost[b2][i]=state_path_b[b2][i].min_cost+eob_cost_2[i];
	       final_nzc_path_b[b2]=i; 
	  }
		  block_b_tree[b2].cost_inwm_status=1;  		  block_a_tree[a2].cost_inwm_status=1;
      	 
	 if(state_path_b[b2][i].min_cost+state_path_a[a2][i].min_cost<tempcost)
	 {
			tempcost=state_path_b[b2][i].min_cost+state_path_a[a2][i].min_cost;
			path_a_no=a2;  			path_b_no=b2;
	 }
	}//end of jj
   }//end of ttt
			 
	node[kk][3][0].block_a_graph_no = path_a_no;  	node[kk][3][0].block_b_graph_no = path_b_no; 
	a2= path_a_no;  	b2= path_b_no;
	block_b_tree[b2].wm_nozero_no=kk;           	block_a_tree[a2].wm_nozero_no=kk;
	
    if(block_b_tree[b2].cost_status_2==0)
	 {  
	    for(i=wm_pos[kk]+1;i<end_right;i++)
		{ 
		  curr_min_2=maxnumber;
		  k=(i-wm_pos[block_b_tree[b2].wm_nozero_no]>15)?15:(i-wm_pos[block_b_tree[b2].wm_nozero_no]-1);  
	      for(j=0; j<=k; j++)
		  {
		    switch (indsi_2[i])
			{
             case 0:
	          for(size=1; size<3; size++)  update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
             break;
             case 1:
	          for(size=1; size<4; size++)  update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
             break;
             case 10:
              for (size=10; size>8; size--) update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
             break;
	         default: //2~9 
             for (size=indsi_2[i]-1; size<indsi_2[i]+2; size++)
	           update_cost_2(i,j,size,dist_2[i][j],d_2[i][size],id_2[i][size],state_path_b[b2]);
			} // end of switch
           }//end of j loop
	
         // for each state, find the cost of going EOB after this nonzero state
         if (i<63)
		 {
			 state_path_b_end_cost[b2][i]=state_path_b[b2][i].min_cost+eob_cost_2[i];
			 if (state_path_b_end_cost[b2][i]<state_path_b_end_cost[b2][final_nzc_path_b[b2]])
			 final_nzc_path_b[b2]=i;
		 } 
          // consider (15,0) case for i>=16 (consider this AFTER ending-cost calculation!)
         if ((i-wm_pos[block_b_tree[b2].wm_nozero_no]>15)&&(i<63)&& (final_nzc_path_b[b2]!=i))
		  			  update_cost_2(i,15,0,dist_2[i][15], sqr(c_abs_2[i]),0,state_path_b[b2]);
		  
		 if (curr_min_2<0) 	      printf("row_b=%d, col_b=%d, i=%d\n", row_b, col_b, i);
		} // end of i loop for the calculation of the minimum cost for one state   
	    block_b_tree[b2].cost_status_2=1;
	}//end if block_a_tree[b2].cost_status_2==0
		  
    if(block_a_tree[a2].cost_status_2==0)
	{
	  
	  for(i=wm_pos[kk]+1;i<end_right;i++)
	  { 
         curr_min=maxnumber;
	     k=(i-wm_pos[block_a_tree[a2].wm_nozero_no]>15)?15:(i-wm_pos[block_a_tree[a2].wm_nozero_no]-1);
	     for(j=0; j<=k; j++)
		 {
		    switch (indsi[i])
			{
	          case 0:
		      for(size=1; size<3; size++)  update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
              break;
              case 1:
		      for(size=1; size<4; size++)  update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
              break;
	          case 10:
              for (size=10; size>8; size--) update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
              break;
		      default: //2~9 
              for (size=indsi[i]-1; size<indsi[i]+2; size++)
		             update_cost(i,j,size,dist[i][j],d[i][size],id[i][size],state_path_a[a2]);
			} // end of switch
		 }//end of j loop
	
	     // for each state, find the cost of going EOB after this nonzero state
	     if (i<63)
		 {
			state_path_a_end_cost[a2][i]=state_path_a[a2][i].min_cost+eob_cost[i];
			if (state_path_a_end_cost[a2][i]<state_path_a_end_cost[a2][final_nzc_path_a[a2]])
			final_nzc_path_a[a2]=i;
		} 
         // consider (15,0) case for i>=16 (consider this AFTER ending-cost calculation!)
         if ((i-wm_pos[block_a_tree[a2].wm_nozero_no]>15)&&(i<63)&&(final_nzc_path_a[a2]!=i))
		    update_cost(i,15,0,dist[i][15],sqr(c_abs[i]),0,state_path_a[a2]);
		 
		 if (curr_min_2<0) printf("row_b=%d, col_b=%d, i=%d\n", row_b, col_b, i);
		} // end of i loop for the calculation of the minimum cost for one state   
			block_a_tree[a2].cost_status_2=1;
	}  //end of  if block_b_tree[a2].cost_status_2
  }	 //end of else
 }//end of for  

   totalcost=maxnumber;
   for(ttt=0;ttt<4;ttt++)
     for(jj=0;jj<num_comb[wm_len-1][ttt];jj++)
	 {
	    a2=node[wm_len-1][ttt][jj].block_a_graph_no;    b2=node[wm_len-1][ttt][jj].block_b_graph_no; 
          
		if(state_path_a_end_cost[a2][final_nzc_path_a[a2]]<state_path_a[a2][63].min_cost)
		   a0_cost=state_path_a_end_cost[a2][final_nzc_path_a[a2]];
		else
		   a0_cost=state_path_a[a2][63].min_cost;
		
		if(state_path_b_end_cost[b2][final_nzc_path_b[b2]]<state_path_b[b2][63].min_cost)
		   b0_cost=state_path_b_end_cost[b2][final_nzc_path_b[b2]];
		else
		   b0_cost=state_path_b[b2][63].min_cost;

		if(a0_cost+b0_cost<totalcost)
		 {
			   nd=ttt;  			   sno=jj;        totalcost=a0_cost+b0_cost;
		}
	 }

    a2=node[wm_len-1][nd][sno].block_a_graph_no;   	b2=node[wm_len-1][nd][sno].block_b_graph_no; 
	if(state_path_a_end_cost[a2][final_nzc_path_a[a2]]<state_path_a[a2][63].min_cost)
	{ 
		a0_cost=state_path_a_end_cost[a2][final_nzc_path_a[a2]];
		sp_a=final_nzc_path_a[a2];
	}
	else
	{
	    a0_cost=state_path_a[a2][63].min_cost;   		sp_a=63;
	}

	if(state_path_b_end_cost[b2][final_nzc_path_b[b2]]<state_path_b[b2][63].min_cost)
	{
	    b0_cost=state_path_b_end_cost[b2][final_nzc_path_b[b2]];
	    sp_b=final_nzc_path_b[b2];
	}
	else
	{
	    b0_cost=state_path_b[b2][63].min_cost;     	    sp_b=63;
	}
		
	sp=0;   	stack[sp]=sp_a;
	if(sp_a==63)
	{   
       *distortion_t=*distortion_t+state_path_a[a2][63].dist_cum;
       *rate_total=*rate_total+state_path_a[a2][63].rate_cum;
	   *cost_t=*cost_t+state_path_a[a2][63].min_cost;
	 }
    else
	{
       *distortion_t=*distortion_t+state_path_a[a2][sp_a].dist_cum+state_path_a_end_cost[a2][sp_a]-state_path_a[a2][sp_a].min_cost-ent_ac[0];
	   *rate_total=*rate_total+state_path_a[a2][sp_a].rate_cum+ent_ac[0];
	   *cost_t=*cost_t+state_path_a_end_cost[a2][sp_a];
	   counts[0]++; // number of EOB increments!
		//printf("counts[0]=%d\n",counts[0]);
	   *total=*total+1;
	 }

     while (stack[sp]!=0)
	 {
	    // count the new (run, size) pair
		counts[(state_path_a[a2][stack[sp]].r<<4)+state_path_a[a2][stack[sp]].s]++;
		*total=*total+1;
		sp=sp+1;
		stack[sp]=stack[sp-1]-state_path_a[a2][stack[sp-1]].r-1;
		if (stack[sp]<0)
		  {
			printf("invalid case: not start from DC coef.!\n");
            break;
		  }
	 }

	 if (stack[sp]!=0)  	   printf("Wrong path!\n");
	 *pointer=sp;
	
	 //restore the optimization image indices based on the run-size pair.
     restore_blk(row_a, col_a, state_path_a[a2], stack, sp);

	 sp=0;     stack[sp]=sp_b;
	 if(sp_b==63)
	 {   
		 *distortion_t=*distortion_t+state_path_b[b2][63].dist_cum;
		 *rate_total=*rate_total+state_path_b[b2][63].rate_cum;
		 *cost_t=*cost_t+state_path_b[b2][63].min_cost;
	 }
	 else
	 {
         *distortion_t=*distortion_t+state_path_b[b2][sp_b].dist_cum+state_path_b_end_cost[b2][sp_b]-state_path_b[b2][sp_b].min_cost-ent_ac[0];
		 *rate_total=*rate_total+state_path_b[b2][sp_b].rate_cum+ent_ac[0];
		 *cost_t=*cost_t+state_path_b_end_cost[b2][sp_b];
		 counts[0]++; // number of EOB increments!
		//printf("counts[0]=%d\n",counts[0]);
		 *total=*total+1;
	 }

     while (stack[sp]!=0)
	 {
	    // count the new (run, size) pair
		counts[(state_path_b[b2][stack[sp]].r<<4)+state_path_b[b2][stack[sp]].s]++;
		*total=*total+1;
		sp=sp+1;
		stack[sp]=stack[sp-1]-state_path_b[b2][stack[sp-1]].r-1;
		if (stack[sp]<0)
		  {
			printf("invalid case: not start from DC coef.!\n");
            break;
		  }
	 }

	 if (stack[sp]!=0)
	  printf("Wrong path!\n");
	  *pointer=sp;
	
	 //restore the optimization image indices based on the run-size pair.
     restore_blk(row_b, col_b, state_path_b[b2], stack, sp);
	 for(i=0;i<wm_len;i++)
	 {
	    if(abs(state_path_b[b2][wm_pos[i]].index-state_path_a[a2][wm_pos[i]].index)!=0)
		{
	      tmp_threshold=(int)ceil((double)(Q[wm_pos[i]]+rdt)/abs(state_path_b[b2][wm_pos[i]].index-state_path_a[a2][wm_pos[i]].index));
		  if(tmp_threshold>qtbl_1d_thrld[wm_pos[i]])
	         qtbl_1d_thrld[wm_pos[i]]=tmp_threshold;
		} 
	 }

	 delete state_a0,state_b0;
	 for(i=0;i<wm_len;i++)
    	for(j=0;j<4;j++)
	      delete node[i][j];
	 for(i=0;i<wm_len;i++) delete node[i]; delete node;
	 for(i=0;i<wm_len;i++) delete num_comb[i]; delete num_comb;

	 for(i=0;i<tr_nod_no;i++)
	 {
       delete state_path_a[i]; delete state_path_b[i]; delete state_path_a_end_cost[i]; delete state_path_b_end_cost[i];
	 }

	 delete state_path_a;      delete state_path_b;      delete state_path_a_end_cost;  delete state_path_b_end_cost;
	 delete final_nzc_path_a;  delete final_nzc_path_b;  delete tmp_cost_1; 
     delete path_a_no_1;       delete path_b_no_1;       delete wm_nocost_pos;  
	 delete part_cost_1;       delete part_cost_2; 
}

		


	  
