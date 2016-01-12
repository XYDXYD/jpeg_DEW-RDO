#include "jhuff.hpp"
#include "sditojpeg.h"
#include <math.h>

#define  sqterm(a,b) sqr(((double)(a))-((double)(b)))
#define  pi 4*atan(1.0)

/* gloabl variables */
extern long huff_put_buffer;  /* buffer for accumulating the current bits */
extern int  huff_put_bits;    /* current number of bits in the buffer     */
extern HUFF_TBL *dctbl_0, *actbl_0; 
extern unsigned char dc_bits_0[17], dc_val_0[12], ac_bits_0[33], ac_val_0[256];
extern void append_bits(unsigned int code, int size);
extern void encode_one_block(int ci, int *zz);
extern void outputheader(myjpeg_compress_struct *dstinfo);
extern void finishjpegstream();
extern void GX_DCT_Weight_dct_8x8(int datain[8][8], int GX_DCT_1dout[8][8]);
extern void opti_two_block();
extern void update_qtbl();
extern void jchuff_tbl(HUFF_TBL *htbl);
//extern void block_encode(int *zz, HUFF_TBL *dctbl, HUFF_TBL *actbl);
extern void fake_blockencode(int *zz, int *counts, int *totalpair, int *dccounts);
extern int  customized_table(int *freq, unsigned char *returnbits, unsigned char *val);
extern void opti_block(int row_b,  int col_b,   int *dctcoef_1b, statenode *state, int *stack, int *pointer,
	int *counts, int *total, double *distortion_t, double *rate_total, double *cost_t, bool block_type/*0代表置零块*/, int c);


//global variable for AC optimization
FILE *stream;
int recon_index[ROWS][COLS],ori_qtbl[8][8],qtbl_1d[64],Q[64],qtbl_1d_thrld[64],adct[ROWS][COLS];
int pairnum, pairnum_0;
double ent_dc[12];         // entropy of DC size group
double ac_r[256];    
double ent_ac[256];        // entropy of each (r,s) pair
int s_min[11]={0,1,2,4,8,16,32,64,128,256,512};   // minimum index for each size category
int s_max[11]={0,1,3,7,15,31,63,127,255,511,1024};// maximum index for each size category
double sigmasquare[64][64];
int CC=3; 

short int zigzag[8][8]={  0, 1, 5, 6,14,15,27,28,
	2, 4, 7,13,16,26,29,42,
	3, 8,12,17,25,30,41,43,
	9,11,18,24,31,40,44,53,
	10,19,23,32,39,45,52,54,
	20,22,33,38,46,51,55,60,
	21,34,37,47,50,56,59,61,
	35,36,48,49,57,58,62,63};
/* quantization table provided by ISO/ITC */
int qtbl_d[8][8]={   
	16, 11, 10, 16, 24, 40, 51, 61,
	12, 12, 14, 19, 26, 58, 60, 55,
	14, 13, 16, 24, 40, 57, 69, 56,
	14, 17, 22, 29, 51, 87, 80, 62,
	18, 22, 37, 56, 68,109,103, 77,
	24, 35, 55, 64, 81,104,113, 92,
	49, 64, 78, 87,103,121,120,101,
	72, 92, 95, 98,112,100,103, 99
};

void Order(int *p,int *q) {
	int temp;
	if(*p>*q) 
	{
		temp=*p;
		*p=*q;
		*q=temp;
	}
}

int min(int a, int b)
{
	return (a < b) ? a : b;
}

//Buuble sorting of integer array A[]
void Bubble(int *a,int n) {
	int i,j;

	for (i=0; i<n; i++)
		for (j=n-1; i<j; j--)
			Order(&a[j-1], &a[j]);

}


/* main function */
int main(int *argc, char **argv)
{
	register int i, j, k, u, v, temp2;
	int ac_counts[257], dc_counts[257];
	int inblock[8][8], inblock1[8][8], *zz_coef, *zz_ind, adct_1b[8][8];
	int last_dc_value = 0, tempdc;
	int begin, end, fix_part, ite_num;
	int *stack, point, total = 0;
	int *a, num_blk, wm_len, *wm_bit;
	int tr_nod_no = 0, base = 0;
	int tr,th,td,tb;
	int *zz;
	int aa[64][64], bb[64][64], x1, y1, x2, y2, tempint;
	double ad[8][8];
	int cc[64], x, y,n/*,cc1[64][64]存小块的cut*/;
	double Sc;

	unsigned char input[ROWS][COLS];
	double lamda2, scale, time, temp, temp1, scale2;
	double epslon = 0.1, previouscost, distortion, rate_tle, minimumcost;
	double c[8] = { 0.707,1.0,1.0,1.0,1.0,1.0,1.0,1.0 };

	bool block_type = 1;//表示当前块是否为置零块，0表示当前块置零
	int cut = 63;//表示截止频率

	statenode *state;
	FILE *infd;
	myjpeg_compress_struct Lena_jpeg_struct;

	//initilize for writing JPEG
	Lena_jpeg_struct.image_width = 512;
	Lena_jpeg_struct.image_height = 512;
	Lena_jpeg_struct.num_components = 1;
	Lena_jpeg_struct.max_h_samp_factor = 4;
	Lena_jpeg_struct.max_v_samp_factor = 4;
	Lena_jpeg_struct.adobe_tag = 0;
	Lena_jpeg_struct.quant_tbl_0 = (unsigned char *)malloc(64 * sizeof(unsigned char));
	Lena_jpeg_struct.comp_info[0].component_id = 1;
	Lena_jpeg_struct.comp_info[0].h_samp_factor = 1;
	Lena_jpeg_struct.comp_info[0].v_samp_factor = 1;
	Lena_jpeg_struct.comp_info[0].quant_tbl_no = 0;
	Lena_jpeg_struct.comp_info[0].width_in_blocks = 512 / 8;
	Lena_jpeg_struct.comp_info[0].height_in_blocks = 512 / 8;
	Lena_jpeg_struct.comp_info[0].MCU_width = 8;
	Lena_jpeg_struct.comp_info[0].MCU_height = 8;
	Lena_jpeg_struct.comp_info[0].last_col_width = 8;
	Lena_jpeg_struct.comp_info[0].last_row_height = 8;
	//end of initialize
	zz = (int *)malloc(64 * sizeof(int));
	for (k = 0; k < 64; k++)
	{
		cc[k] = 63;
	}
	/*random shuffle of block position*/
	for (i = 0;i < 64;i++)
	{
		for (j = 0;j < 64;j++)
		{
			aa[i][j] = i;
			bb[i][j] = j;
		}
	}
	// for(int oc=0; oc<17392;oc++)
	//  for(k=0;k<500;k++)
	srand(10000);
	for (int oc = 0; oc < 36813; oc++)   //277588; 936813
	{
		for (k = 0;k < 100;k++)
		{
			
			x1 = (int)(63 * rand()) / 32767;  	 y1 = (int)(63 * rand()) / 32767;

			x2 = (int)(63 * rand()) / 32767;      y2 = (int)(63 * rand()) / 32767;

			tempint = aa[x1][y1];
			aa[x1][y1] = aa[x2][y2];

			/* if(aa[x1][y1]<0)
			{		 k=k;
			}
			*/
			aa[x2][y2] = tempint;

			tempint = bb[x1][y1];
			bb[x1][y1] = bb[x2][y2];
			bb[x2][y2] = tempint;
		}//aa和bb矩阵中任意交换元素
	}
	/*random shuffle of block position*/

	begin = clock();
	// number of 8x8 blocks
	num_blk = (int)ROWS*COLS / 64;
	// get lamda, iteration number and scaling factor from the command line argument
	wm_len = atoi(argv[1]);//水印的长度
	lamda2 = atof(argv[2]);
	scale = atof(argv[3]);
	scale2 = atof(argv[4]);
	wm_bit = new (int[wm_len]);

	//a is used to represent wm bit
	a = (int *)malloc(num_blk*wm_len*sizeof(int));

	a[0] = 0; a[1] = 1;	a[2] = 0;	a[3] = 0;	a[4] = 0;	a[5] = 1;	a[6] = 1;
	for (i = 7;i < num_blk*wm_len;i++)
		a[i] = (a[i - 7] + a[i - 6]) % 2;

	//
	for (i = 0;i < 64;i++)
		qtbl_1d_thrld[i] = 1;

	//initilize original quantization table for JWC and the quantization for attack
	for (i = 0; i < 8; i++)
	{
		for (j = 0; j < 8; j++)
		{
			temp1 = scale2*qtbl_d[i][j] + 0.5;
			if (temp1 < 1) Q[zigzag[i][j]] = 1;
			else if (temp1>255) Q[zigzag[i][j]] = 255;
			else Q[zigzag[i][j]] = (int)temp1;
			//Q[zigzag[i][j]]=qtbl_d[i][j];//1; //int(0.1*qtbl_d[i][j]+0.5);
			//int(0.5*qtbl_d[i][j]+0.5);////2*qtbl_d[i][j];//0;
			//int(0.1*qtbl_d[i][j]+0.5);//qtbl_d[i][j]/2; 
			temp1 = scale*qtbl_d[i][j];
			if (temp1 < 1) ori_qtbl[i][j] = 1;
			else if (temp1>255) ori_qtbl[i][j] = 255;
			else ori_qtbl[i][j] = (int)temp1;
			//ori_qtbl[i][j]=(temp1<256)?((int)temp1):255;
		}
	}
	//generate the one-dimension quantization table from ori_qtbl [] zigzag[]
	for (u = 0; u < 8; u++)
		for (v = 0; v < 8; v++)
			qtbl_1d[zigzag[u][v]] = ori_qtbl[u][v];



	// intilialization for optimization
	// output_buffer=(char *)calloc(ROWS*COLS, sizeof(char));
	zz_coef = (int *)malloc(64 * sizeof(int)); /* store the coefficent of one block */

	zz_ind = (int *)malloc(64 * sizeof(int));
	state = (statenode *)malloc(64 * sizeof(statenode));
	stack = (int *)malloc(64 * sizeof(int));

	// initial the first state (state 0) once which corresponds to the DC coefficient
	state[0].r = 0;
	state[0].dist_cum = 0;
	state[0].rate_cum = 0;
	state[0].min_cost = 0;


	/* input the original pgm image to input[][] */
	// infd=fopen("lena512.raw","rb");
	infd = fopen(argv[5], "rb");
	fread(input, sizeof(unsigned char), ROWS*COLS, infd);
	fclose(infd);
	
	//precompress the image
	// count the time
	// begin=clock();
	for (i = 0; i < 256; i++)
	{
		ac_counts[i] = 0;
		dc_counts[i] = 0;
	}

	/* the ROWSxCOLS image is processed by ROWS/8xCOLS/8 block lines and columns */
	for (i = 0; i < ROWS / 8; i++)
	{
		for (j = 0; j < COLS / 8; j++)
		{
			// change the format of unsigned char to integer before computation 
			int sum = 0;
			for (u = 0; u < 8; u++)
			{
				for (v = 0; v < 8; v++)
				{

					inblock[u][v] = (int)input[i * 8 + u][j * 8 + v];
					sum += inblock[u][v];
				}
			}
			double blk_mean = (double)sum / 64;
			//sigmasquare[i][j] = 0;

			//for (u = 0; u < 8; u++)
			//{
			//	for (v = 0; v < 8; v++)
			//	{

			//		sigmasquare[i][j] += (inblock[u][v] - blk_mean)*(inblock[u][v] - blk_mean);

			//	}
			//}
			//sigmasquare[i][j] = 2 * sigmasquare[i][j] / 64 + 58.5225;//每一个块的方差*2 + c2

			// remove the mean of pixels in the image block
			for (u = 0; u < 8; u++)
				for (v = 0; v < 8; v++)
					inblock[u][v] = inblock[u][v] - 128;

			// call fast integer forward DCT function	
			/* Forward DCT of one block */
			int x, y;
			temp = 0.0;
			for (u = 0; u < 8; u++)
			{
				for (v = 0; v < 8; v++)
				{
					temp = 0.0;
					for (x = 0; x < 8; x++)
						for (y = 0; y < 8; y++)
							temp += (double)inblock[x][y] * cos((2 * x + 1)*u*pi / 16)*cos((2 * y + 1)*v*pi / 16);
					adct_1b[u][v] = (int)temp*c[u] * c[v] / 4;
				}
			}
			//GX_DCT_Weight_dct_8x8(inblock,adct_1b);  fast algorithm
			///////////////////////////////////////////////////////////////////////////////////////////
			double coe_mean = 0;
			double abs_adct[8][8];
			for (int i = 0; i < 8; i++)
			{
				for (int j = 0; j < 8; j++)
				{
					abs_adct[i][j] = adct_1b[i][j];
					coe_mean += abs_adct[i][j] / 64;
				}
			}
			sigmasquare[i][j] = 0;
			for (u = 0; u < 8; u++)
			{
				for (v = 0; v < 8; v++)
				{

					sigmasquare[i][j] += (abs_adct[u][v] - coe_mean)*(abs_adct[u][v] - coe_mean);

				}
			}
			sigmasquare[i][j] = 2 * sigmasquare[i][j] / 64 + 58.5225;//每一个块的方差*2 + c2
			///////////////////////////////////////////////////////////////////////////////////////////
			//sigmasquare[i][j] = 4000;
			// Quanntization of one block 
			for (u = 0; u < 8; u++)
			{
				for (v = 0; v < 8; v++)
				{
					adct[i * 8 + u][j * 8 + v] = adct_1b[u][v];
					temp1 = adct_1b[u][v];
					if (temp1 < 0)
					{
						temp1 = -temp1;
						temp1 += ori_qtbl[u][v] / 2;
						temp2 = (int)temp1 / ori_qtbl[u][v];
						recon_index[i * 8 + u][j * 8 + v] = -temp2;
					}
					else
					{
						temp1 += ori_qtbl[u][v] / 2;
						temp2 = (int)temp1 / ori_qtbl[u][v];
						recon_index[i * 8 + u][j * 8 + v] = temp2;
					}
				}
			}
			// change the 8x8 block to zigzag sequence form 
			for (u = 0; u < 8; u++)
				for (v = 0; v < 8; v++)
					zz_ind[zigzag[u][v]] = recon_index[i * 8 + u][j * 8 + v];

			// replace DC value of each block as the difference (DPCM)
			tempdc = zz_ind[0];
			zz_ind[0] = zz_ind[0] - last_dc_value;
			last_dc_value = tempdc;

			// Fake Huffman encode to get the statistices of the (run, pair) of this image
			fake_blockencode(zz_ind, ac_counts, &total, dc_counts);

		} /* end of the loop for one block */
	}
	// optimizing AC
	ite_num = 1; // at least one iteration
	previouscost = 0;
	///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
	int count = 0; //DCT块计数器
	for (i = 0; i < ROWS / 8; i++)
	{
		for (j = 0; j < COLS / 8; j++)
		{
			if (count % 32 == 0)
			{
				double total_sc = 0;
				for (k = 63; k >= 0; k--)
				{
					int tmp_count = -1;
					Sc = 0;
					for (int p = i; p < ROWS / 8; p++)//到了一个区域的开头，往后遍历32个块
					{
						for (int q = j; q < COLS / 8; q++)
						{
							tmp_count++;
							//Sc += (zz[k] * zz[k]);
							//cout << endl;
							for (u = 0; u < 8; u++)
								for (v = 0; v < 8; v++)
								{
									zz_coef[zigzag[u][v]] = abs(recon_index[aa[p][q] * 8 + u][bb[p][q] * 8 + v]);//实现块置换的地方
									//cout << zz_coef[zigzag[u][v]] << endl;h
								}
							Sc += zz_coef[k]*zz_coef[k];
							if (tmp_count == 31) break;
						}
						if (tmp_count == 31) break;
					}
					total_sc += Sc;
				}
				if (total_sc >= 200)
				{
					if (count / 32 % 2 == 1) //B区域
						cc[count / 64] = min(cc[count / 64], k);
					else
						cc[count / 64] = k;
					break;
				}
				if (k < 7)
				{
					cc[count / 64] = k;
					break;
				}
			}
			count++;
		}
	}

	////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////    。
	for (;;)
	{
		// generate the entropy vector
		temp1 = log10((float)total) / log10((float)2);
		for (i = 0; i < 256; i++)
		{
			fix_part = (int)i & 0x0F;
			if (ac_counts[i] == 0)
				ac_r[i] = lamda2*(fix_part + temp1);
			else
				ac_r[i] = lamda2*(fix_part + temp1 - log10((float)ac_counts[i]) / log10((float)2));
		}

		total = 0;
		distortion = 0;
		rate_tle = 0;
		minimumcost = 0;
		for (i = 0; i < 256; i++)
			ac_counts[i] = 0;

		count = 0; //DCT块计数器置零
		for (i = 0; i < ROWS / 8; i++)
		{
			for (j = 0; j < COLS / 8; j++)
			{
				for (int k = 0;k < 256; k++)
					ent_ac[k] = sigmasquare[aa[i][j]][bb[i][j]] * ac_r[k];


				for (u = 0; u < 8; u++)
					for (v = 0; v < 8; v++)
						zz_coef[zigzag[u][v]] = adct[aa[i][j] * 8 + u][bb[i][j] * 8 + v];//实现块置换的地方
 //hide--------------------------------------------

				td = count / 64;
				//th = (tr % 2 + td % 2) % 2;
				tb = a[td];
				//cout << tb << endl;
				//			printf("a=%d\n", a[td]);
				if ((tb == 0 && count / 32 % 2 == 0)/*A区域*/ || (tb == 1 && count / 32 % 2 == 1)/*B区域*/)
				{
					for (k = cc[td]; k <= 63; k++)
					{
						zz_coef[k] = 0;
					}
					block_type = 0;
				}
				/*for (u = 0; u < 8; u++)
				{
					for (v = 0; v < 8; v++)
						cout << zz_coef[zigzag[u][v]] << " ";
					cout << endl;
				}*/
				cut = cc[td];

				opti_block(aa[i][j], bb[i][j], zz_coef, state, stack/*64个int*/, &point/*空*/, ac_counts/*全零*/, &total/*totalpair*/, &distortion, &rate_tle, &minimumcost, block_type, cut);
				count++;
			}
		}

		distortion = distortion / (ROWS*COLS);
		rate_tle = rate_tle / (ROWS*COLS*lamda2);
		minimumcost = minimumcost / (ROWS*COLS);
		printf("Current normalized distortion is %f\n", distortion);
		printf("Current normalized bit rate is %f\n", rate_tle);
		printf("Current normalized minimumcost is %f\n", minimumcost);

		// check whether the iteration converges
		if (fabs(previouscost - minimumcost) < epslon)
			break;
		ite_num++;
		if (ite_num > 300)
			break;
		previouscost = minimumcost;
		//update the quantization table 
		update_qtbl();
	}

	// end=clock();
	pairnum_0 = customized_table(dc_counts, dc_bits_0, dc_val_0);
	pairnum = customized_table(ac_counts, ac_bits_0, ac_val_0);

	for (i = 0;i < 8;i++)
		for (j = 0;j < 8;j++)
			Lena_jpeg_struct.quant_tbl_0[i * 8 + j] = (unsigned char)qtbl_1d[zigzag[i][j]];

	//write to JPEG file
	//stream=fopen("stream.jpg", "wb");
	stream = fopen(argv[6], "wb");
	outputheader(&Lena_jpeg_struct);

	last_dc_value = 0;

	for (i = 0; i < ROWS / 8; i++)
	{
		for (j = 0; j < COLS / 8; j++)
		{
			for (u = 0; u < 8; u++)
				for (v = 0; v < 8; v++)
					zz_ind[zigzag[u][v]] = recon_index[i * 8 + u][j * 8 + v];
			// replace DC value of each block as the difference (DPCM)  
			tempdc = zz_ind[0];
			zz_ind[0] = zz_ind[0] - last_dc_value;
			last_dc_value = tempdc;
			//block_encode(zz_ind, dctbl, actbl);


			encode_one_block(0, zz_ind);
		}
	}

	finishjpegstream();
	fclose(stream);

	end = clock();
	time = (double)(end - begin) / CLOCKS_PER_SEC;
	printf("%d iterations of optimization!\n", (ite_num - 1));
	printf("%8.6f seconds has been used\n", time);
	printf("pairnum=%d\n", pairnum);

	free(zz_coef);     free(zz_ind);
	free(state);

	free(stack);
	free(a);

	free(Lena_jpeg_struct.quant_tbl_0);


	delete wm_bit;

	system("pause");
	return 0;

}