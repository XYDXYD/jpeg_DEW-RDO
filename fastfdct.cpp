/* fast inverse IDCT algorithm  * /
/* There is a small PSNR loss using this fast algorithm */

#define len 14
typedef int DCTELEM;
#define DCTsize 8
#define DCTSIZE 8
#define DCTsize2 64
#define CONST_BITS 8
#define FIX_0_382683433  ((__int32)   98)	// FIX(0.382683433) 
#define FIX_0_541196100  ((__int32)  139)	// FIX(0.541196100) 
#define FIX_0_707106781  ((__int32)  181)	// FIX(0.707106781)
#define FIX_1_306562965  ((__int32)  334)	// FIX(1.306562965)

#define FIX_1_082392200  ((__int32)  277)	// FIX(1.082392200) 
#define FIX_1_414213562  ((__int32)  362)	// FIX(1.414213562) 
#define FIX_1_847759065  ((__int32)  473)	// FIX(1.847759065) 
#define FIX_2_613125930  ((__int32)  669)	// FIX(2.613125930) 

#define FAST_FLOAT float

#define RIGHT_SHIFT(x, n) (x>>n)
#define DESCALE(x,n)  RIGHT_SHIFT(x, n)

#define MULTIPLY(var,const)  ((DCTELEM) DESCALE((var) * (const), CONST_BITS))

static const int GX_DCT_weight[DCTsize][DCTsize] = {
	{512,369,392,435,512,652,946,1855},
	{369,266,283,314,369,470,682,1338},
	{392,283,300,333,392,499,724,1420},
	{435,314,333,370,435,554,805,1578},
	{512,369,392,435,512,652,946,1856},
	{652,470,499,554,652,829,1204,2362},
	{946,682,724,805,946,1204,1748,3429},
	{1855,1338,1420,1578,1856,2362,3429,6726}
};

void GX_DCT_fdct_ifast(DCTELEM * data)
{
	DCTELEM tmp0, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
	DCTELEM tmp10, tmp11, tmp12, tmp13;
	DCTELEM z1, z2, z3, z4, z5, z11, z13;
	DCTELEM *dataptr;
	int ctr;

	// Pass 1: process rows. 
	dataptr = data;
	for (ctr = DCTsize - 1; ctr >= 0; ctr--) {
		tmp0 = dataptr[0] + dataptr[7];
		tmp7 = dataptr[0] - dataptr[7];
		tmp1 = dataptr[1] + dataptr[6];
		tmp6 = dataptr[1] - dataptr[6];
		tmp2 = dataptr[2] + dataptr[5];
		tmp5 = dataptr[2] - dataptr[5];
		tmp3 = dataptr[3] + dataptr[4];
		tmp4 = dataptr[3] - dataptr[4];

		// Even part 
		tmp10 = tmp0 + tmp3;	//phase 2 
		tmp13 = tmp0 - tmp3;
		tmp11 = tmp1 + tmp2;
		tmp12 = tmp1 - tmp2;

		dataptr[0] = tmp10 + tmp11; // phase 3 
		dataptr[4] = tmp10 - tmp11;

		z1 = MULTIPLY(tmp12 + tmp13, FIX_0_707106781); // c4 
		dataptr[2] = tmp13 + z1;	// phase 5
		dataptr[6] = tmp13 - z1;

		//Odd part
		tmp10 = tmp4 + tmp5;	// phase 2 
		tmp11 = tmp5 + tmp6;
		tmp12 = tmp6 + tmp7;

		//The rotator is modified from fig 4-8 to avoid extra negations. 
		z5 = MULTIPLY(tmp10 - tmp12, FIX_0_382683433); // c6
		z2 = MULTIPLY(tmp10, FIX_0_541196100) + z5; // c2-c6 
		z4 = MULTIPLY(tmp12, FIX_1_306562965) + z5; // c2+c6 
		z3 = MULTIPLY(tmp11, FIX_0_707106781); // c4 

		z11 = tmp7 + z3;		//phase 5
		z13 = tmp7 - z3;

		dataptr[5] = z13 + z2;	// phase 6 
		dataptr[3] = z13 - z2;
		dataptr[1] = z11 + z4;
		dataptr[7] = z11 - z4;

		dataptr += DCTsize;		// advance pointer to next row 
	}

	// Pass 2: process columns. 
	dataptr = data;
	for (ctr = DCTsize - 1; ctr >= 0; ctr--) {
		tmp0 = dataptr[DCTsize * 0] + dataptr[DCTsize * 7];
		tmp7 = dataptr[DCTsize * 0] - dataptr[DCTsize * 7];
		tmp1 = dataptr[DCTsize * 1] + dataptr[DCTsize * 6];
		tmp6 = dataptr[DCTsize * 1] - dataptr[DCTsize * 6];
		tmp2 = dataptr[DCTsize * 2] + dataptr[DCTsize * 5];
		tmp5 = dataptr[DCTsize * 2] - dataptr[DCTsize * 5];
		tmp3 = dataptr[DCTsize * 3] + dataptr[DCTsize * 4];
		tmp4 = dataptr[DCTsize * 3] - dataptr[DCTsize * 4];

		// Even part 
		tmp10 = tmp0 + tmp3;	// phase 2 
		tmp13 = tmp0 - tmp3;
		tmp11 = tmp1 + tmp2;
		tmp12 = tmp1 - tmp2;

		dataptr[DCTsize * 0] = tmp10 + tmp11; // phase 3 
		dataptr[DCTsize * 4] = tmp10 - tmp11;

		z1 = MULTIPLY(tmp12 + tmp13, FIX_0_707106781); // c4 
		dataptr[DCTsize * 2] = tmp13 + z1; // phase 5 
		dataptr[DCTsize * 6] = tmp13 - z1;

		// Odd part 
		tmp10 = tmp4 + tmp5;	// phase 2 
		tmp11 = tmp5 + tmp6;
		tmp12 = tmp6 + tmp7;

		// The rotator is modified from fig 4-8 to avoid extra negations. 
		z5 = MULTIPLY(tmp10 - tmp12, FIX_0_382683433); // c6 
		z2 = MULTIPLY(tmp10, FIX_0_541196100) + z5; // c2-c6 
		z4 = MULTIPLY(tmp12, FIX_1_306562965) + z5; // c2+c6 
		z3 = MULTIPLY(tmp11, FIX_0_707106781); // c4 

		z11 = tmp7 + z3;		// phase 5 
		z13 = tmp7 - z3;

		dataptr[DCTsize * 5] = z13 + z2; // phase 6 
		dataptr[DCTsize * 3] = z13 - z2;
		dataptr[DCTsize * 1] = z11 + z4;
		dataptr[DCTsize * 7] = z11 - z4;

		dataptr++;			// advance pointer to next column 
	}
}


void jpeg_fdct_float(FAST_FLOAT * data)
{
	FAST_FLOAT tmp0, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7;
	FAST_FLOAT tmp10, tmp11, tmp12, tmp13;
	FAST_FLOAT z1, z2, z3, z4, z5, z11, z13;
	FAST_FLOAT *dataptr;
	int ctr;

	/* Pass 1: process rows. */

	dataptr = data;
	for (ctr = DCTSIZE - 1; ctr >= 0; ctr--) {
		tmp0 = dataptr[0] + dataptr[7];
		tmp7 = dataptr[0] - dataptr[7];
		tmp1 = dataptr[1] + dataptr[6];
		tmp6 = dataptr[1] - dataptr[6];
		tmp2 = dataptr[2] + dataptr[5];
		tmp5 = dataptr[2] - dataptr[5];
		tmp3 = dataptr[3] + dataptr[4];
		tmp4 = dataptr[3] - dataptr[4];

		/* Even part */

		tmp10 = tmp0 + tmp3;	/* phase 2 */
		tmp13 = tmp0 - tmp3;
		tmp11 = tmp1 + tmp2;
		tmp12 = tmp1 - tmp2;

		dataptr[0] = tmp10 + tmp11; /* phase 3 */
		dataptr[4] = tmp10 - tmp11;

		z1 = (tmp12 + tmp13) * ((FAST_FLOAT) 0.707106781); /* c4 */
		dataptr[2] = tmp13 + z1;	/* phase 5 */
		dataptr[6] = tmp13 - z1;

		/* Odd part */

		tmp10 = tmp4 + tmp5;	/* phase 2 */
		tmp11 = tmp5 + tmp6;
		tmp12 = tmp6 + tmp7;

		/* The rotator is modified from fig 4-8 to avoid extra negations. */
		z5 = (tmp10 - tmp12) * ((FAST_FLOAT) 0.382683433); /* c6 */
		z2 = ((FAST_FLOAT) 0.541196100) * tmp10 + z5; /* c2-c6 */
		z4 = ((FAST_FLOAT) 1.306562965) * tmp12 + z5; /* c2+c6 */
		z3 = tmp11 * ((FAST_FLOAT) 0.707106781); /* c4 */

		z11 = tmp7 + z3;		/* phase 5 */
		z13 = tmp7 - z3;

		dataptr[5] = z13 + z2;	/* phase 6 */
		dataptr[3] = z13 - z2;
		dataptr[1] = z11 + z4;
		dataptr[7] = z11 - z4;

		dataptr += DCTSIZE;		/* advance pointer to next row */
	}

	/* Pass 2: process columns. */

	dataptr = data;
	for (ctr = DCTSIZE - 1; ctr >= 0; ctr--) {
		tmp0 = dataptr[DCTSIZE * 0] + dataptr[DCTSIZE * 7];
		tmp7 = dataptr[DCTSIZE * 0] - dataptr[DCTSIZE * 7];
		tmp1 = dataptr[DCTSIZE * 1] + dataptr[DCTSIZE * 6];
		tmp6 = dataptr[DCTSIZE * 1] - dataptr[DCTSIZE * 6];
		tmp2 = dataptr[DCTSIZE * 2] + dataptr[DCTSIZE * 5];
		tmp5 = dataptr[DCTSIZE * 2] - dataptr[DCTSIZE * 5];
		tmp3 = dataptr[DCTSIZE * 3] + dataptr[DCTSIZE * 4];
		tmp4 = dataptr[DCTSIZE * 3] - dataptr[DCTSIZE * 4];

		/* Even part */

		tmp10 = tmp0 + tmp3;	/* phase 2 */
		tmp13 = tmp0 - tmp3;
		tmp11 = tmp1 + tmp2;
		tmp12 = tmp1 - tmp2;

		dataptr[DCTSIZE * 0] = tmp10 + tmp11; /* phase 3 */
		dataptr[DCTSIZE * 4] = tmp10 - tmp11;

		z1 = (tmp12 + tmp13) * ((FAST_FLOAT) 0.707106781); /* c4 */
		dataptr[DCTSIZE * 2] = tmp13 + z1; /* phase 5 */
		dataptr[DCTSIZE * 6] = tmp13 - z1;

		/* Odd part */

		tmp10 = tmp4 + tmp5;	/* phase 2 */
		tmp11 = tmp5 + tmp6;
		tmp12 = tmp6 + tmp7;

		/* The rotator is modified from fig 4-8 to avoid extra negations. */
		z5 = (tmp10 - tmp12) * ((FAST_FLOAT) 0.382683433); /* c6 */
		z2 = ((FAST_FLOAT) 0.541196100) * tmp10 + z5; /* c2-c6 */
		z4 = ((FAST_FLOAT) 1.306562965) * tmp12 + z5; /* c2+c6 */
		z3 = tmp11 * ((FAST_FLOAT) 0.707106781); /* c4 */

		z11 = tmp7 + z3;		/* phase 5 */
		z13 = tmp7 - z3;

		dataptr[DCTSIZE * 5] = z13 + z2; /* phase 6 */
		dataptr[DCTSIZE * 3] = z13 - z2;
		dataptr[DCTSIZE * 1] = z11 + z4;
		dataptr[DCTSIZE * 7] = z11 - z4;

		dataptr++;			/* advance pointer to next column */
	}
}




void GX_DCT_Weight_dct_8x8(int input[DCTsize][DCTsize], int GX_DCT_1dout[8][8]) {
	//void GX_DCT_Weight_dct_8x8(int *datain, int *GX_DCT_1dout){

	int i, j;
	int datain[64];

	for (i = 0;i < DCTsize;i++)
		for (j = 0;j < DCTsize;j++)
			datain[i*DCTsize + j] = input[i][j];
	// dct transform
	GX_DCT_fdct_ifast(datain);

	//weighting and out
	for (i = 0;i < DCTsize;i++)
		for (j = 0;j < DCTsize;j++)
			GX_DCT_1dout[i][j] = ((GX_DCT_weight[i][j] * datain[i*DCTsize + j]) >> 12);

}

/*

GX_DCT_Weight_dct_8x8(int input[DCTsize][DCTsize],int GX_DCT_1dout[8][8]){
//void GX_DCT_Weight_dct_8x8(int *datain, int *GX_DCT_1dout){

	int i,j;
	float datain[64];

	for (i=0;i<DCTsize;i++ )
		for(j=0;j<DCTsize;j++)
			datain[i*DCTsize+j]=(float)input[i][j];
	// dct transform
	jpeg_fdct_float (datain);

	//weighting and out
	for (i=0;i<DCTsize;i++ )
		for(j=0;j<DCTsize;j++)
		   GX_DCT_1dout[i][j]=((GX_DCT_weight[i][j]*datain[i*DCTsize+j])>>12);

}*/