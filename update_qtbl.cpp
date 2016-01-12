/* update quantization table while satifying watermarking constraint */


#include "jhuff.hpp"

extern int ori_qtbl[8][8], qtbl_1d[64], qtbl_1d_thrld[64], aqant[ROWS][COLS],
adct[ROWS][COLS], recon_index[ROWS][COLS];
extern short int zigzag[8][8];

// update quantization table qtbl_1d
void update_qtbl()
{
	register int i, j, u, v;
	int cross[8][8], square[8][8];

	// reconstruct the image index from state, stack and point
	for (u = 0; u < 8; u++)
		for (v = 0; v < 8; v++)
		{
			cross[u][v] = 0;
			square[u][v] = 0;
		}

	//update 63 step sizes for AC coefficients
	for (i = 0; i < ROWS / 8; i++)
		for (j = 0; j < COLS / 8; j++)
			for (u = 0; u < 8; u++)
				for (v = 0; v < 8; v++)
				{
					//cross[u][v]=cross[u][v]+aqant[i*8+u][j*8+v]*recon_index[i*8+u][j*8+v]; 
					cross[u][v] = cross[u][v] + adct[i * 8 + u][j * 8 + v] * recon_index[i * 8 + u][j * 8 + v];
					square[u][v] = square[u][v] + recon_index[i * 8 + u][j * 8 + v] * recon_index[i * 8 + u][j * 8 + v];
				}

	// not update DC step size
	u = 0;
	for (v = 1; v < 8; v++)
	{
		if (square[u][v] != 0)
		{
			//qtbl_1d[zigzag[u][v]]=(int)ori_qtbl[u][v]*cross[u][v]/square[u][v];
			qtbl_1d[zigzag[u][v]] = (int)(cross[u][v] / square[u][v] + 0.5);
			if (qtbl_1d[zigzag[u][v]] < qtbl_1d_thrld[zigzag[u][v]])
				qtbl_1d[zigzag[u][v]] = qtbl_1d_thrld[zigzag[u][v]];
			if (qtbl_1d[zigzag[u][v]] > 255)
				qtbl_1d[zigzag[u][v]] = 255;
		}
		else
			qtbl_1d[zigzag[u][v]] = ori_qtbl[u][v];
	}

	for (u = 1; u < 8; u++)
		for (v = 0; v < 8; v++)
		{
			if (square[u][v] != 0)
			{
				//qtbl_1d[zigzag[u][v]]=(int)ori_qtbl[u][v]*cross[u][v]/square[u][v];
				qtbl_1d[zigzag[u][v]] = (int)(cross[u][v] / square[u][v] + 0.5);
				if (qtbl_1d[zigzag[u][v]] < qtbl_1d_thrld[zigzag[u][v]])
					qtbl_1d[zigzag[u][v]] = qtbl_1d_thrld[zigzag[u][v]];
				if (qtbl_1d[zigzag[u][v]] > 255)
					qtbl_1d[zigzag[u][v]] = 255;
			}
			else
				qtbl_1d[zigzag[u][v]] = ori_qtbl[u][v];
		}
}
