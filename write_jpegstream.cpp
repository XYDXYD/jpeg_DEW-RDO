/* This file ise used to write out JPEG file */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "jhuff.hpp"
#include "sditojpeg.h"

#define BUFFER_SIZE 256

unsigned char buffer[BUFFER_SIZE + 2], *current_byte;

extern short int zigzag[8][8];
extern int pairnum, pairnum_0;
extern FILE *stream;

/* gloabl variables for Huffman encoding */
//for luminance

HUFF_TBL *dctbl_0, *actbl_0;
unsigned  char dc_bits_0[17];   //={0,0,1,5,1,1,1,1,1,1,0,0,0,0,0,0,0};
unsigned char dc_val_0[12];     //={0,1,2,3,4,5,6,7,8,9,10,11};
unsigned char ac_bits_0[33];    //={0,0,2,1,3,3,2,4,3,5,5,4,4,0,0,1,0x7d};
unsigned char ac_val_0[256];
/*=
{	0x01, 0x02, 0x03, 0x00, 0x04, 0x11, 0x05, 0x12,
	0x21, 0x31, 0x41, 0x06, 0x13, 0x51, 0x61, 0x07,
	0x22, 0x71, 0x14, 0x32, 0x81, 0x91, 0xa1, 0x08,
	0x23, 0x42, 0xb1, 0xc1, 0x15, 0x52, 0xd1, 0xf0,
	0x24, 0x33, 0x62, 0x72, 0x82, 0x09, 0x0a, 0x16,
	0x17, 0x18, 0x19, 0x1a, 0x25, 0x26, 0x27, 0x28,
	0x29, 0x2a, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39,
	0x3a, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49,
	0x4a, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59,
	0x5a, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69,
	0x6a, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79,
	0x7a, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89,
	0x8a, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98,
	0x99, 0x9a, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7,
	0xa8, 0xa9, 0xaa, 0xb2, 0xb3, 0xb4, 0xb5, 0xb6,
	0xb7, 0xb8, 0xb9, 0xba, 0xc2, 0xc3, 0xc4, 0xc5,
	0xc6, 0xc7, 0xc8, 0xc9, 0xca, 0xd2, 0xd3, 0xd4,
	0xd5, 0xd6, 0xd7, 0xd8, 0xd9, 0xda, 0xe1, 0xe2,
	0xe3, 0xe4, 0xe5, 0xe6, 0xe7, 0xe8, 0xe9, 0xea,
	0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8,
	0xf9, 0xfa};*/

	// for chrominance
HUFF_TBL *dctbl_1, *actbl_1;
unsigned char dc_bits_1[17] = { 0, 0, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0 };
unsigned char dc_val_1[] = { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 };
unsigned char ac_bits_1[17] = { 0, 0, 2, 1, 2, 4, 4, 3, 4, 7, 5, 4, 4, 0, 1, 2, 0x77 };
unsigned char ac_val_1[] =
{ 0x00, 0x01, 0x02, 0x03, 0x11, 0x04, 0x05, 0x21,
	0x31, 0x06, 0x12, 0x41, 0x51, 0x07, 0x61, 0x71,
	0x13, 0x22, 0x32, 0x81, 0x08, 0x14, 0x42, 0x91,
	0xa1, 0xb1, 0xc1, 0x09, 0x23, 0x33, 0x52, 0xf0,
	0x15, 0x62, 0x72, 0xd1, 0x0a, 0x16, 0x24, 0x34,
	0xe1, 0x25, 0xf1, 0x17, 0x18, 0x19, 0x1a, 0x26,
	0x27, 0x28, 0x29, 0x2a, 0x35, 0x36, 0x37, 0x38,
	0x39, 0x3a, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48,
	0x49, 0x4a, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58,
	0x59, 0x5a, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68,
	0x69, 0x6a, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78,
	0x79, 0x7a, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87,
	0x88, 0x89, 0x8a, 0x92, 0x93, 0x94, 0x95, 0x96,
	0x97, 0x98, 0x99, 0x9a, 0xa2, 0xa3, 0xa4, 0xa5,
	0xa6, 0xa7, 0xa8, 0xa9, 0xaa, 0xb2, 0xb3, 0xb4,
	0xb5, 0xb6, 0xb7, 0xb8, 0xb9, 0xba, 0xc2, 0xc3,
	0xc4, 0xc5, 0xc6, 0xc7, 0xc8, 0xc9, 0xca, 0xd2,
	0xd3, 0xd4, 0xd5, 0xd6, 0xd7, 0xd8, 0xd9, 0xda,
	0xe2, 0xe3, 0xe4, 0xe5, 0xe6, 0xe7, 0xe8, 0xe9,
	0xea, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8,
	0xf9, 0xfa };

long huff_put_buffer = 0; // buffer for accumulating the current bits 
int  huff_put_bits = 0;    // current number of bits in the buffer 

/* Emit a byte */
void emit_byte(char ch)
{
	*current_byte = ch;
	current_byte++;
	if (current_byte == (buffer + BUFFER_SIZE))
	{
		fwrite(buffer, 1, BUFFER_SIZE, stream);
		current_byte = buffer;
	}
}

/* Emit a markeode */
void emit_marker(char mark)
{
	emit_byte(0xFF);
	emit_byte(mark);
}

/* Emit a 2-byte integer; these are always MSB first in JPEG files */
void emit_2bytes(int value)
{
	emit_byte((value >> 8) & 0xFF);
	emit_byte(value & 0xFF);
}

/* Emit an Adobe header (optional) */
void emit_adobe(myjpeg_compress_struct *dstinfo)
{
	emit_marker(0xee);

	emit_2bytes(14);	// lenght of the header

	emit_byte(0x41);    // a
	emit_byte(0x64);    // d
	emit_byte(0x6f);    // o
	emit_byte(0x62);    // b
	emit_byte(0x65);	// e

	emit_2bytes(100);	// Version 
	emit_2bytes(0);		// Flags0 
	emit_2bytes(0);		// Flags1 

	switch (dstinfo->jpeg_color_space)
	{
	case 3:				// JCS_YCbCr
		emit_byte(1);
		break;
	case 5:				// JCS_YCCK
		emit_byte(2);
		break;
	default:
		emit_byte(0);	// others including RGB
	}
}

/* Emit a DQT marker */
void emit_dqt(myjpeg_compress_struct *dstinfo)
{
	int i, j;
	int qtbl_zz[64];

	emit_marker(0xdb);			// marker
	emit_2bytes(67);			// length 64(precion is 8 for baseline jpeg) + 1 + 2
	emit_byte(0);				// (prec<<4)+index where both index and precision are zero
	for (i = 0; i < 8; i++)			// change the quantization table to zigzag order first
	{
		for (j = 0; j < 8; j++)
		{
			qtbl_zz[zigzag[i][j]] = dstinfo->quant_tbl_0[i * 8 + j];
		}
	}
	for (i = 0; i < 64; i++)
	{
		emit_byte(qtbl_zz[i] & 0xFF);	//the table entries must be emitted in zigzag order.
	}

	if (dstinfo->num_components > 1)		//output the second quantization table
	{
		emit_marker(0xdb);		// marker
		emit_2bytes(67);		// length 64(precion is 8 for baseline jpeg) + 1 + 2
		emit_byte(1);			// (prec<<4)+index where index=1 and precision are zero
		for (i = 0; i < 8; i++)		// change the quantization table to zigzag order first
		{
			for (j = 0; j < 8; j++)
			{
				qtbl_zz[zigzag[i][j]] = dstinfo->quant_tbl_1[i * 8 + j];
			}
		}
		for (i = 0; i < 64; i++)
		{
			emit_byte(qtbl_zz[i] & 0xFF); // The table entries must be emitted in zigzag order. 
		}
	}
}

/* Emit a SOF marker */
void emit_sof(myjpeg_compress_struct *dstinfo)
{
	int ci;
	myjpeg_component_info *compptr;

	emit_marker(0xc0);						//SOF0: Baseline DCT

	emit_2bytes(3 * dstinfo->num_components + 2 + 5 + 1); //length 

//	emit_byte(8);                           // precision
	emit_byte(8);
	emit_2bytes(dstinfo->image_height);
	emit_2bytes(dstinfo->image_width);
	emit_byte(dstinfo->num_components);

	for (ci = 0, compptr = dstinfo->comp_info; ci < dstinfo->num_components; ci++, compptr++)
	{
		emit_byte(compptr->component_id);
		emit_byte((compptr->h_samp_factor << 4) + compptr->v_samp_factor);
		emit_byte(compptr->quant_tbl_no);
	}
}

/* Emit a DHT table (default tables) */
void emit_dht(int index, int is_ac)
{
	unsigned char *bit_ptr, *val_ptr;
	int length, i;

	if (index == 0)
	{
		if (is_ac)
		{
			bit_ptr = ac_bits_0;
			val_ptr = ac_val_0;
			index += 0x10;		// output index has AC bit set 
			//length = 162;
			length = pairnum;
		}
		else
		{
			bit_ptr = dc_bits_0;
			val_ptr = dc_val_0;
			//	length = 12; 
			length = pairnum_0;
		}
	}
	else
	{
		if (is_ac)
		{
			bit_ptr = ac_bits_1;
			val_ptr = ac_val_1;
			index += 0x10;		// output index has AC bit set 
			length = 162;
		}
		else
		{
			bit_ptr = dc_bits_1;
			val_ptr = dc_val_1;
			length = 12;
		}
	}

	emit_marker(0xc4);
	emit_2bytes(length + 2 + 1 + 16);
	emit_byte(index);

	/*for (i = 1; i <= 16; i++)
	{
		emit_byte(bit_ptr[i]);
	}*/

	for (i = 1; i <= 16; i++)
	{
		emit_byte(bit_ptr[i]);
	}

	for (i = 0; i < length; i++)
	{
		emit_byte(val_ptr[i]);
	}
}

/* Emit a SOS marker (always one scan)*/
void emit_sos(myjpeg_compress_struct *dstinfo)
{
	int i;

	emit_marker(0xda);

	emit_2bytes(2 * dstinfo->num_components + 2 + 1 + 3); // length 

	emit_byte(dstinfo->num_components);

	for (i = 0; i < dstinfo->num_components; i++)
	{
		if (i == 0)	//luminance
		{
			emit_byte(i + 1);   //component_id
			emit_byte(0);     // td<<4+ta where td=0 and ta=0
		}
		else		// chrominance
		{
			emit_byte(i + 1);   //component_id
			emit_byte(17);    //td<<4+ta where td=1 and ta=1
		}
	}
	emit_byte(0);   // Ss
	emit_byte(63);  // Se
	emit_byte(0);   // ah<<4+al
}

void write_header(myjpeg_compress_struct *dstinfo)
{
	// send SOI
	emit_marker(0xd8);

	// send Adobe header if there is one
	if (dstinfo->adobe_tag == 1)
		emit_adobe(dstinfo);

	// send quantization table(s)
	emit_dqt(dstinfo);

	// send frame header
	emit_sof(dstinfo);

	// send Huffman tables
	//	emit_marker(0xc4);
	//emit_2bytes(length + 2 + 1 + 16);
	//	emit_2bytes(0x00D2);
	//	emit_byte(00);
	emit_dht(0, 0);  // first DC table
	//  emit_byte(0x10);

	emit_dht(0, 1);  // first AC table

	if (dstinfo->num_components > 1)
	{
		emit_dht(1, 0);  // second DC table
		emit_dht(1, 1);  // second AC table
	}

	// send scan header
	emit_sos(dstinfo);
}

/* function jchuff() is used to create the standard Huffman table */
void jchuff_tbl(HUFF_TBL *htbl)
{
	int i, k, l, lastk, si;
	char huffsize[257];
	unsigned int huffcode[257], code;

	/* create the code length table for each symbol (refer to Figure C.1 of ISO/JTC 10918-1 */
	/* the entries are in code-length order */
	k = 0;
	for (l = 1; l <= 16; l++)
	{
		for (i = 1; i <= (int)htbl->bits[l]; i++)
		{
			huffsize[k++] = (char)l;
		}
	}
	huffsize[k] = 0;
	lastk = k;

	/* generate the Huffman codes in code-length order for each symbol */
	/* refer to Figure C.2 of ISO/JTC 10918-1 */
	code = 0;
	si = huffsize[0];
	k = 0;
	do
	{
		do
		{
			huffcode[k] = code;
			code++;
			k++;
		} while (huffsize[k] == si);

		if (huffsize[k] == 0)
		{
			break;
		}
		else
		{
			do
			{
				code <<= 1;
				si++;
			} while (huffsize[k] != si);
		}
	} while (huffsize[k] == si);

	/* generate encoding table (refer to Figure C.3 of ISO/JTC 10918-1) */
	memset((void *)(htbl->ehufsi), 0, sizeof(htbl->ehufsi));
	for (k = 0; k < lastk; k++)
	{
		htbl->ehufco[htbl->huffval[k]] = huffcode[k];
		htbl->ehufsi[htbl->huffval[k]] = huffsize[k];
	}
}


/* function append_bits() is used to output Huffman code of bytes to the file */
/* it is called by function block_encode() */
void append_bits(unsigned int code, int size)
{
	long put_buffer = (long)code;
	int  c, put_bits = huff_put_bits;

	put_buffer &= (((long)1) << size) - 1; /* mask off any excess bits in code */
	put_bits += size;                   /* new number of bits in buffer */
	put_buffer <<= 24 - put_bits;         /* align incoming bits */
	put_buffer |= huff_put_buffer;      /* merge with old contents in buffer */
	while (put_bits >= 8)
	{
		c = (int)((put_buffer >> 16) & 0xFF);
		emit_byte(c);
		// output_buffer[bytes_in_buffer++]=(char)c;
		if (c == 0xFF)   /* need to stuff a zero byte */
			emit_byte(0);
		put_buffer <<= 8;
		put_bits = put_bits - 8;
	}
	huff_put_buffer = put_buffer;   /* update global variables */
	huff_put_bits = put_bits;
}


/* function encode_one_block() is used to Huffman encode one image block */
void encode_one_block(int ci, int *zz)
{
	HUFF_TBL *dctbl, *actbl;
	register int temp, temp2, nbits;
	register int k, r, i;

	if (ci == 0)   //luminance
	{
		dctbl = dctbl_0;
		actbl = actbl_0;
	}
	else		//chrominance
	{
		dctbl = dctbl_1;
		actbl = actbl_1;
	}

	/* encode DC coefficient */
	temp = temp2 = zz[0];
	if (temp < 0)
	{
		temp = -temp;   /* temp is the absulate value of input coefficient */
		temp2--;      /* for negative coefficient, get complement of abs */
	}
	/* find the number of bits needed for the magnitude of the coeffcient */
	nbits = 0;
	while (temp)
	{
		nbits++;
		temp >>= 1;
	}

	/* emit the Huffman_coded symbol for the number of bits */
	append_bits(dctbl->ehufco[nbits], dctbl->ehufsi[nbits]);

	/* emit that number of bits of the value for positive coefficient
		or the complement of its magnitude for negative coefficient */
	if (nbits)
		append_bits((unsigned int)temp2, nbits);

	/* encode AC coefficients (refer to Figure F.1.2.2 */
	r = 0;   /* r is the run length of zero */
	for (k = 1; k < 64; k++)
	{
		if ((temp = zz[k]) == 0)
			r++;
		else
		{	/* if run length is greater than 15, emit special code 0xF0 */
			while (r > 15)
			{
				append_bits(actbl->ehufco[0xF0], actbl->ehufsi[0xF0]);
				r = r - 16;
			}
			temp2 = temp;
			if (temp < 0)
			{
				temp = -temp;
				temp2--;
			}
			/* find the number of bits needed for the magnitude of the coefficient */
			nbits = 1; /* Nonzero AC value  is at least 1 bits long */
			while (temp >>= 1)
				nbits++;

			/* emit Huffman symbol for run length/number of bits */
			i = (r << 4) + nbits;
			append_bits(actbl->ehufco[i], actbl->ehufsi[i]);

			/* emit that number of bits of the value for positive coefficient
				or the complement of its magnitude for negative coefficient */
			append_bits((unsigned int)temp2, nbits);
			r = 0;
		}
	}
	/* if the last coefficients are zero, emit an end-of-block code */
	if (r > 0)
		append_bits(actbl->ehufco[0], actbl->ehufsi[0]);
}

void outputheader(myjpeg_compress_struct *dstinfo)
{
	// open the output JPEG file stream here for testing
	// stream = fopen("../decoder/outwindows.jpg", "wb");
	current_byte = buffer;

	// output jpeg headers and tables first
	write_header(dstinfo);

	// generate Huffman table for block encoding
	dctbl_0 = (HUFF_TBL *)malloc(sizeof(HUFF_TBL));
	actbl_0 = (HUFF_TBL *)malloc(sizeof(HUFF_TBL));

	// copy the standard huffman bits and values to Huffman tables 
	memcpy(dctbl_0->bits, dc_bits_0, 17 * sizeof(unsigned char));
	memcpy(actbl_0->bits, ac_bits_0, 17 * sizeof(unsigned char));
	memcpy(dctbl_0->huffval, dc_val_0, 12 * sizeof(unsigned char));
	memcpy(actbl_0->huffval, ac_val_0, 162 * sizeof(unsigned char));

	// create Huffman table 
	jchuff_tbl(dctbl_0);
	jchuff_tbl(actbl_0);

	if (dstinfo->num_components > 1)
	{
		dctbl_1 = (HUFF_TBL *)malloc(sizeof(HUFF_TBL));
		actbl_1 = (HUFF_TBL *)malloc(sizeof(HUFF_TBL));

		memcpy(dctbl_1->bits, dc_bits_1, 17 * sizeof(unsigned char));
		memcpy(actbl_1->bits, ac_bits_1, 17 * sizeof(unsigned char));

		memcpy(dctbl_1->huffval, dc_val_1, 12 * sizeof(unsigned char));
		memcpy(actbl_1->huffval, ac_val_1, 162 * sizeof(unsigned char));

		jchuff_tbl(dctbl_1);
		jchuff_tbl(actbl_1);
	}
}

void finishjpegstream()
{
	/* Ensure the last bits in huff_put_buffer are sent out to file. To do so, append two end-of-block code
	which is 4 bits long each if it is grey image, or append four end-of-block code which is 2 bits long if
	a chrominance is the end component (here we simply add 4 EOB of actbl_1*/
	if (huff_put_bits > 0)
	{
		append_bits(actbl_0->ehufco[0], actbl_0->ehufsi[0]);
		append_bits(actbl_0->ehufco[0], actbl_0->ehufsi[0]);
		/*	append_bits(actbl_1->ehufco[0], actbl_1->ehufsi[0]);
			append_bits(actbl_1->ehufco[0], actbl_1->ehufsi[0]);
			append_bits(actbl_1->ehufco[0], actbl_1->ehufsi[0]);
			append_bits(actbl_1->ehufco[0], actbl_1->ehufsi[0]);*/
	}

	// send EOI
	emit_marker(0xd9);

	// flush the output buffer
	fwrite(buffer, 1, (current_byte - buffer), stream);

	free(dctbl_0);
	free(actbl_0);
	/*	free(dctbl_1);
		free(actbl_1);*/
		// fclose(stream);
}