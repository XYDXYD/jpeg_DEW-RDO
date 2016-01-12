/*
 * sditojpeg.h
 *
 * This header file contains the minimum parameter we need to create a JPEG file.
 *
 */

typedef struct
{
	int component_id;			/* identifier for this component (0..255) */
	int h_samp_factor;			/* horizontal sampling factor (1..4) */
	int v_samp_factor;			/* vertical sampling factor (1..4) */
	int quant_tbl_no;		    /* quantization table selector (0..3) */
	int width_in_blocks;
	int height_in_blocks;
	int MCU_width;				/* number of blocks per MCU, horizontally */
	int MCU_height;				/* number of blocks per MCU, vertically */
	int last_col_width;			/* # of non-dummy blocks across in last MCU */
	int last_row_height;		/* # of non-dummy blocks down in last MCU */
}myjpeg_component_info;

typedef struct
{
	int image_width;			/* input image width */
	int image_height;			/* input image height */
	int num_components;			/* # of color components in JPEG image */
	short int jpeg_color_space;	/* colorspace of JPEG image */
	int max_h_samp_factor;		/* largest h_samp_factor */
	int max_v_samp_factor;		/* largest v_samp_factor */
	char adobe_tag;				/* indicate whether an Adobe header is seen, 1: seen, 0: no */

	myjpeg_component_info comp_info[3];
	unsigned char *quant_tbl_0;
	unsigned char *quant_tbl_1;
}myjpeg_compress_struct;