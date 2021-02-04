/*
 * Fast-ish evaluation of SURFs given as sums of SURFSums, each one given by
 * (possibly gzipped) raw binary data.
 */

#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <gmp.h>
#include <zlib.h>

#define LINEBUFSIZE 4096
#define STREAMBUFSIZE (32*1024*1024)
#define CHUNKBUFSIZE 192

int crunch(int argc, char *argv[])
{
     FILE *file;
     gzFile gzfile;

     char line[LINEBUFSIZE];
     unsigned int nvalues, i, j, k, chunk_size, max_chunk_size, nrays;
     int*int_chunk;
     mpq_t *values, *results, *mpq_chunk, x, y;

     if (argc < 4) {
          /* fprintf(stderr, "Syntax: %s values results data0 [...]\n", argv[0]); */
	  return 1;
     }

     if (sizeof(int) != 4) {
        /* fprintf(stderr, "crunch needs sizeof(int) == 4\n"); */
	 return 1;
     }

     /************************************************************************/
     /* Don't suicide just because someone knocks on the door. */
     /************************************************************************/
     signal(SIGPOLL, SIG_IGN);

     /************************************************************************/
     /* Read the values and set up the results. */
     /************************************************************************/

     if (!(file = fopen(argv[1], "r"))) return 1;
     if (!fgets(line, LINEBUFSIZE, file)) return 2;
     if (!sscanf(line, "%d", &nvalues)) return 3;

     values = malloc(nvalues * sizeof(mpq_t));
     results = malloc(nvalues * sizeof(mpq_t));

     if (!values || !results) return 4;
     for (i = 0; i < nvalues; ++i) {
	  mpq_inits(values[i], results[i], NULL);
	  if (!fgets(line, LINEBUFSIZE, file)) return 5;
	  if (mpq_set_str(values[i], line, 10)) return 6;
	  mpq_canonicalize(values[i]);
     }
     fclose(file);

     /************************************************************************/
     /* Set up the chunk buffer. */
     /************************************************************************/

     max_chunk_size = CHUNKBUFSIZE;
     int_chunk = malloc(max_chunk_size * sizeof(int));
     mpq_chunk = malloc(max_chunk_size * sizeof(mpq_t));
     if (!int_chunk || !mpq_chunk) return 7;
     for (i = 0; i < max_chunk_size; ++i) {
	  mpq_init(mpq_chunk[i]);
     }

     /************************************************************************/
     /* Loop over the SURFs from all data files. */
     /************************************************************************/

     mpq_inits(x, y, NULL);
     for (k = 3; k < argc; ++k) {
	 if(!(gzfile = gzopen(argv[k], "rb"))) return 8;
	 if (gzbuffer(gzfile, STREAMBUFSIZE)) return 9;

	 for (;;) {
	     /*
	      * Each data file consists of blocks of the form [nrays | chunk].
	      * Each chunk consists of 2*nrays+1 integers: scalar,a0,b0,a1,b1,...
	      * corresponding to scalar/(a0*s-b0)/(a1*s-b1)/...
	      */

	     if(!(i = gzread(gzfile, &nrays, sizeof(int))))
		 break;
	     if (i != sizeof(int)) return 10;

	     chunk_size = 2*nrays + 1;

	     /*
	      * If necessary, resize the chunk buffer.
	      * We don't care about its previous contents.
	      */
	     if (chunk_size > max_chunk_size) {
		 for (i = 0; i < max_chunk_size; ++i) {
		     mpq_clear(mpq_chunk[i]);
		     }
		 free(int_chunk);
		 free(mpq_chunk);
		 max_chunk_size = 2 * chunk_size;
		 
		 int_chunk = malloc(max_chunk_size * sizeof(int));
		 mpq_chunk = malloc(max_chunk_size * sizeof(mpq_t));
		 if (!int_chunk || !mpq_chunk) return 11;

		 for (i = 0; i < max_chunk_size; ++i) {
		     mpq_init(mpq_chunk[i]);
		     }
		 }

	     /*
	      * Turn the chunk integers from the file into mpqs.
	      */
	     if (chunk_size*sizeof(int) != gzread(gzfile, int_chunk, chunk_size*sizeof(int)))
		 return 12;
	     for (i = 0; i < chunk_size; ++i) {
		 mpq_set_si(mpq_chunk[i], int_chunk[i], 1);
		 }

	     /* 
	      * For each element values[i] of 'values', evaluate the current
	      * simplicial chunk and add the result to results[i].
	      */
	     for (i = 0; i < nvalues; ++i) {
		 mpq_set(x, mpq_chunk[0]);
		 for (j = 1; j < chunk_size;) {
		     mpq_mul(y, mpq_chunk[j++], values[i]);
		     mpq_sub(y, y, mpq_chunk[j++]);
		     mpq_div(x, x, y);
		     }
		 mpq_add(results[i], results[i], x);
		 }
	     }
	 gzclose(gzfile);
     }

     /************************************************************************/
     /* Clean up. */
     /************************************************************************/

     free(int_chunk);
     for (i = 0; i < max_chunk_size; ++i) {
	  mpq_clear(mpq_chunk[i]);
     }
     free(mpq_chunk);
     for (i = 0; i < nvalues; ++i) {
	  mpq_clear(values[i]);
     }
     free(values);
     mpq_clears(x, y, NULL);

     /************************************************************************/
     /* Write the results */
     /************************************************************************/

     file = fopen(argv[2], "w");
     if (!file) return 14;
     for (i=0; i < nvalues; ++i) {
	  if (!mpq_out_str(file, 10, results[i])) return 15;
	  fprintf(file, "\n");
     }
     fclose(file);

     return 0;
}
