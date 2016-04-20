/*
This file is part of the SigCert tool

* Copyright (c) 2011-2012 by Van-Chan Ngo.
* All rights reserved.
*
*/

/* a simple YICES wrapper */
/* input is taken from standard input */

#include <stdio.h>
#include <stdlib.h>
#include "yicesl_c.h"

int main(int argc, char **argv)
{
  int i, numpars, incomment, incmd, ok;
  unsigned long int strpos;
  char* buff;
  yicesl_context ctx = yicesl_mk_context();
  numpars = incomment = incmd = strpos = 0;
  int debug = 0;

  if (argc == 2 && !strcmp(argv[1],"-debug")) {
    debug=1;
  }


  buff = (char*) malloc(100000000*sizeof(char));
  i = getchar();
  while (i != EOF) {
	/*
    if (debug) {
      printf("%c",i);
    }
	*/
    /* skip all comments */
    if (i == ';') {
      incomment = 1;
    }
    if (incomment) {
      if (i == '\n') {
        incomment = 0;
      }
    } else {
      /* set incmd = 1 if we start in a command */
      if (numpars > 0) {
        incmd = 1;
      } else {
        incmd = 0;
      }
      if (strpos > 99999999) {
        printf("ERROR: input too long (%d)\n",strpos);
        exit(1);  /* error */
      }

      buff[strpos++] = i;

      if (i == '(') {
        numpars++;
      }
      if (i == ')') {
        numpars--;
      }

      if (numpars == 0 && incmd) {
        buff[strpos++]=0;
        ok = yicesl_read(ctx,buff);
        if (!ok) {
          printf("ERROR: %s\n",yicesl_get_last_error_message());
          exit(1);
        }
        printf("\n\n");
        fflush(stdout);
        strpos = 0;
      }
    }
    i = getchar();
  }

  free(buff);
  return 0;
}
