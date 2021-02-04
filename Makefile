CC = gcc
CFLAGS = -O2 -Wall -Wstrict-overflow=5 -s -z defs -shared -fPIC -lc -lgmp -lz

CCVERSION = $(shell $(CC) --version 2>/dev/null)
SAGEROOT = $(shell sage --root 2>/dev/null)

ifneq ($(SAGEROOT),)
	CFLAGS += -I $(SAGEROOT)/local/include -L $(SAGEROOT)/local/lib
ifeq ($(CCVERSION),)
	CC = $(SAGEROOT)/local/bin/gcc
	CCVERSION = $(shell $(CC) --version 2>/dev/null)
endif
endif

all: crunch.so addmany.so

addmany.so: addmany.pyx
	sage -python setup.py build_ext --inplace

crunch.so: crunch.c
ifeq ($(CCVERSION),)
	@echo "No C compiler found. Try manually setting 'CC'."
	@exit 1
endif

	$(CC) $(CFLAGS) crunch.c -o crunch.so -lgmp -lz

clean:
	rm -f crunch.so
	rm -f addmany.so

