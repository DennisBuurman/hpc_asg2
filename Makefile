CC = gcc
CXX = g++
CFLAGS = -Wall -Wextra -Wno-unused-result -Wno-unused-parameter -Wno-unused-but-set-variable -O3
CXXFLAGS = $(CFLAGS) -std=c++11

all:	mst

mst:	mst.o mmio.o matrix.o
	$(CXX) $(CFLAGS) -o $@ $^


mmio.o:	mmio.c
	$(CC) $(CFLAGS) -c mmio.c

%.o:	%.cc
	$(CXX) $(CXXFLAGS) -c $<

clean:
	rm -f *o
	rm -f mst
