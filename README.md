# Identifying Large Structural Balanced Cliques in Signed Graphs

This project aims to identify all large structural balanced cliques in signed graphs.

bce is the executable, and is compiled on Ubuntu 18.04.5, with -O3 optimization.

bitcoin.txt is an example signed graph. Most datasets used in our experiments are from the [SNAP](https://snap.stanford.edu/data/) and [KONECT](http://konect.cc/networks/).

## Running Format

./bce [1]input_graph [2]tau [3]alpha

**Running example for identifying large structural balanced cliques**

./bce ./bitcoin.txt 3 1

**Running example for enumerating all maximal structural balanced cliques**

./bce ./bitcoin.txt 3 n

### Note

To enumerate all maximal structural balanced cliques, alpha can be set as n (i.e., the number of vertices in the target graph).

## Graph Format

number of vertices \t number of edges \n

v0 \t v1 \t sign \n

v0 \t v2 \t sign \n

...
