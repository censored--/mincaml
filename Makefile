# Sumii's Makefile for Min-Caml (for GNU Make)
# 
# ack.ml�ʤɤΥƥ��ȥץ�����test/���Ѱդ���make do_test��¹Ԥ���ȡ�
# min-caml��ocaml�ǥ���ѥ��롦�¹Ԥ�����̤�ư����Ӥ��ޤ���

RESULT = min-caml
NCSUFFIX = .opt
CC = gcc
CFLAGS = -g -O2 -Wall

default: $(RESULT)
contest: 
ifneq ($(ARG3),)
	./min-caml -c -inline $(ARG3) ../sim/rt/min-rt
else
	./min-caml -c ../sim/rt/min-rt
endif

$(RESULT): debug-code top
## [��ʬ�ʽ�����Ѥ���]
## ��OCamlMakefile��Ť�GNU Make�ΥХ�(?)�Ǿ�Τ褦�������ɬ��(??)
## ��OCamlMakefile�Ǥ�debug-code��native-code�Τ��줾���
##   .mli������ѥ��뤵��Ƥ��ޤ��Τǡ�ξ���Ȥ�default:�α��դ�������
##   ��make���ˡ�.mli���ѹ�����Ƥ���Τǡ�.ml��ƥ���ѥ��뤵���
clean:: nobackup

# ���⤷�������¤�����顢����˹�碌���Ѥ���
ML_SOURCES = log.ml util.ml float.c type.ml id.ml m.ml s.ml \
syntax.ml myparser.mly mylexer.mll typing.mli typing.ml kNormal.mli kNormal.ml \
ss.ml subelim.ml\
alpha.mli alpha.ml beta.mli beta.ml assoc.mli assoc.ml \
inline.mli inline.ml constFold.mli constFold.ml elim.mli elim.ml \
closure.mli closure.ml \
typing_closure.mli typing_closure.ml \
tuple.ml \
asm.mli asm.ml virtual.mli virtual.ml \
simm.mli simm.ml regAlloc.mli regAlloc.ml \
aS.ml block.ml liveness.ml \
graph.mli graph.ml \
coloring.ml regAlloc2.ml \
toAsm.ml \
emit.mli emit.ml \
main.mli main.ml

SOURCES = $(patsubst %,src/%,$(ML_SOURCES))

include OCamlMakefile
