# Sumii's Makefile for Min-Caml (for GNU Make)
# 
# ack.mlなどのテストプログラムをtest/に用意してmake do_testを実行すると、
# min-camlとocamlでコンパイル・実行した結果を自動で比較します。

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
## [自分（住井）用の注]
## ・OCamlMakefileや古いGNU Makeのバグ(?)で上のような定義が必要(??)
## ・OCamlMakefileではdebug-codeとnative-codeのそれぞれで
##   .mliがコンパイルされてしまうので、両方ともdefault:の右辺に入れると
##   再make時に（.mliが変更されているので）.mlも再コンパイルされる
clean:: nobackup

# ↓もし実装を改造したら、それに合わせて変える
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
