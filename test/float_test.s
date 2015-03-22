	.globl  :main
label	:main # main entry point
   # main program start
	sw	ra, 1, sp
	addi	sp, sp, 2
	jal	:min_caml_read_float
	subi	sp, sp, 2
	lw	ra, 1, sp
	fmov	f30, f0
	la	at, 1073741824 #2.000000
	mtc1	at, f31
	swc1	f31, 0, sp
	fmov	f1, f31
	fmov	f0, f30
	sw	ra, 1, sp
	addi	sp, sp, 2
	jal	:f_5
	subi	sp, sp, 2
	lw	ra, 1, sp
	fmov	f31, f0
	fmov	f0, f31
	sw	ra, 1, sp
	addi	sp, sp, 2
	jal	:min_caml_print_float
	subi	sp, sp, 2
	lw	ra, 1, sp
   # main program end
label	:end_loop
	j	:end_loop
label	:f_5
	fmul	f31, f0, f1
	fadd	f0, f0, f31
	jr	ra
