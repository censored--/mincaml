	.globl  :main
label	:main # main entry point
   # main program start
	li	v0, 1
	li	v1, 2
	li	a0, 3
	li	a1, 4
	li	a2, 5
	li	a3, 6
	li	t0, 7
	li	t1, 8
	li	t2, 9
	li	t3, 0
	li	t4, 1
	li	t5, 2
	li	t6, 3
	li	t7, 4
	li	s0, 5
	li	s1, 6
	li	s2, 7
	li	s3, 8
	li	s4, 9
	li	s5, 0
	move	s7, s5
	move	s6, s4
	move	s5, s3
	move	s4, s2
	move	s3, s1
	move	s2, s0
	move	s1, t7
	move	s0, t6
	move	t7, t5
	move	t6, t4
	move	t5, t3
	move	t4, t2
	move	t3, t1
	move	t2, t0
	move	t1, a3
	move	t0, a2
	move	a3, a1
	move	a2, a0
	move	a1, v1
	move	a0, v0
	sw	ra, 1, sp
	addi	sp, sp, 2
	jal	:dummyfun_67
	subi	sp, sp, 2
	lw	ra, 1, sp
	move	a0, v0
	sw	ra, 1, sp
	addi	sp, sp, 2
	jal	:min_caml_print_int
	subi	sp, sp, 2
	lw	ra, 1, sp
   # main program end
label	:end_loop
	j	:end_loop
label	:dummyfun2_57
	add	v0, a0, a1
	add	v0, v0, a2
	add	v0, v0, a3
	add	v0, v0, t0
	add	v0, v0, t1
	add	v0, v0, t2
	add	v0, v0, t3
	add	v0, v0, t4
	jr	ra
label	:dummyfun_67
	sw	s5, 0, sp
	sw	s4, 1, sp
	sw	s3, 2, sp
	sw	s2, 3, sp
	sw	s1, 4, sp
	sw	s0, 5, sp
	sw	t9, 6, sp
	sw	t8, 7, sp
	sw	t7, 8, sp
	sw	t6, 9, sp
	sw	t5, 10, sp
	sw	t4, 11, sp
	sw	t3, 12, sp
	sw	t2, 13, sp
	sw	t1, 14, sp
	sw	t0, 15, sp
	sw	a3, 16, sp
	sw	a2, 17, sp
	sw	a1, 18, sp
	sw	a0, 19, sp
	read	at	#read_int
	sll	at, at, 8
	read	at
	sll	at, at, 8
	read	at
	sll	at, at, 8
	read	at
	move	v0, at
	sw	v0, 20, sp
	read	at	#read_int
	sll	at, at, 8
	read	at
	sll	at, at, 8
	read	at
	sll	at, at, 8
	read	at
	move	v0, at
	sw	v0, 21, sp
	read	at	#read_int
	sll	at, at, 8
	read	at
	sll	at, at, 8
	read	at
	sll	at, at, 8
	read	at
	move	v0, at
	sw	v0, 22, sp
	read	at	#read_int
	sll	at, at, 8
	read	at
	sll	at, at, 8
	read	at
	sll	at, at, 8
	read	at
	move	v0, at
	sw	v0, 23, sp
	read	at	#read_int
	sll	at, at, 8
	read	at
	sll	at, at, 8
	read	at
	sll	at, at, 8
	read	at
	move	v0, at
	sw	v0, 24, sp
	read	at	#read_int
	sll	at, at, 8
	read	at
	sll	at, at, 8
	read	at
	sll	at, at, 8
	read	at
	move	v0, at
	sw	v0, 25, sp
	read	at	#read_int
	sll	at, at, 8
	read	at
	sll	at, at, 8
	read	at
	sll	at, at, 8
	read	at
	move	v0, at
	sw	v0, 26, sp
	read	at	#read_int
	sll	at, at, 8
	read	at
	sll	at, at, 8
	read	at
	sll	at, at, 8
	read	at
	move	v0, at
	sw	v0, 27, sp
	read	at	#read_int
	sll	at, at, 8
	read	at
	sll	at, at, 8
	read	at
	sll	at, at, 8
	read	at
	move	v0, at
	move	t2, v0
	lw	v0, 20, sp
	lw	v1, 21, sp
	lw	a0, 22, sp
	lw	a1, 23, sp
	lw	a2, 24, sp
	lw	a3, 25, sp
	lw	t0, 26, sp
	lw	t1, 27, sp
	move	t4, t2
	move	t3, t1
	move	t2, t0
	move	t1, a3
	move	t0, a2
	move	a3, a1
	move	a2, a0
	move	a1, v1
	move	a0, v0
	sw	ra, 29, sp
	addi	sp, sp, 30
	jal	:dummyfun2_57
	subi	sp, sp, 30
	lw	ra, 29, sp
	lw	v1, 18, sp
	lw	a0, 19, sp
	add	v1, a0, v1
	lw	a0, 17, sp
	add	v1, v1, a0
	lw	a0, 16, sp
	add	v1, v1, a0
	lw	a0, 15, sp
	add	v1, v1, a0
	lw	a0, 14, sp
	add	v1, v1, a0
	lw	a0, 13, sp
	add	v1, v1, a0
	lw	a0, 12, sp
	add	v1, v1, a0
	lw	a0, 11, sp
	add	v1, v1, a0
	lw	a0, 10, sp
	add	v1, v1, a0
	lw	a0, 9, sp
	add	v1, v1, a0
	lw	a0, 8, sp
	add	v1, v1, a0
	lw	a0, 7, sp
	add	v1, v1, a0
	lw	a0, 6, sp
	add	v1, v1, a0
	lw	a0, 5, sp
	add	v1, v1, a0
	lw	a0, 4, sp
	add	v1, v1, a0
	lw	a0, 3, sp
	add	v1, v1, a0
	lw	a0, 2, sp
	add	v1, v1, a0
	lw	a0, 1, sp
	add	v1, v1, a0
	lw	a0, 0, sp
	add	v1, v1, a0
	add	v0, v1, v0
	jr	ra
