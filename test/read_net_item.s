	.globl  :main
label	:main # main entry point
   # main program start
	li	v1, 10
	move	a0, v1
	sw	ra, 1, sp
	addi	sp, sp, 2
	jal	:read_net_item_12
	subi	sp, sp, 2
	lw	ra, 1, sp
   # main program end
label	:end_loop
	j	:end_loop
label	:read_net_item_12
	sw	v1, 0, sp
	sw	v1, 1, sp
	sw	v1, 2, sp
	read	at	#read_int
	sll	at, at, 8
	read	at
	sll	at, at, 8
	read	at
	sll	at, at, 8
	read	at
	move	v0, at
	li	at, -1
	bne	k0, at, :beq_else_29
	addi	k1, a0, 1
	li	v1, -1
	move	a1, v1
	move	a0, k1
	j	:min_caml_create_array
label	:beq_else_29
	addi	v1, a0, 1
	sw	k0, 3, sp
	sw	a0, 4, sp
	move	a0, v1
	sw	ra, 5, sp
	addi	sp, sp, 6
	jal	:read_net_item_12
	subi	sp, sp, 6
	lw	ra, 5, sp
	move	v1, v0
	addi	k1, a0, 0
	add	at, v1, k1
	sw	k0, 0, at
	move	v0, v1
	jr	ra
