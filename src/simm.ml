open Asm

let rec is_two_pow x = match x with
  |0->false
  |1->true
  |_->if x mod 2 = 0 then is_two_pow (x/2) else false

let rec log2 x = if x <= 0 then assert false else
  match x with
  |1->0
  |_->if x mod 2 = 0 then 1 + log2 (x/2) else assert false

let rec g env = function (* 命令列の 16 bit 即値最適化 *)
  | Ans(exp) -> Ans(g' env exp)
  | Let((x, t), Li(i), e) when (-32768 <= i) && (i < 32768) ->
      let e' = g (M.add x i env) e in
      if List.mem x (fv e') then Let((x, t), Li(i), e') else e'
  | Let(xt, Add(y, C(i)), e) when M.mem y env -> (* for array access *)
      g env (Let(xt, Li((M.find y env) lsl i), e))
  | Let(xt, exp, e) -> Let(xt, g' env exp, g env e)
and g' env = function (* 各命令の 16 bit 即値最適化 *)
  | Add(x, V(y)) when M.mem y env -> Add(x, C(M.find y env))
  | Add(x, V(y)) when M.mem x env -> Add(y, C(M.find x env))
  | Sub(x, V(y)) when M.mem y env -> Sub(x, C(M.find y env))
  | Mul(x, V(y)) when M.mem y env -> 
     let y' = M.find y env in 
     if is_two_pow y' then Sll(x, C(log2 y')) else Mul(x, C(M.find y env))
  | Mul(x, V(y)) when M.mem x env ->
     let x' = M.find x env in 
     if is_two_pow x' then Sll(y, C(log2 x')) else Mul(y, C(M.find x env))
  | Sll(x, V(y)) when M.mem y env -> Sll(x, C(M.find y env))
  | Sll(x, V(y)) when M.mem x env -> Sll(y, C(M.find x env))
  | Srl(x, V(y)) when M.mem y env -> Srl(x, C(M.find y env))
  | Srl(x, V(y)) when M.mem x env -> Srl(y, C(M.find x env))
  | Sra(x, V(y)) when M.mem y env -> Sra(x, C(M.find y env))
  | Sra(x, V(y)) when M.mem x env -> Sra(y, C(M.find x env))
  | Div(x, V(y)) when M.mem y env ->
     let y' = M.find y env in 
     if is_two_pow y' then Sra(x, C(log2 y')) else Div(x, C(M.find y env))
  | Slw(x, V(y)) when M.mem y env -> Slw(x, C(M.find y env))
  | Lw(x, V(y)) when M.mem y env -> Lw(x, C(M.find y env))
  | Sw(x, y, V(z)) when M.mem z env -> Sw(x, y, C(M.find z env))
  | Lfd(x, V(y)) when M.mem y env -> Lfd(x, C(M.find y env))
  | Stfd(x, y, V(z)) when M.mem z env -> Stfd(x, y, C(M.find z env))
  | IfEq(x, V(y), e1, e2) when M.mem y env -> 
      IfEq(x, C(M.find y env), g env e1, g env e2)
  | IfLE(x, V(y), e1, e2) when M.mem y env ->
      IfLE(x, C(M.find y env), g env e1, g env e2)
  | IfGE(x, V(y), e1, e2) when M.mem y env -> 
      IfGE(x, C(M.find y env), g env e1, g env e2)
  | IfEq(x, V(y), e1, e2) when M.mem x env -> 
      IfEq(y, C(M.find x env), g env e1, g env e2)
  | IfLE(x, V(y), e1, e2) when M.mem x env -> 
      IfGE(y, C(M.find x env), g env e1, g env e2)
  | IfGE(x, V(y), e1, e2) when M.mem x env -> 
      IfLE(y, C(M.find x env), g env e1, g env e2)
  | IfEq(x, y', e1, e2) -> IfEq(x, y', g env e1, g env e2)
  | IfLE(x, y', e1, e2) -> IfLE(x, y', g env e1, g env e2)
  | IfGE(x, y', e1, e2) -> IfGE(x, y', g env e1, g env e2)
  | IfFEq(x, y, e1, e2) -> IfFEq(x, y, g env e1, g env e2)
  | IfFLE(x, y, e1, e2) -> IfFLE(x, y, g env e1, g env e2)
  | e -> e

(* トップレベル関数の 16 bit 即値最適化 *)
let h { name = l; args = xs; fargs = ys; body = e; ret = t} = 
  { name = l; args = xs; fargs = ys; body = g M.empty e; ret = t}

(* プログラム全体の 16 bit 即値最適化 *)
let f (Prog(fundefs, e)) = 
  Prog(List.map h fundefs, g M.empty e)
