(set-info :smt-lib-version 2.6)
(set-logic BV)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: bouncing-ball, node 5810 For more info see: No further information available.

Translated to BV by Mathias Preiner.
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status sat)
(declare-fun v () (_ BitVec 32))
(declare-fun g () (_ BitVec 32))
(declare-fun tuscore2dollarskuscore2 () (_ BitVec 32))
(declare-fun huscore2dollarskuscore2 () (_ BitVec 32))
(declare-fun t () (_ BitVec 32))
(declare-fun V () (_ BitVec 32))
(declare-fun c () (_ BitVec 32))
(declare-fun t1uscore0dollarskuscore2 () (_ BitVec 32))
(declare-fun vuscore2dollarskuscore2 () (_ BitVec 32))
(declare-fun h () (_ BitVec 32))
(declare-fun ts1uscore2 () (_ BitVec 32))
(assert (not (exists ((ts1uscore2 (_ BitVec 32))) (let ((?v_0 (bvsdiv g (_ bv2 32))) (?v_1 (bvneg g)) (?v_2 (bvadd t1uscore0dollarskuscore2 tuscore2dollarskuscore2))) (=> (and (and (and (and (and (and (and (and (and (and (and (and (=> (and (bvsle (_ bv0 32) ts1uscore2) (bvsle ts1uscore2 t1uscore0dollarskuscore2)) (bvsge (bvmul (bvsdiv (_ bv1 32) (_ bv2 32)) (bvadd (bvadd (bvmul (_ bv2 32) huscore2dollarskuscore2) (bvmul (bvmul (bvneg (_ bv1 32)) g) (bvmul ts1uscore2 ts1uscore2))) (bvmul (bvmul (_ bv2 32) ts1uscore2) vuscore2dollarskuscore2))) (_ bv0 32))) (bvsge t1uscore0dollarskuscore2 (_ bv0 32))) (= huscore2dollarskuscore2 (bvadd (bvmul ?v_0 (bvmul tuscore2dollarskuscore2 tuscore2dollarskuscore2)) (bvmul vuscore2dollarskuscore2 tuscore2dollarskuscore2)))) (bvsge huscore2dollarskuscore2 (_ bv0 32))) (bvsge tuscore2dollarskuscore2 (_ bv0 32))) (bvsle vuscore2dollarskuscore2 (bvadd (bvmul ?v_1 tuscore2dollarskuscore2) V))) (bvsgt g (_ bv0 32))) (bvsle (_ bv0 32) c)) (bvslt c (_ bv1 32))) (= h (bvadd (bvmul ?v_0 (bvmul t t)) (bvmul v t)))) (bvsge h (_ bv0 32))) (bvsge t (_ bv0 32))) (bvsle v (bvadd (bvmul ?v_1 t) V))) (or (bvsgt ?v_2 (_ bv0 32)) (bvsge ?v_2 (_ bv0 32))))))))
(check-sat)
(exit)
