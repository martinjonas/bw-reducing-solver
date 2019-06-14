(set-logic BV)

(declare-const z (_ BitVec 32))
(assert
 (forall ((x (_ BitVec 32)))
         (= (_ bv0 32) (bvmul z x))

         ))
(check-sat)
