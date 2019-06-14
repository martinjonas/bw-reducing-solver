(set-logic BV)

(assert
 (forall ((x (_ BitVec 32)))
         (exists ((y (_ BitVec 32)))
                 (= (_ bv1 32) (bvmul x y))
                 )
         )
 )
(check-sat)
