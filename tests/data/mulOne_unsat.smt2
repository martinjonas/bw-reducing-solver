(set-logic BV)

(assert
 (exists ((x (_ BitVec 32)))
         (forall ((y (_ BitVec 32)))
                 (= (_ bv1 32) (bvmul x y))
                 )
         )
 )
(check-sat)
