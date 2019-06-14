(set-logic BV)

(assert
 (exists ((x (_ BitVec 32)))
         (forall ((y (_ BitVec 32)))
                 (= (_ bv0 32) (bvadd x y))
                 )
         )
 )
(check-sat)
