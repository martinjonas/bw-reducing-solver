(set-logic BV)

(assert
 (forall ((x (_ BitVec 32)))
         (exists ((y (_ BitVec 32)))
                 (distinct (_ bv0 32) (bvadd x y))
                 )
         )
 )
(check-sat)
