

(declare-datatypes () (
  (Nat zero
       (succ (nat Nat)))

  (Type 
     rvalue
     rinteger
     rnum
     rreal
     rboolean
     )
))



(declare-fun subtype (Type Type) Bool)

(assert (subtype rinteger rnum))
(assert (subtype rreal rnum))
(assert (subtype rboolean rvalue))
(assert (subtype rnum rvalue))


;; reflexive
(assert (forall ((x Type)) (subtype x x)))

;; trans
(assert (forall ((x Type) (y Type) (z Type))
          (=> (and (subtype x y) (subtype y z)) 
              (subtype x z)))) 

;; anti-symmetry
(assert (forall ((x Type) (y Type))
          (=> (and (subtype x y) (subtype y x)) 
              (= x y))))

;; 
(assert (forall ((x Type) (y Type) (z Type))
          (=> (and (subtype x y) (subtype x z)) 
              (or (subtype y z) (subtype z y))))) 



(assert (forall ((x Type)) (subtype x rvalue)))
(check-sat)
(get-model)

