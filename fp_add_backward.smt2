; EXPECT: unsat
; COMMAND-LINE: --cegqi-si=all --sygus-out=status
(set-option :produce-models true)

(set-logic FP)

;(define-sort MyFloat () Float32)
(define-sort MyFloat () (_ FloatingPoint 4 8))


(define-fun lower ((x MyFloat) (z MyFloat)) MyFloat
     (fp.sub RNE (fp.sub RTN z (fp #b0 #b0000 #b0000001)) x) )


(declare-fun x () MyFloat)
(declare-fun z () MyFloat)
(declare-fun a () MyFloat)
(declare-fun b () MyFloat)




(assert (not (and
             (=> (and (not (fp.isInfinite z)) (not (fp.isInfinite x)) (fp.leq a x) (fp.leq z (fp.add RNE a b)))
                  (fp.leq (lower x z) b))
             (not (fp.isInfinite (lower (_ +zero 4 8) (_ +zero 4 8))))
             (not (= (fp #b1 #b1110 #b1111111) (lower (_ +zero 4 8) (_ +zero 4 8))))
             (fp.leq (fp #b1 #b0001 #b0000000) (lower (_ +zero 4 8) (_ +zero 4 8)))
             (fp.leq (lower (_ +zero 4 8) (_ +zero 4 8)) (fp #b0 #b0001 #b0000000))
)))

(check-sat)
(get-value (x z a b (fp.add RNE a b) (fp.sub RTN z (fp #b0 #b0000 #b0000001)) (lower x z) (fp.sub RNE (fp.add RNE a b) a)))

;((fp.add roundNearestTiesToEven a b)                                   (fp #b0 #b0111 #b1001000))
;(z                                                                     (fp #b0 #b0111 #b0010001));
;((fp.sub roundTowardNegative z (fp (_ bv0 1) (_ bv0 4) (_ bv1 7)))     (fp #b0 #b0111 #b0010000))
;(a                                                                     (fp #b0 #b0111 #b0111001))
;(x                                                                     (fp #b0 #b0111 #b0000000))
;((lower x z)                                                           (fp #b0 #b0100 #b0000000)))
;(b                                                                     (fp #b0 #b0011 #b1110000))
;((fp.sub roundNearestTiesToEven (fp.add roundNearestTiesToEven a b) a) (fp #b0 #b0011 #b1110000))
