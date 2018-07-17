; EXPECT: unsat
; COMMAND-LINE: --cegqi-si=all --sygus-out=status
(set-option :produce-models true)

(set-logic FP)

;(define-sort MyFloat () Float32)
(define-sort MyFloat () (_ FloatingPoint 4 8))


(define-fun lower ((rne RoundingMode) (x MyFloat) (y MyFloat)) MyFloat (fp.add rne x y))


(declare-fun x () MyFloat)
(declare-fun y () MyFloat)
(declare-fun a () MyFloat)
(declare-fun b () MyFloat)


(assert (not (=> (and (not (fp.isInfinite y)) (not (fp.isInfinite x)) (fp.leq x a) (fp.leq y b))
        (fp.leq (lower RNE x y) (fp.add RNE a b)))))


(check-sat)
(get-model)
