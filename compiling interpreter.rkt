#lang plai
;STEP 3
#|
(define-type CFAE-Value
  [numV (n number?)]
  [closureV (body CFAE?)
            (ds (listof CFAE-Value?))])

(define-type CFAE
  [cnum (n number?)]
  [cadd (lhs CFAE?)
       (rhs CFAE?)]
  [csub (lhs CFAE?)
       (rhs CFAE?)]
  [cid (pos number?)]
  [cfun (body CFAE?)]
  [capp (fun-expr CFAE?)
        (argl CFAE?)])

(define-type CFAE-Cont
  [mtK]
  [addSecondK (r CFAE?) (ds (listof CFAE-Value?)) (k CFAE-Cont?)]
  [doAddK     (v CFAE-Value?) (k CFAE-Cont?)]
  [subSecondK (r CFAE?) (ds (listof CFAE-Value?)) (k CFAE-Cont?)]
  [doSubK (v CFAE-Value?) (k CFAE-Cont?)]
  [appArgK (a CFAE?) (ds (listof CFAE-Value?)) (k CFAE-Cont?)]
  [doAppK (v CFAE-Value?) (k CFAE-Cont?)])

; initialization for interp and continue
(define cfae-reg (cnum 0))
(define k-reg (mtK))
(define v-reg (numV 0))
(define ds-reg empty)

; interp : -> CFAE-Value
(define (interp)
  (type-case CFAE cfae-reg
    [cnum (n)   (begin (set! v-reg (numV n))
                       (continue))]
    [cadd (l r) (begin (set! cfae-reg l)
                       (set! k-reg (addSecondK r ds-reg k-reg))
                       (interp))]
    [csub (l r) (begin (set! cfae-reg l)
                       (set! k-reg (subSecondK r ds-reg k-reg))
                       (interp))]
    [cid (pos)  (begin (set! v-reg (list-ref ds-reg pos))
                       (continue))]
    [cfun (body)  (begin (set! v-reg (closureV body ds-reg))
                         (continue))]
    [capp (fe ae) (begin (set! cfae-reg fe)
                         (set! k-reg (appArgK ae ds-reg k-reg))
                         (interp))]))

;; num-op : (number number -> number) -> (KCFAE-Value KCFAE-Value -> KCFAE-Value)
; making binary operation on two numbers
(define (num-op op op-name)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))

(define num+ (num-op + '+))
(define num- (num-op - '-))

; continue : CFAE-Cont CFAE-Value -> CFAE-Value
(define (continue)
  (type-case CFAE-Cont k-reg
    [mtK () v-reg]
    [addSecondK (r ds k1) (begin (set! cfae-reg r)
                                 (set! ds-reg ds)
                                 (set! k-reg (doAddK v-reg k1))
                                 (interp))]
    [doAddK (v1 k1) (begin (set! v-reg (num+ v1 v-reg))
                                 (set! k-reg k1)
                                 (continue))]
    [subSecondK (r ds k1) (begin (set! cfae-reg r)
                                 (set! ds-reg ds)
                                 (set! k-reg (doSubK v-reg k1))
                                 (interp))]
    [doSubK (v1 k1) (begin (set! v-reg (num- v1 v-reg))
                                 (set! k-reg k1)
                                 (continue))]
    [appArgK (a ds k1) (begin (set! cfae-reg a)
                                 (set! ds-reg ds)
                                 (set! k-reg (doAppK v-reg k1))
                                 (interp))]
    [doAppK (fun-val k)
            (begin (set! cfae-reg (closureV-body fun-val))
                                 (set! k-reg k)
                                 (set! ds-reg (cons v-reg (closureV-ds fun-val)))
                                 (interp))]))

(define-type CDefrdSub
  [mtCSub]
  [aCSub (name symbol?)
        (rest CDefrdSub?)])

; run : string -> (or number ’closure)
;; evaluate a CFAE program contained in a string
(define (run str)
  (begin
    (set! cfae-reg str)
    (set! k-reg (mtK))
    (set! v-reg (numV 0))
    (set! ds-reg empty)
    (type-case CFAE-Value (interp)
               [numV (n) n]
               [closureV (b ds) 'closure])))

(run (capp (capp (capp (cfun (cfun (cfun (cadd (cid 0) (cadd (cid 1) (cid 2)))))) (cnum 10)) (cnum 7))
                     (cnum 13)))


|#

;; ---------------------------------------- STEP 2
(define-type FAE
  [num (n number?)]
  [add (lhs FAE?)
       (rhs FAE?)]
  [sub (lhs FAE?)
       (rhs FAE?)]
  [id (name symbol?)]
  [fun (param symbol?)
       (body FAE?)]
  [app (fun-expr FAE?)
       (argl FAE?)])

(define-type CFAE-Value
  [numV (n number?)]
  [closureV (body CFAE?)
            (ds (listof CFAE-Value?))])

(define-type CFAE
  [cnum (n number?)]
  [cadd (lhs CFAE?)
       (rhs CFAE?)]
  [csub (lhs CFAE?)
       (rhs CFAE?)]
  [cid (pos number?)]
  [cfun (body CFAE?)]
  [capp (fun-expr CFAE?)
        (argl CFAE?)])

; compile : FAE CDefrdSub -> CFAE
(define (compile fae ds)
  ;(print fae)
  ;(print ds) (newline)
  (type-case FAE fae
    [num (n) (cnum n)]
    [add (l r) (cadd (compile l ds) (compile r ds))]
    [sub (l r) (csub (compile l ds) (compile r ds))]
    [id (name) (cid (locate name ds))]
    [fun (param body)
         (cfun (compile body (aCSub param ds)))]
    [app (fun-expr arg-expr) (capp (compile fun-expr ds) (compile arg-expr ds))]))

(define (locate name ds)
  (type-case CDefrdSub ds
    [mtCSub () (error 'locate "free variable")]
    [aCSub (sub-name rest-ds)
           (if (symbol=? sub-name name)
               0
               (+ 1 (locate name rest-ds)))]))

(define-type CDefrdSub
  [mtCSub]
  [aCSub (name symbol?)
        (rest CDefrdSub?)])

(define-type CFAE-Cont
  [mtK]
  [addSecondK (r CFAE?) (ds (listof CFAE-Value?)) (k CFAE-Cont?)]
  [doAddK     (v CFAE-Value?) (k CFAE-Cont?)]
  [subSecondK (r CFAE?) (ds (listof CFAE-Value?)) (k CFAE-Cont?)]
  [doSubK (v CFAE-Value?) (k CFAE-Cont?)]
  [appArgK (a CFAE?) (ds (listof CFAE-Value?)) (k CFAE-Cont?)]
  [doAppK (v CFAE-Value?) (k CFAE-Cont?)])

; interp : CFAE list-of-CFAE-Value CFAE-Cont -> CFAE-Value
(define (interp cfae ds k)
  (print "CFAE:") (print cfae) (newline)
  (print "list:") (print ds) (newline)
  (type-case CFAE cfae
    [cnum (n) (continue k (numV n))]
    [cadd (l r) (interp l ds (addSecondK r ds k))]
    [csub (l r) (interp l ds (subSecondK r ds k))]
    [cid (pos) (continue k (list-ref ds pos))] ;returns number
    [cfun (body-expr) (continue k (closureV body-expr ds))]
    [capp (fun-expr arg-expr) (interp fun-expr ds (appArgK arg-expr ds k))]))

; continue : CFAE-Cont CFAE-Value -> CFAE-Value
(define (continue k v)
  (print "k:")(print k) (newline)
  (print "v:") (print v) (newline)
  (type-case CFAE-Cont k
    [mtK () v]
    [addSecondK (r ds k1) (interp r ds (doAddK v k1))]
    [doAddK (v1 k1) (continue k1 (num+ v1 v))]
    [subSecondK (r ds k1) (interp r ds (doSubK v k1))]
    [doSubK (v1 k1) (continue k1 (num- v1 v))]
    [appArgK (a ds k1) (interp a ds (doAppK v k1))]
    [doAppK (fun-val k)
            (interp (closureV-body fun-val)
                    (cons v (closureV-ds fun-val))
                    k)]))


;; num-op : (number number -> number) -> (KCFAE-Value KCFAE-Value -> KCFAE-Value)
; making binary operation on two numbers
(define (num-op op op-name)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))

(define num+ (num-op + '+))
(define num- (num-op - '-))
  


(interp (compile (app
 (app (app (fun 'x (fun 'y (fun 'z (add (id 'z) (add (id 'y) (id 'x)))))) (num 10)) (num 7))
 (num 13)) (mtCSub)) '() (mtK))

(compile (app
 (app (app (fun 'x (fun 'y (fun 'z (add (id 'z) (add (id 'y) (id 'x)))))) (num 10)) (num 7))
 (num 13)) (mtCSub))

#|

;; ---------------------------------------- STEP 1
(define-type FAE
  [num (n number?)]
  [add (lhs FAE?)
       (rhs FAE?)]
  [sub (lhs FAE?)
       (rhs FAE?)]
  [id (name symbol?)]
  [fun (param symbol?)
       (body FAE?)]
  [app (fun-expr FAE?)
       (argl FAE?)])

(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?)
        (value FAE-Value?)
        (rest DefrdSub?)])

(define-type FAE-Value
  [numV (n number?)]
  [closureV (param symbol?)
            (body FAE?)
            (sc DefrdSub?)])

;lookup: symbol DefrdSub -> KCFAE-Value
; look for a value in DefrdSub for given symbol
(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub  (x val rest) 
           (if (symbol=? name x)   
               val
               (lookup name rest))]))

;; num-op : (number number -> number) -> (KCFAE-Value KCFAE-Value -> KCFAE-Value)
; making binary operation on two numbers
(define (num-op op op-name)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))

(define num+ (num-op + '+))
(define num- (num-op - '-))

;; interp : KCFAE DefrdSub (KCFAE-Value -> alpha) -> alpha
; interpreting KCFAEs
(define (interp a-fae ds k)
  (type-case FAE a-fae
    [num (n) (continue k (numV n))]
    [add (l r) (interp l ds (addSecondK r ds k))]
    [sub (l r) (interp l ds (subSecondK r ds k))]
    [id (name) (continue k (lookup name ds))]
    [fun (param body-expr) (continue k (closureV param body-expr ds))]
    [app (fun-expr arg-expr) (interp fun-expr ds (appArgK arg-expr ds k))]))

; continue : FAE-Cont FAE-Value -> FAE-Value
(define (continue k v)
  (type-case FAE-Cont k
    [mtK () v]
    [addSecondK (r ds k1) (interp r ds (doAddK v k1))]
    [doAddK (v1 k1) (continue k1 (num+ v1 v))]
    [subSecondK (r ds k1) (interp r ds (doSubK v k1))]
    [doSubK (v1 k1) (continue k1 (num- v1 v))]
    [appArgK (a ds k1) (interp a ds (doAppK v k1))]
    [doAppK (f-val k1) (interp (closureV-body f-val) (aSub (closureV-param f-val) v (closureV-sc f-val)) k1)]))

(define-type FAE-Cont
  [mtK]
  [addSecondK (r FAE?) (ds DefrdSub?) (k FAE-Cont?)]
  [doAddK     (v FAE-Value?) (k FAE-Cont?)]
  [subSecondK (r FAE?) (ds DefrdSub?) (k FAE-Cont?)]
  [doSubK (v FAE-Value?) (k FAE-Cont?)]
  [appArgK (a FAE?) (ds DefrdSub?) (k FAE-Cont?)]
  [doAppK (v FAE-Value?) (k FAE-Cont?)])

(interp (add (num 3) (num 2)) (mtSub) (mtK))
(interp (fun 'x (sub (id 'x) (num 4))) (mtSub) (mtK))
(interp (app (fun 'x (sub (id 'x) (num 4))) (num 2)) (mtSub) (mtK))

|#







