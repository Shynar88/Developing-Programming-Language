#lang plai

;; BFAE abstract syntax trees
(define-type BFAE
  [num  (n number?)]
  [add  (lhs BFAE?) (rhs BFAE?)]
  [sub  (lhs BFAE?) (rhs BFAE?)]
  [id   (name symbol?)]
  [fun (name symbol?) (body BFAE?)]
  [app  (ftn BFAE?) (arg BFAE?)]
  [newbox (box BFAE?)]
  [setbox (box BFAE?) (val BFAE?)]
  [openbox (val BFAE?)]
  [rec (lst (listof mypair?))]
  [get (b BFAE?) (s symbol?)]
  [setB (r BFAE?) (s symbol?) (e BFAE?)]
  [seqn (lpr (listof BFAE?))])

(define-type Mpair
  [mypair (s symbol?) (b BFAE?)])

(define-type Fipair
  [fpair (s symbol?) (b v*s?)])


(define-type DefrdSub
  [mtSub]
  [aSub (name symbol?) (value BFAE-Value?) (ds DefrdSub?)])

(define-type BFAE-Value
  [numV (n number?)]
  [closureV (param symbol?)
            (body BFAE?)
            (ds DefrdSub?)]
  [boxV (address integer?)]
  [recordV (lst (listof fpair?))])


(define-type Store
  [mtSto]
  [aSto (address integer?) (value BFAE-Value?)
        (rest Store?)])


(define-type Value*Store
  [v*s (value BFAE-Value?) (store Store?)])

; parse: sexpr -> BFAE
;; to convert s-expressions into BFAEs
(define (parse sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse l) (parse r))]
    [(list '- l r) (sub (parse l) (parse r))]
    [(? symbol?) (id sexp)]
    [(list 'fun p b) (fun (first p) (parse b))]
    [(list 'seqn exp ...) (seqn (map (lambda (i)
                                             (parse i))
                                           exp))]
    [(list 'newbox bx) (newbox (parse bx))]
    [(list 'openbox bx) (openbox (parse bx))]
    [(list 'setbox bx v) (setbox (parse bx) (parse v))]
    [(list 'rec ls ...) (if (check-duplicates ls #:key car)
                            (error 'parse "duplicate fields")
                         (rec (map (lambda (i)
                                        (mypair (first i) (parse (second i))))
                                    ls)))]
    [(list 'get b s) (get (parse b) s)]
    [(list 'set r s e) (setB (parse r) s (parse e))]
    [(list f a) (app (parse f) (parse a))]
    [else (error 'parse "bad syntax: ~a" sexp)]))

; malloc : Store -> integer
; gives available address in storage
(define (malloc st)
  (+ 1 (max-address st)))

; max-address : Store -> integer
;gives highest number of occupied place in memory 
(define (max-address st)
  (type-case Store st
    [mtSto () 0]
    [aSto (n v st)
          (max n (max-address st))]))

; num+: BFAE BFAE -> BFAE
;sums two numbers 
(define (num+ x y)
  (numV (+ (numV-n x) (numV-n y))))

; num-: BFAE BFAE -> BFAE
;substracts two numbers
(define (num- x y)
  (numV (- (numV-n x) (numV-n y))))

; interp-two : BFAE BFAE DefrdSub Store
;              (Value Value Store -> Value*Store)
;              -> Value*Store
;interprets two expressions one after another and passing possibly changed store 
(define (interp-two expr1 expr2 ds st handle)
  (type-case Value*Store (interp expr1 ds st)
    [v*s (val1 st2)
         [type-case Value*Store (interp expr2 ds st2)
           [v*s (val2 st3)
                (handle val1 val2 st3)]]]))

; lookup : symbol DefrdSub -> BFAE-Value
; look for a value in DefrdSub for identifier
(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub    (sub-name val rest-ds)
             (if (symbol=? sub-name name)
                 val  ;it will output recordV
                 (lookup name rest-ds))]))

; store-lookup : integer Store -> BFAE-Value
;returns a value stored in certain address
(define (store-lookup adr st)
  ;(display "case:")(newline)
  ;(display st)(newline)
  (type-case Store st
    [mtSto () (error "unallocated")] 
    [aSto (ad v rst)
          (if (equal? ad adr)
          v
          (store-lookup adr rst))]))

;effstore: integer BFAE-Value Store -> Store
;takes store returns modified store
(define (effstore addr val st)
  (type-case Store st
    [mtSto () (error "unallocated")] 
    [aSto (ad v rst) (if (equal? ad addr)
                         (aSto addr val rst)
                         (aSto ad v (effstore addr val rst)))]))

;interpmany: (listof BFAE) DefrdSub Store -> Value*Store
;interprets sequence of expressions one after another and passing possibly changed store 
(define (interpmany lsexpr ds st)
  (local [(define val (interp (first lsexpr) ds st))]
  (if (empty? (rest lsexpr))
      val
  (interpmany (rest lsexpr) ds (v*s-store val)))))

;findrec: (listof fpair) symbol DefrdSub Store -> Value*Store
;returns interpreted value of needed record body expression
(define (findrec lfp s ds st)
  (if (empty? lfp)
      (error 'search "no such field")
      (if (equal? (fpair-s (first lfp)) s)
          (fpair-b (first lfp))
          (findrec (rest lfp) s ds st))))

;changerec: symbol BFAE-Value BFAE-Value -> (listof fpair)
;changing body of particular record
(define (changerec name lfp newval st)
  (if (equal? (fpair-s (first lfp)) name)
      (append (list (fpair name (v*s newval st))) (rest lfp))
      (append (list (first lfp)) (changerec name (rest lfp) newval st)))) 

;change: integer BFAE-Value symbol Store -> Store
;change a body of record inside of store
(define (change addr newval s st)
  ;(display st)(newline)
  (type-case Store st
    [mtSto () (error "unallocated")]
    [aSto (ad v rst) (if (equal? ad addr) 
                         (aSto addr (recordV (changerec s (recordV-lst v) newval rst)) rst) 
                         (aSto ad v (change addr newval s rst)))]))

;eval: (listof mypair) DefrdSub Store -> (listof fpair)
;interpreting listof mypair to lisotof fpair
(define (eval lsmp ds st)
  (map (lambda (i)
         (fpair (mypair-s i) (interp (mypair-b i) ds st)))
       lsmp))

; interp : BFAE DefrdSub Store -> Value*Store
; interpreting BFAEs
(define (interp expr ds st)
  (type-case BFAE expr
    [num (n) (v*s (numV n) st)]
    [add  (l r) (interp-two l r ds st
                            (lambda (v1 v2 st1) (v*s (num+ v1 v2) st1)))]
    [sub  (l r) (interp-two l r ds st
                            (lambda (v1 v2 st1) (v*s (num- v1 v2) st1)))]
    [id   (name) (v*s (lookup name ds) st)] 
    [fun (param body-expr) (v*s (closureV param body-expr ds) st)]
    [app (f a) 
         (type-case Value*Store (interp f ds st)
           [v*s (clsr st1)
                (local [(define val (interp a ds st1))] 
                (interp (closureV-body clsr)
                        (aSub (closureV-param clsr)
                              (v*s-value val)
                              (closureV-ds clsr))
                       (v*s-store val)
                        ))])]
    [seqn (lsexpr) (interpmany lsexpr ds st)]
    [rec (lsmpr) (local [(define a (malloc st))
                         (define fpl (eval lsmpr ds st))]
                     (v*s (boxV a)
                          (aSto a (recordV fpl) st)))] 
    [get (b s) (local [(define bxpair (interp b ds st))]
                 (type-case Value*Store bxpair
                   [v*s (bx str)
                        (local [(define rclfp (store-lookup (boxV-address bx) str))]
                          (findrec (recordV-lst rclfp) s ds str))]))] 
    [setB (r s e) (type-case Value*Store (interp r ds st)
                    [v*s (rc str)
                         (type-case Value*Store (interp e ds str)
                           [v*s (val str1)
                                (v*s val (change (boxV-address rc) val s str))])])] ;str1
                          ;(define newval (interp e ds (v*s-store bxr)))] 
                    ;(v*s (v*s-value newval)
                    ;     (effstore (boxV-address (v*s-value bxr)) (v*s-value newval) (v*s-store newval))))] 
    [newbox (val)
            (type-case Value*Store (interp val ds st)
              [v*s (vl st1)
                   (local [(define a (malloc st1))]
                     (v*s (boxV a)
                          (aSto a vl st1)))])]
    [openbox (bx-expr)
             (type-case Value*Store (interp bx-expr ds st)
               [v*s (bx-val st1)
                    (v*s (store-lookup (boxV-address bx-val)
                                       st1)
                         st1)])]
    [setbox (bx-expr val-expr)
            (interp-two bx-expr val-expr ds st
                        (lambda (bx-val val st1)
                          (v*s val
                               (effstore (boxV-address bx-val) val st1))))]))

; interp : BFAE -> integer or symbol
; interpreting BFAEs
(define (interp-expr prs)
  (local [(define res (interp prs (mtSub) (mtSto)))]
    (type-case BFAE-Value (v*s-value res)
      [numV (n) n]
      [closureV (p b ds) 'func]
      [boxV (add) (if (recordV? (store-lookup add (v*s-store res)))
                      'record
                      'box)]
      [recordV (lst) 'record])))

(test (interp (parse '{{fun {b} {seqn {setbox b {+ 2 (openbox b)}} {setbox b {+ 3 (openbox b)}} {setbox b {+ 4 (openbox b)}} {openbox b}}} {newbox 1}}) (mtSub) (mtSto)) (v*s (numV 10) (aSto 1 (numV 10) (mtSto))))
(test (interp (parse '{seqn {newbox 0} {setbox x 1} {openbox x}}) (aSub 'x (boxV 1) (mtSub)) (aSto 1 (numV 0) (mtSto))) (v*s (numV 1) (aSto 2 (numV 0) (aSto 1 (numV 1) (mtSto)))))
(test (interp (parse '{{fun {a} {{fun {b} {seqn {setbox b 2} {setbox a {fun {c} {+ c 1}}} {{openbox a} {openbox b}}}} {openbox a}}} {newbox {newbox 1}}}) (mtSub) (mtSto)) (v*s (numV 3) (aSto 2 (closureV 'c (add (id 'c) (num 1)) (aSub 'b (boxV 1) (aSub 'a (boxV 2) (mtSub)))) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{{fun {b} {openbox {setbox b b}}} {newbox 0}}) (mtSub) (mtSto)) (v*s (boxV 1) (aSto 1 (boxV 1) (mtSto))))
(test (interp (parse '{newbox {{fun {b} {setbox b 2}} {newbox 0}}}) (mtSub) (mtSto)) (v*s (boxV 2) (aSto 2 (numV 2) (aSto 1 (numV 2) (mtSto)))))
(test (interp-expr (parse '{{fun {r} {seqn {set r x 5} {get r x}}} {rec {x 1}}})) 5)
(test (interp (parse '{{fun {b} {openbox b}} {seqn {newbox 9} {newbox 10}}}) (mtSub) (mtSto)) (v*s (numV 10) (aSto 2 (numV 10) (aSto 1 (numV 9) (mtSto)))))
(test (interp-expr (parse '{{fun {r} {seqn {setbox {get r x} 2} {openbox {get r x}}}} {rec {x {newbox 0}}}})) 2)
(test (interp-expr (parse '{newbox 1})) 'box)
(test (interp-expr (parse '{{fun {r} {+ {get r x} {seqn {set r x 2}}}} {rec {z 3} {y 2} {x 1}}})) 3)
(test (interp-expr (parse '{rec})) 'record)
(test (interp (parse '{{fun {a} {{fun {b} {seqn {setbox b {- {openbox b} 1}} {setbox a {+ {openbox a} 1}} {newbox 0} {openbox b}}} {newbox 1}}} {newbox 2}}) (aSub 'a (boxV 0) (mtSub)) (mtSto)) (v*s (numV 0) (aSto 3 (numV 0) (aSto 2 (numV 0) (aSto 1 (numV 3) (mtSto))))))
(test (interp (parse '{seqn {newbox 1}}) (mtSub) (mtSto)) (v*s (boxV 1) (aSto 1 (numV 1) (mtSto))))
(test (interp-expr (parse '{{fun {r1} {{fun {r} {seqn {set r x 0} {get r1 x}}} {rec {x 1} {y 2}}}} {rec {x 3} {y 4}}})) 3)
(test (interp-expr (parse '{{fun {r} {seqn {setbox {get r x} 1} {get r y}}} {{fun {b} {rec {x b} {y {openbox b}}}} {newbox 0}}})) 0)
(test (interp (parse '{{openbox {{fun {b} {seqn {setbox b 2} {newbox {fun {a} {setbox a 3}}}}} {newbox 0}}} {newbox 1}}) (mtSub) (mtSto)) (v*s (numV 3) (aSto 3 (numV 3) (aSto 2 (closureV 'a (setbox (id 'a) (num 3)) (aSub 'b (boxV 1) (mtSub))) (aSto 1 (numV 2) (mtSto))))))
(test (interp (parse '{seqn 1 {fun {x} {+ x 1}} {newbox 2} {{fun {x} {setbox x {newbox 1}}} {newbox 3}}}) (mtSub) (mtSto)) (v*s (boxV 3) (aSto 3 (numV 1) (aSto 2 (boxV 3) (aSto 1 (numV 2) (mtSto))))))
(test (interp (parse '{{{fun {a} {fun {b} {setbox a 2}}} {newbox 1}} {newbox 0}}) (mtSub) (mtSto)) (v*s (numV 2) (aSto 2 (numV 0) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{{{fun {b} {fun {a} {openbox b}}} {newbox 9}} {newbox 10}}) (mtSub) (mtSto)) (v*s (numV 9) (aSto 2 (numV 10) (aSto 1 (numV 9) (mtSto)))))
(test (interp-expr (parse '{set {rec {x 1}} x 0})) 0)
(test (interp (parse '{{fun {b} {setbox b 2}} {seqn {newbox 0} {newbox 1}}}) (mtSub) (mtSto)) (v*s (numV 2) (aSto 2 (numV 2) (aSto 1 (numV 0) (mtSto)))))
(test (interp (parse '{{fun {b} {- {openbox b} {seqn {setbox b b} {setbox {openbox b} 1} {openbox b}}}} {newbox 0}}) (mtSub) (mtSto)) (v*s (numV -1) (aSto 1 (numV 1) (mtSto))))
(test (interp (parse '{{fun {b} {seqn {setbox b 2} {openbox b}}} {newbox 1}}) (mtSub) (mtSto)) (v*s (numV 2) (aSto 1 (numV 2) (mtSto))))
(test/exn (interp (parse '{openbox x}) (aSub 'x (boxV 1) (mtSub)) (mtSto))  "")
(test (interp (parse '{{fun {b} {seqn {setbox b 12} {openbox b}}} {newbox 10}}) (mtSub) (mtSto)) (v*s (numV 12) (aSto 1 (numV 12) (mtSto))))
(test (interp (parse '{setbox {{fun {b} {seqn {newbox b} {newbox b}}} 0} 1}) (mtSub) (mtSto)) (v*s (numV 1) (aSto 2 (numV 1) (aSto 1 (numV 0) (mtSto)))))
(test (interp (parse '{{fun {b} {setbox b 2}} {newbox 0}}) (mtSub) (aSto 1 (numV 0) (mtSto))) (v*s (numV 2) (aSto 2 (numV 2) (aSto 1 (numV 0) (mtSto)))))
(test (interp (parse '{+ {{fun {b} {setbox b 2}} {newbox 0}} {{fun {b} {setbox b 2}} {newbox 1}}}) (mtSub) (mtSto)) (v*s (numV 4) (aSto 2 (numV 2) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{seqn 1 2}) (mtSub) (mtSto)) (v*s (numV 2) (mtSto)))
(test (interp-expr (parse '{{fun {r} {get r x}} {rec {x 1}}})) 1)
(test (interp (parse '{{fun {b} {openbox b}} {newbox 10}}) (mtSub) (mtSto)) (v*s (numV 10) (aSto 1 (numV 10) (mtSto))))
(test (interp-expr (parse '{{fun {b} {seqn {setbox b 12} {openbox b}}} {newbox 10}})) 12)
(test (interp-expr (parse '{{fun {b} {seqn {set {openbox b} y {newbox {openbox b}}} {openbox {get {openbox b} y}}}} {newbox {rec {x 1} {y 2}}}})) 'record)
(test (interp-expr (parse '{{{{{fun {g} {fun {s} {fun {r1} {fun {r2} {+ {get r1 b} {seqn {{s r1} {g r2}} {+ {seqn {{s r2} {g r1}} {get r1 b}} {get r2 b}}}}}}}} {fun {r} {get r a}}} {fun {r} {fun {v} {set r b v}}}} {rec {a 0} {b 2}}} {rec {a 3} {b 4}}})) 5)
(test (interp-expr (parse '{{fun {r} {+ {setbox {get r x} 2} {openbox {get r x}}}} {rec {x {newbox 0}}}})) 4)
(test (interp-expr (parse '{fun {x} x})) 'func)
(test (interp-expr (parse '{{fun {b} {seqn {set {openbox b} y {newbox {openbox b}}} {get {openbox {get {openbox b} y}} y}}} {newbox {rec {x 1} {y 2}}}})) 'box)
(test (interp-expr (parse '{{fun {b} {{fun {a} {seqn {set a x {openbox b}} {setbox b 1} {set a y {openbox b}} {get a x}}} {rec {x 1} {y 2}}}} {newbox 0}})) 0)
(test (interp (parse '{openbox {{fun {b} {seqn {setbox b 2} {newbox {fun {a} {setbox a 3}}}}} {newbox 0}}}) (mtSub) (mtSto)) (v*s (closureV 'a (setbox (id 'a) (num 3)) (aSub 'b (boxV 1) (mtSub))) (aSto 2 (closureV 'a (setbox (id 'a) (num 3)) (aSub 'b (boxV 1) (mtSub))) (aSto 1 (numV 2) (mtSto)))))
(test (interp (parse '{{fun {b} {seqn {setbox b b} {openbox b}}} {newbox 0}}) (mtSub) (mtSto)) (v*s (boxV 1) (aSto 1 (boxV 1) (mtSto))))
(test (interp (parse '{{fun {b} {+ {openbox b} {seqn {setbox b 2} {openbox b}}}} {newbox 1}}) (mtSub) (mtSto)) (v*s (numV 3) (aSto 1 (numV 2) (mtSto))))
(test/exn (interp (parse '{get {rec {a 10}} b}) (mtSub) (mtSto)) "")
(test/exn (interp (parse '{get {rec {b 10} {b {+ 1 2}}} b}) (mtSub) (mtSto)) "")
(test/exn (interp (parse '{{fun {x} {get {rec {a x} {x a}} a}} 7}) (mtSub) (mtSto)) "")
(test (interp-expr (parse '{{fun {x} {rec {a x}}} {newbox 1}})) 'record)
(test (interp-expr (parse '{{fun {x} {{fun {r} {get r a}} {rec {a x}}}} {newbox 1}})) 'box)
(test (interp-expr (parse '{{fun {x} {{fun {r} {{fun {b} {openbox b}} {get r a}}} {rec {a x}}}} {newbox 1}})) 1)
(test (interp-expr (parse '{{fun {x} {{fun {r} {{fun {b} {seqn {openbox b} {setbox b 2} {openbox b}}} {get r a}}} {rec {a x}}}} {newbox 1}})) 2)
(test (interp-expr (parse '{{fun {x} {{fun {r} {{fun {b} {seqn {openbox b} {setbox b 2} {openbox b} {set r a 3} {get r a}}} {get r a}}} {rec {a x}}}} {newbox 1}})) 3)
(test (interp-expr (parse '{{fun {x} {{fun {r} {{fun {b} {seqn {openbox b} {setbox b 2} {openbox b} {set r a 3} {get r a} {openbox b}}} {get r a}}} {rec {a x}}}} {newbox 1}})) 2)




;mytests
(test/exn (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {set r x 3}
                                  {get r x}}}
                            {rec {x 1} {x 6}}})) "parse: duplicate fields")

(test (interp-expr (parse '{{fun {b}
    {seqn
        {setbox b {+ 4 {openbox b}}}
        {setbox b {+ 7 {openbox b}}}}}
                            {newbox 9}})) 20)

(test (interp-expr (parse '{rec {x 1}}))
      'record)

(test (interp (parse '{{fun {b} {seqn
                                 {setbox b 44}
                                 {openbox b}}}
                       {newbox 1}}) (mtSub) (mtSto))
      (v*s (numV 44)
           (aSto 1 (numV 44) (mtSto))))

(test (interp (parse '{{fun {b} {openbox b}}
                       {seqn
                        {newbox 5}
                        {newbox 9}}}) (mtSub) (mtSto))
      (v*s (numV 9)
           (aSto 2 (numV 9) (aSto 1 (numV 5) (mtSto)))))

(test (interp-expr (parse '{newbox 9}))
      'box)

(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {set r x 5}
                                  {get r x}}}
                            {rec {x 1} {y 2} {z 3}}}))
      5)
 
(test/exn (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {set r x 5}
                                  {get r y}}}
                            {rec {x 1}}}))
      "no such field")




;given tests
(test (interp (parse '{seqn 1 2})
              (mtSub)
              (mtSto))
      (v*s (numV 2) (mtSto)))

(test (interp (parse '{{fun {b} {openbox b}}
                       {newbox 10}})
              (mtSub)
              (mtSto))
      (v*s (numV 10)
           (aSto 1 (numV 10) (mtSto))))

(test (interp (parse '{{fun {b} {seqn
                                 {setbox b 12}
                                 {openbox b}}}
                       {newbox 10}})
              (mtSub)
              (mtSto))
      (v*s (numV 12)
           (aSto 1
                 (numV 12)
                 (mtSto))))

(test (interp-expr (parse '{{fun {b} {seqn
                                      {setbox b 12}
                                      {openbox b}}}
                            {newbox 10}}))
      12)

(test (interp (parse '{{fun {b} {openbox b}}
                       {seqn
                        {newbox 9}
                        {newbox 10}}})
              (mtSub)
              (mtSto))
      (v*s (numV 10)
           (aSto 2 (numV 10)
                 (aSto 1 (numV 9) (mtSto)))))

(test (interp (parse '{{{fun {b}
                             {fun {a}
                                  {openbox b}}}
                        {newbox 9}}
                       {newbox 10}})
              (mtSub)
              (mtSto))
      (v*s (numV 9)
           (aSto 2 (numV 10)
                 (aSto 1 (numV 9) (mtSto)))))
(test (interp (parse '{{fun {b}
                            {seqn
                             {setbox b 2}
                             {openbox b}}}
                       {newbox 1}})
              (mtSub)
              (mtSto))
      (v*s (numV 2)
           (aSto 1 (numV 2) (mtSto))))

(test (interp (parse '{{fun {b}
                            {seqn
                             {setbox b {+ 2 (openbox b)}}
                             {setbox b {+ 3 (openbox b)}}
                             {setbox b {+ 4 (openbox b)}}
                             {openbox b}}}
                       {newbox 1}})
              (mtSub)
              (mtSto))
        (v*s (numV 10)
             (aSto 1 (numV 10) (mtSto))))


(test/exn (interp (parse '{openbox x})
                  (aSub 'x (boxV 1) (mtSub))
                  (mtSto))
          "unallocated")

;; records

(test (interp-expr (parse '{{fun {r}
                                 {get r x}}
                            {rec {x 1}}}))
      1)

(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {set r x 5}
                                  {get r x}}}
                            {rec {x 1}}}))
      5)
(test (interp-expr (parse '{{{{{fun {g}
                                    {fun {s}
                                         {fun {r1}
                                              {fun {r2}
                                                   {+ {get r1 b}
                                                      {seqn
                                                       {{s r1} {g r2}}
                                                       {+ {seqn
                                                           {{s r2} {g r1}}
                                                           {get r1 b}}
                                                          {get r2 b}}}}}}}}
                               {fun {r} {get r a}}}            ; g
                              {fun {r} {fun {v} {set r b v}}}} ; s
                             {rec {a 0} {b 2}}}                ; r1
                            {rec {a 3} {b 4}}}))               ; r2
      5)

(test (interp-expr (parse '{fun {x} x}))
      'func)
(test (interp-expr (parse '{newbox 1}))
      'box)
(test (interp-expr (parse '{rec}))
      'record)







