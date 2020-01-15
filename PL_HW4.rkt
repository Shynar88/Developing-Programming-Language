#lang plai
(require (for-syntax racket/base) racket/match racket/list racket/string
         (only-in mzlib/string read-from-string-all))

;; build a regexp that matches restricted character expressions, can use only
;; {}s for lists, and limited strings that use '...' (normal racket escapes
;; like \n, and '' for a single ')
(define good-char "(?:[ \t\r\na-zA-Z0-9_{}!?*/<=>:+-]|[.][.][.])")
;; this would make it awkward for students to use \" for strings
;; (define good-string "\"[^\"\\]*(?:\\\\.[^\"\\]*)*\"")
(define good-string "[^\"\\']*(?:''[^\"\\']*)*")
(define expr-re
  (regexp (string-append "^"
                         good-char"*"
                         "(?:'"good-string"'"good-char"*)*"
                         "$")))
(define string-re
  (regexp (string-append "'("good-string")'")))

(define (string->sexpr str)
  (unless (string? str)
    (error 'string->sexpr "expects argument of type <string>"))
    (unless (regexp-match expr-re str)
      (error 'string->sexpr "syntax error (bad contents)"))
    (let ([sexprs (read-from-string-all
                 (regexp-replace*
                  "''" (regexp-replace* string-re str "\"\\1\"") "'"))])
    (if (= 1 (length sexprs))
      (car sexprs)
      (error 'string->sexpr "bad syntax (multiple expressions)"))))

(test/exn (string->sexpr 1) "expects argument of type <string>")
(test/exn (string->sexpr ".") "syntax error (bad contents)")
(test/exn (string->sexpr "{} {}") "bad syntax (multiple expressions)")

;; FWAE abstract syntax trees
(define-type FWAE
  [num  (n number?)] 
  [add  (left FWAE?) (right FWAE?)]
  [sub  (left FWAE?) (right FWAE?)]
  [with (name symbol?) (named-expr FWAE?) (body FWAE?)]
  [id   (name symbol?)]
  [app (ftn FWAE?) (argl (listof FWAE?))]
  [fun (paraml (listof symbol?)) (body FWAE?)]
  [record (lstmp (listof mypair?))] 
  [access (arg FWAE?) (name symbol?)])


(define-type FWAE-Value
  [numV     (n number?)]
  [closureV (paraml (listof symbol?)) (body FWAE?) (ds DefrdSub?)]
  [recordV (lst (listof Vpair?))])

(define-type tpl
  [mypair (frst symbol?) (scnd FWAE?)])

(define-type Vtpl
  [Vpair (frst symbol?) (scnd FWAE-Value?)])

(define-type DefrdSub
  [mtSub]
  [aSub (name (listof symbol?)) (value (listof FWAE-Value?)) (ds DefrdSub?)])

; parse-sexpr : sexpr -> FWAE
;; to convert s-expressions into FWAEs
(define (parse-sexpr sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse-sexpr l) (parse-sexpr r))]
    [(list '- l r) (sub (parse-sexpr l) (parse-sexpr r))]
    [(list 'with (list x i) b) (with x (parse-sexpr i) (parse-sexpr b))]
    [(? symbol?) (id sexp)]
    [(list 'fun pl b) (fun (if (check-duplicates pl) (error 'parse "bad syntax") pl) (parse-sexpr b))]
    [(list 'access fw i) (access (parse-sexpr fw) i)]
    [(list 'record a ...) (if (check-duplicates a #:key car) (error 'parse-sexpr "duplicate fields")
                              (record (map (lambda (i)
                                       (mypair (first i) (parse-sexpr (second i))))
                                                   a)))]
    [(list f al ...) (app (parse-sexpr f) (map (lambda (i)
                                             (parse-sexpr i))
                                           al))]
    [else (error 'parse "bad syntax: ~a" sexp)]))



;; parse : string -> FWAE
;; parses a string containing a FWAE expression to a FWAE AST
(define (parse str)
  (parse-sexpr (string->sexpr str)))

; num+: FWAE-Value FWAE-Value -> FWAE-Value
; adds FWAE-Values
(define (num+ x y)
  (numV (+ (numV-n x) (numV-n y))))

; num-: FWAE-Value FWAE-Value -> FWAE-value
; substracts FWAE-Values
(define (num- x y)
  (numV (- (numV-n x) (numV-n y))))

; lookup : symbol DefrdSub -> number
; searches for value coreseponding to given symbol
(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free identifier")]
    [aSub  (xl vall rest) 
           (if (member name xl)   
               (list-ref vall (index-of xl name))
               (lookup name rest))]))

; search : (list of Vpair) symbol -> FWAE-Value
; searches for value corrseponding to given symbol in a record
(define (search lst name)
  (if (empty? lst) (error 'search "no such field")
      (if (equal? (Vpair-frst (first lst)) name) (Vpair-scnd (first lst)) (search (rest lst) name))))

; interp: FWAE DefrdSub -> FWAE-Value
;; evaluates FWAE expressions by reducing them to FWAE-Value
(define (interp fwae ds)
  (type-case FWAE fwae 
    [num  (n) (numV n)]
    [add  (l r) (num+ (interp l ds) (interp r ds))]
    [sub  (l r) (num- (interp l ds) (interp r ds))]
    [with (x i b) (interp b (aSub (list x) (list (interp i ds)) ds))]
    [id   (s)     (lookup s ds)]
    [record (lstofmypairs) (recordV (map (lambda (i)
                                           (Vpair (mypair-frst i) (interp (mypair-scnd i) ds))) lstofmypairs))]
    [access (fw i) (local [(define rval (interp fw ds))]
                     (type-case FWAE-Value rval 
                       [numV (n) (error 'access "expected a record")]
                       [recordV (lst) (search lst i)]
                       [closureV (x v b) (error 'access "expected a record")]))]
    [fun  (x b) (if ((listof symbol?) x) (closureV x b ds) (closureV '(x) b ds))]
    [app (f a) (local [(define f-val (interp f ds))]
                 (if (equal? (length (closureV-paraml f-val)) (length a))
                 (interp (closureV-body f-val) 
                         (aSub (closureV-paraml f-val)
                               (map (lambda (i)
                                      (interp i ds))
                                    a)
                               (closureV-ds f-val))) (error 'interp "wrong arity")))]))


; run : string -> number or symbol
;; evaluate a FWAE program contained in a string
(define (run str)
  (local [(define result (interp (parse str) (mtSub)))]
    (type-case FWAE-Value result 
      [numV (n) n]
      [closureV (x v b) 'function]
      [recordV (l) 'record])))

;my tests
(test (run "{{fun {x y z} {+ x 1}} {+ 10 12} 3 2}") 23)
(test (run "{{fun {} 5} }") 5)
(test (run "{{fun {x y z} {+ x 1}} 10 3 2}") 11)
(test (run "{{fun {} {+ 2 1}} }") 3)
(test/exn (run "{{fun {x y z} {+ x y z}} 2 3 4 5}") "wrong arity")
(test/exn (run "{{fun {x x z} {+ x y z}} 2 3 4}") "bad syntax")
(test/exn (run "{{fun {f x x} x} 2}") "bad syntax")
(test (run "{fun {} 3}") 'function)


;given tests
(test (run "{record {a 10} {b {+ 1 2}}}")
      'record)
(test (run "{access {record {a 10} {b {+ 1 2}}} b}")
      3)
(test/exn (run "{access {record {b 10} {b {+ 1 2}}} b}")
          "duplicate fields")
(test/exn (run "{access {record {a 10}} b}")
          "no such field")
(test (run "{with {g {fun {r} {access r c}}}
                  {g {record {a 0} {c 12} {b 7}}}}")
      12)
(test (run "{access {record {r {record {z 0}}}} r}")
      'record)
(test (run "{access {access {record {r {record {z 0}}}} r} z}")
      0)
(test/exn (run "{record {z {access {record {z 0}} y}}}")
          "no such field")
(test (run "{with {f {fun {a b} {+ a b}}}
                  {with {g {fun {x} {- x 5}}}
                        {with {x {f 2 5}} {g x}}}}") 2)
(test (run "{with {f {fun {x y} {+ x y}}} {f 1 2}}") 3)
(test (run "{with {f {fun {} 5}}
                  {+ {f} {f}}}") 10)
(test (run "{with {h {fun {x y z w} {+ x w}}}
                  {h 1 4 5 6}}") 7) 
(test (run "{with {f {fun {} 4}}
                  {with {g {fun {x} {+ x x}}}
                        {with {x 10} {- {+ x {f}} {g 4}}}}}") 6)
(test (run "{record {a 10} {b {+ 1 2}}}") 'record)
(test (run "{access {record {r {record {z 0}}}} r}") 'record)
(test (run "{access {access {record {r {record {z 0}}}} r} z}") 0)
(test (run "{with {x 3} {with {y 5} {access {record {a x} {b y}} a}}}") 3)
(test (run "{with {f {fun {a b} {+ {access a a} b}}}
                  {with {g {fun {x} {+ 5 x}}}
                        {with {x {f {record {a 10} {b 5}} 2}} {g x}}}}") 17)
(test (run "{with {f {fun {a b c d e} {record {a a} {b b} {c c} {d d} {e e}}}}
                  {access {f 1 2 3 4 5} c}}") 3)
(test (run "{with {f {fun {a b c} {record {a a} {b b} {c c}}}}
                  {access {f 1 2 3} b}}") 2)
(test (run "{with {f {fun {a b c} {record {x a} {y b} {z c} {d 2} {e 3}}}}
                  {access {f 1 2 3} y}}") 2)
(test (run "{with {f {fun {a b c} {record {x a} {y b} {z c} {d 2} {e 3}}}}
                  {access {f 1 2 3} d}}") 2)
(test (run "{with {f {fun {x} {+ 5 x}}}
                  {f {access {access {record {a {record {a 10} {b {- 5 2}}}} {b {access {record {x 50}} x}}} a} b}}}") 8)
(test (run "{access {record {a 10} {b {+ 1 2}}} b}") 3)
(test (run "{access {record {r {record {z 0}}}} r}") 'record)
(test (run "{access {access {record {r {record {z 0}}}} r} z}") 0)
(test (run "{record {a 10}}") `record)
(test (run "{access {record {a 10}} a}") 10)
(test (run "{access {record {a {+ 1 2}}} a}") 3)
(test (run "{fun {x} x}") 'function)
(test (run "{access {record {a {record {b 10}}}} a}") `record)
(test (run "{access {access {record {a {record {a 10}}}} a} a}") 10)
(test (run "{access {access {record {a {record {a 10} {b 20}}}} a} a}") 10)
(test (run "{access {access {record {a {record {a 10} {b 20}}}} a} b}") 20)
(test (run "{+ {access {record {a 10}} a} {access {record {a 20}} a}}") 30)
(test (run "{+ {access {record {a 10}} a} {access {record {a 20}} a}}") 30)
(test (run "{record {a 10}}") `record)
(test (run "{record {a {- 2 1}}}") `record)
(test (run "{access {record {a 10}} a}") 10)
(test (run "{access {record {a {- 2 1}}} a}") 1)
(test (run "{access {record {a {record {b 10}}}} a}") `record)
(test (run "{access {access {record {a {record {a 10}}}} a} a}") 10)
(test (run "{access {access {record {a {record {a 10} {b 20}}}} a} a}") 10)
(test (run "{access {access {record {a {record {a 10} {b 20}}}} a} b}") 20)
(test (run "{access {record {r {record {z 0}}}} r}") 'record)
(test (run "{access {access {record {r {record {z 0}}}} r} z}") 0)
(test (run "{with {y {record {x 1} {y 2} {z 3}}} {access y y}}") 2)
(test (run "{with {y {record {x 1} {y 2} {z 3}}} {access y z}}") 3)
(test (run "{record {a 10} {b {+ 1 2}}}") 'record)
(test (run "{access {record {a 10} {b {+ 1 2}}} b}") 3)
(test (run "{with {g {fun {r} {access r c}}}
                  {g {record {a 0} {c 12} {b 7}}}}") 12)
(test (run "{access {record {r {record {z 0}}}} r}") 'record)
(test (run "{access {access {record {r {record {z 0}}}} r} z}") 0)

