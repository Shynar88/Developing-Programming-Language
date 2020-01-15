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



(define-type KCFAE
  [num (n number?)]
  [add (lhs KCFAE?)
       (rhs KCFAE?)]
  [sub (lhs KCFAE?)
       (rhs KCFAE?)]
  [id (name symbol?)]
  [fun (paraml (listof symbol?))
       (body KCFAE?)]
  [app (fun-expr KCFAE?)
       (argl (listof KCFAE?))]
  [if0 (test KCFAE?)
       (then KCFAE?)
       (else KCFAE?)]
  [withcc (name symbol?)
          (body KCFAE?)]
  [trycatch (try KCFAE?) (catch KCFAE?)]
  [throw])

(define-type KCFAE-Value
  [numV (n number?)]
  [closureV (paraml (listof symbol?))
            (body KCFAE?)
            (sc DefrdSub?)]
  [contV (proc procedure?)])

(define-type DefrdSub
  [mtSub]
  [aSub (name (listof symbol?))
        (value (listof KCFAE-Value?))
        (rest DefrdSub?)])

;; ----------------------------------------

;; parse : S-expr -> KCFAE
(define (parse sexp)
  (cond
    [(number? sexp) (num sexp)]
    [(symbol? sexp) (id sexp)]
    [(pair? sexp)
     (case (car sexp)
       [(+) (add (parse (second sexp)) (parse (third sexp)))]
       [(-) (sub (parse (second sexp)) (parse (third sexp)))]
       [(fun) (fun (if (check-duplicates (second sexp)) (error 'parse "bad syntax") (second sexp)) (parse (third sexp)))]
       [(if0) (if0 (parse (second sexp))
                   (parse (third sexp))
                   (parse (fourth sexp)))]
       [(withcc) (withcc (second sexp) (parse (third sexp)))]
       [(try) (trycatch (parse (second sexp)) (parse (fourth sexp)))]
       [(throw) (throw)]
       [else (app (parse (first sexp)) (map (lambda (i)
                                             (parse i))
                                           (rest sexp)))])]))

(define evaluated 0)
(define env 0)
(define answer 0)

;; ----------------------------------------

;; interp : KCFAE DefrdSub (KCFAE-Value -> alpha) -> alpha
(define (interp a-fae ds k)
  ;(print a-fae)
  ;(newline)
  ;(print ds)
  ;(newline)
  (type-case KCFAE a-fae
    [num (n) (k (numV n))]
    [add (l r) (interp l ds
                       (lambda (v1)
                         (if (equal? v1 'throw)
                             answer
                         (interp r ds
                                 (lambda (v2)
                                   (if (equal? v2 'throw)
                                       ;(begin (set! evaluated false) answer)
                                       answer
                                   (k (num+ v1 v2))))))))]
    [sub (l r) (interp l ds
                       (lambda (v1)
                         (if (equal? v1 'throw)
                             answer
                         (interp r ds
                                 (lambda (v2)
                                   (if (equal? v2 'throw)
                                       answer
                                   (k (num- v1 v2))))))))]
    [id (name) (k (lookup name ds))]
    [fun (param body-expr)
         (k (if ((listof symbol?) param) (closureV param body-expr ds) (closureV '(param) body-expr ds)))]
    [app (fun-expr arg-expr)
         (interp fun-expr ds
                 (lambda (fun-val)
                   (if (equal? fun-val 'throw)
                             answer
                          (local [(define arg-val (map (lambda (i) (interp i ds (lambda (x) x))) arg-expr))]
                             (type-case KCFAE-Value fun-val
                               [closureV (paraml body ds1)
                                         (print evaluated) (newline)
                                         (if evaluated
                                             (begin (set! evaluated false) answer)
                                         (if (equal? (length paraml) (length arg-expr))
                                         (interp body
                                                 (aSub paraml
                                                       arg-val
                                                       ds1) ;we evaluate throw under this ds1. eval becomes true somewhere later
                                                 k)
                                         (error 'interp "wrong arity")))]
                               [contV (k1)
                                      ;(k1 arg-val)]
                                      (begin
                                        (set! evaluated true)
                                      (set! answer (k1 (first arg-val)))
                                      (k1 (first arg-val)))]
                               [else (error 'interp "not a function")])))))]
    [if0 (test-expr then-expr else-expr)
         (interp test-expr ds
                 (lambda (v)
                   (if (equal? v 'throw)
                             answer
                   (if (numzero? v)
                       (interp then-expr ds k)
                       (interp else-expr ds k)))))]
    [withcc (id body-expr)
            (interp body-expr 
                    (aSub (list id)
                          (list (contV k)) 
                          ds)
                    k)]
    [trycatch (try catch) (interp try
                                  (aSub (list 'catch) (list (interp catch ds k)) ds)
                                  (lambda (v)
                                    (if (equal? 'throw v)
                                        (interp catch ds k)
                                        (k v))))]
    [throw () (begin (print evaluated) (set! evaluated true) (print evaluated) (set! answer (lookup 'catch ds)) (k 'throw))]))

;; num-op : (number number -> number) -> (KCFAE-Value KCFAE-Value -> KCFAE-Value)
(define (num-op op op-name)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))

(define num+ (num-op + '+))
(define num- (num-op - '-))

;; numzero? : KCFAE-Value -> boolean
(define (numzero? x)
  (zero? (numV-n x)))

#|(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name val rest-sc)
          (if (symbol=? sub-name name) 
              num
              (lookup name rest-sc))]))|#
(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub  (xl vall rest) 
           (if (member name xl)   
               (list-ref vall (index-of xl name))
               (lookup name rest))]))

(test/exn (lookup 'x (mtSub)) "free variable")
(test (lookup 'x (aSub '(x) (list (numV 9)) (mtSub))) (numV 9))
(test (lookup 'x (aSub '(y) (list (numV 10)) (aSub '(x) (list (numV 9)) (mtSub)))) (numV 9))

;; interp-expr : KCFAE -> KCFAE-Value
(define (interp-expr a-fae)
  (type-case KCFAE-Value (interp a-fae (mtSub) (lambda (x) x))
    [numV (n) n]
    [closureV (param body ds) 'function]
    [contV (k) 'function]))

(define (run str)
  (begin (set! evaluated false)
  (interp-expr (parse (string->sexpr str)))))

;(interp-expr (app (fun '(f) (trycatch (app (id 'f) (list (num 3))) (num 8))) (list (fun '(x) (throw)))))

#|(interp-expr (app
 (withcc 'esc (trycatch (app (withcc 'k (app (id 'esc) (list (id 'k)))) (list (num 0))) (fun '(x) (num 8))))
 (list (fun '(x) (throw)))))|#

(test (run "{{fun {x y} {- y x}} 10 12}") 2)
(test (run "{fun {} 12}") 'function)
(test (run "{fun {x} {fun {} x}}") 'function)
(test (run "{{{fun {x} {fun {} x}} 13}}") 13)
(test (run "{withcc esc {{fun {x y} x} 1 {esc 3}}}") 3)

(test (run "{try 7 catch 8}")
        7)
(test (run "{try {throw} catch 8}")
      8)
(test (run "{try {+ 1 {throw}} catch 8}")
      8)
(test (run "{{fun {f} {try {f 3} catch 8}}
               {fun {x} {throw}}}")
      8)
(test (run "{try {try {throw} catch 8} catch 9}")
      8)
(test (run "{try {try {throw} catch {throw}} catch 9}")
      9)
(test (run "{try {try 7 catch {throw}} catch 9}")
      7)
(test (run "{{withcc esc {try {{withcc k {esc k}} 0} catch {fun {x} 8}}}
               {fun {x} {throw}}}")
      8)

#|{{withcc esc {try {{withcc k {esc k}} 0} catch {fun {x} 8}}}
               {fun {x} {throw}}}
esc {[] {fun {x} {throw}}}
k {{try {[] 0} catch {fun {x} 8}} {fun {x} {throw}}}
{esc k}|#

; multiple arguments (5)
(test (run "{{fun {x y} {- y x}} 10 12}") 2)
(test (run "{fun {} 12}") 'function)
(test (run "{fun {x} {fun {} x}}") 'function)
(test (run "{{{fun {x} {fun {} x}} 13}}") 13)
(test (run "{withcc esc {{fun {x y} x} 1 {esc 3}}}") 3)

; exceptions (35)
(test (run "{+ {withcc k {k 5}} 4}" ) 9)
(test (run "{{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} 1 {+ y {g g {- y 1}}}}} 10}") 55) ; recursive function
(test (run "{withcc done {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {done 100} {+ y {g g {- y 1}}}}} 10}}") 100) ; exit from recursive function using continuation
(test (run "{withcc k {- 0 {k 100}}}" ) 100)
(test (run "{withcc k {k {- 0 100}}}" ) -100)
(test (run "{withcc k {k {+ 100 11}}}" ) 111)
(test (run "{{fun {a b c} {- {+ {withcc k {+ {k 100} a}} b} c}} 100 200 300}" ) 0)
(test (run "{withcc esc {{fun {x y} x} 1 {esc 3}}}") 3)
(test (run "{{withcc esc {{fun {x y} {fun {z} {+ z y}}} 1 {withcc k {esc k}}}} 10}") 20)
(test (run "{try {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {+ y {g g {- y 1}}}}} 10} catch 110}") 110) ; exit from recursive function using try-catch
(test (run "{{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch y}}} 10}") 54) ; equal? for multiple recursive try-catch
(test (run "{withcc done {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch {done y}}}} 10}}") 2)
(test (run "{try {{fun {f x} {f f x}} {fun {g y} {if0 {- y 1} {throw} {try {+ y {g g {- y 1}}} catch {throw}}}} 10} catch 20110464}") 20110464) ; recursive try-catch throwing (1)
(test (run "{try {{fun {x y z} {a b c}} 1 2 {throw}} catch 0}") 0)
(test (run "{{fun {f} {try {f 3} catch 8}} {fun {x} {throw}}}") 8)
(test (run "{try {- 0 {withcc k {+ 3 {k {throw}}}}} catch 89}") 89)
(test (run "{try {+ 3 {withcc k {+ 1000 {k {throw}}}}} catch 11}") 11)
(test (run "{{fun {x y z} {try {+ 1 {+ x {throw}}} catch {+ y z}}} 1 2 3}") 5)
(test (run "{+ {try {- 10 {throw}} catch 3} 10}") 13)
(test (run "{try {if0 0 {throw} {+ 1 2}} catch {if0 10 1 {try {throw} catch 54}}}") 54)
(test (run "{try {withcc a {+ 1 {withcc b {throw}}}} catch 10}") 10)
(test (run "{try {- 0 {throw}} catch 5}") 5)
(test (run "{try {if0 {throw} 3 4} catch 5}") 5)
(test (run "{try {{fun {x y} {try x catch y}} {throw} 0} catch -1}") -1)
(test (run "{try {try {throw} catch {throw}} catch 9}") 9)
(test (run "{{withcc esc {try {{withcc k {esc k}} 0} catch {fun {x} 8}}} {fun {x} {throw}}}") 8)
(test (run "{{withcc esc {try {{withcc k {try {esc k} catch {fun {x} {fun {y} 9}}}} 0} catch {fun {x} 8}}} {fun {x} {throw}}}") 8)
(test (run "{withcc foo {{fun {x y} {y x}} {+ 2 3} {withcc bar {+ 1 {bar foo}}}}}") 5)
(test (run "{try {withcc zzz {{fun {x y z w} {+ {+ x y} {+ z w}}} 1 2 {zzz 10} {throw}}} catch 42}") 10)
(test (run "{try {withcc zzz {{fun {x y z w} {+ {+ x y} {+ z w}}} 1 2 {throw} {zzz 10}}} catch 42}") 42)
(test (run "{try {withcc zzz {{fun {x y z w} {+ {w {+ x y}} {+ {throw} z}}} 1 2 3 zzz}} catch 42}") 3)
(test (run "{withcc esc {try {+ {throw} {esc 3}} catch 4}}") 4)
(test (run "{withcc esc {{fun {x y} {+ {+ x 3} y}} {withcc k {try {k {esc {throw}}} catch {k 5}}} 7}}") 15)
(test (run "{try {withcc x {+ {x 1} {throw}}} catch 0}") 1)
(test (run "{+ 12 {withcc k {+ 1 {k {{fun {} 7}}}}}}") 19)

; multiple arguments (6)
(test (run "{+ 999 {withcc done {{fun {f x} {f f x done}} {fun {g y z} {if0 {- y 1} {z 100} {+ y {g g {- y 1} z}}}} 10}}}") 1099)
(test (run "{+ 999 {withcc done {{fun {f x} {f f x {fun {x} {if0 x {done {- 0 999}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 100} {+ y {g g {- y 1} z}}}} 10}}}") 11053)
(test (run "{+ 999 {withcc done {{fun {f x} {f f x {fun {x} {if0 x {done {- 0 999}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {+ y {g g {- y 1} z}}}} 10}}}") 0)
(test (run "{withcc done {{fun {f x} {f f x {fun {x} {if0 x {fun {y} {fun {x} {+ x y}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 3}}") 64)
(test (run "{{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 3}} 5}") 'function)
(test (run "{{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 4}} {fun {y} {fun {y} {fun {y} {fun {x} 42}}}}}") 42)

; exceptions (4)
(test (run "{try {{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} {throw}}}}} {fun {g y z} {if0 {- y 1} {z 1} {{g g {- y 1} z} 32}}} 4}} {fun {y} {fun {y} {fun {y} {fun {x} 42}}}}} catch 4242}") 4242)
(test (run "{withcc esc {{try {withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} {throw}}}}} {fun {g y z} {if0 {- y 1} {z 1} {{g g {- y 1} z} 32}}} 4}} catch esc} 33}}") 33)
(test (run "{try {try {throw} catch {try {throw} catch {try {throw} catch {+ {withcc k {try {throw} catch {k 0}}} {throw}}}}} catch 0}") 0)
(test (run "{try {{withcc done {{fun {f x} {f f x {fun {x} {if0 x {withcc k {fun {x} {fun {x} {fun {x} k}}}} 10000}}}} {fun {g y z} {if0 {- y 1} {z 0} {{g g {- y 1} z} 32}}} 4}} {fun {y} {fun {y} {fun {y} {throw}}}}} catch 4242}") 4242)