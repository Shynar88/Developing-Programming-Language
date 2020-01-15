#lang plai-typed

;; EXPR abstract syntax trees
(define-type EXPR  
  [num (n : number)]
  [bool (b : boolean)]
  [add (lhs : EXPR) (rhs : EXPR)]
  [sub (lhs : EXPR) (rhs : EXPR)]
  [equ (lhs : EXPR) (rhs : EXPR)]
  [id (name : symbol)]
  [fun (param : symbol) (paramty : TE) (body : EXPR)]
  [app (fun-expr : EXPR) (arg-expr : EXPR)]
  [ifthenelse (test-expr : EXPR) (then-expr : EXPR) (else-expr : EXPR)]
  [rec (name : symbol) (ty : TE) (named-expr : EXPR) (body : EXPR)]
  [with-type (name : symbol)
             (var1-name : symbol) (var1-ty : TE)
             (var2-name : symbol) (var2-ty : TE)
             (body-expr : EXPR)]
  [cases (name : symbol)
         (dispatch-expr : EXPR)
         (var1-name : symbol) (bind1-name : symbol) (rhs1-expr : EXPR)
         (var2-name : symbol) (bind2-name : symbol) (rhs2-expr : EXPR)]
  [tfun (name : symbol) (expr : EXPR)]
  [tapp (body : EXPR) (type : TE)])

(define-type TE
  [numTE]
  [boolTE]
  [arrowTE (param : TE) (result : TE)]
  [polyTE (forall : symbol) (body : TE)]
  [idTE (name : symbol)]
  [tvTE (name : symbol)])

(define-type Type 
  [numT]
  [boolT]
  [arrowT (param : Type) (result : Type)]
  [polyT (forall : symbol) (body : Type)] ;forall alpha t
  [idT (name : symbol)] ;animal fruit color
  [tvT (name : symbol)]) ;alpha beta

;parse-type: TE -> Type
;converts TE to Type
(define (parse-type te)
  (type-case TE te
    [numTE () (numT)]
    [boolTE () (boolT)]
    [arrowTE (param result) (arrowT (parse-type param) (parse-type result))]
    [polyTE (forall body) (polyT forall (parse-type body))]
    [idTE (name) (idT name)]
    [tvTE (name) (tvT name)]))

(define-type EXPR-Value
  [numV (n : number)]
  [boolV (b : boolean)]
  [closureV (param : symbol) (body : EXPR) (ds : DefrdSub)] ;ds is used here for interp, not type check
  [variantV (right? : boolean) (val : EXPR-Value)]
  [constructorV (right? : boolean)])

(define-type DefrdSub
  [mtSub]
  [aSub    (name : symbol)
           (value : EXPR-Value)
           (ds : DefrdSub)]
  [aRecSub (name : symbol)
           (value-box : (boxof EXPR-Value))
           (ds : DefrdSub)])

;validtype: Type TypeEnv -> TypeEnv
;function checks if type is valid
(define (validtype ty env)
  (type-case Type ty
    [numT () (mtEnv)]
    [boolT () (mtEnv)]
    [arrowT (a b) (begin (validtype a env)
                         (validtype b env))]
    [polyT (fa b) (validtype b (pBind fa env))] ;when in fun app alpha can be introduced by polyTE  
    [idT (id) (find-type-id id env)]
    [tvT (id) (find-polytype id env)]))
  
(define-type TypeEnv  
  [mtEnv]
  [aBind (name : symbol) (type : Type) (rest : TypeEnv)]
  [tBind (name : symbol)
         (var1-name : symbol) (var1-type : Type)
         (var2-name : symbol) (var2-type : Type)
         (rest : TypeEnv)]
  [pBind (name : symbol) (rest : TypeEnv)])

;get-type: symbol TypeEnv -> Type
;for finding Type given to symbol in environment
(define (get-type name-to-find env) 
  (type-case TypeEnv env
    [mtEnv () (error 'get-type "free variable, so no type")]
    [aBind (name ty rest)
           (if (symbol=? name-to-find name)
               ty
               (get-type name-to-find rest))]
    [tBind (name var1-name var1-ty var2-name var2-ty rest)
           (get-type name-to-find rest)]
    [pBind (name rest) (get-type name-to-find rest)])) 


; find-type-id: symbol TypeEnv -> TypeEnv
; for checking if tid was introduced by programmer before by looking up whether given tid exists in environment
(define (find-type-id name-to-find env)       ;for colors, fruits, animals
  (type-case TypeEnv env
    [mtEnv () (error 'find-type-id "free type name, so no type")]
    [aBind (name ty rest)
           (find-type-id name-to-find rest)]
    [tBind (name var1-name var1-ty var2-name var2-ty rest)
           (if (symbol=? name-to-find name)
               env
               (find-type-id name-to-find rest))]
    [pBind (name rest) (find-type-id name-to-find rest)]))

;find-polytype: symbol TypeEnv -> TypeEnv
; for checking if tvt was introduced by programmer before by looking up whether given tvt exists in environment
(define (find-polytype name-to-find env)
  (type-case TypeEnv env
    [mtEnv () (error 'find-polytype "free poly name, so no type")]
    [aBind (name ty rest)
           (find-polytype name-to-find rest)]
    [tBind (name var1-name var1-ty var2-name var2-ty rest)
               (find-polytype name-to-find rest)]
    [pBind (name rest) (if (symbol=? name-to-find name)
                      env
                      (find-polytype name-to-find rest))]))
;typecheck: EXPR TypeEnv -> Type
;typechecks given expression for detecting type-related errors at compile time
(define typecheck : (EXPR TypeEnv -> Type)
  (lambda (expr env)
    (type-case EXPR expr
      [num (n) (numT)]
      [bool (b) (boolT)]
      [add (l r)
           (type-case Type (typecheck l env)
             [numT ()
                   (type-case Type (typecheck r env)
                     [numT () (numT)]
                     [else (type-error r "num")])]
             [else (type-error l "num")])]
      [sub (l r)
           (type-case Type (typecheck l env)
             [numT ()
                   (type-case Type (typecheck r env)
                     [numT () (numT)]
                     [else (type-error r "num")])]
             [else (type-error l "num")])]
      [equ (l r) (type-case Type (typecheck l env)
                   [numT ()
                         (type-case Type (typecheck r env)
                           [numT () (boolT)]
                           [else (type-error r "num")])]
                   [else (type-error l "num")])]
      [id (name) (get-type name env)]
      [fun (name te body)
           (local [(define param-type (parse-type te))]
             (begin
               (validtype param-type env)
               (arrowT param-type
                       (typecheck body (aBind name param-type env)))))]
      [app (fn arg)
           (type-case Type (typecheck fn env)
             [arrowT (param-type result-type)
                     (if (equal? param-type
                                 (typecheck arg env))
                         result-type
                         (type-error arg
                                     (to-string param-type)))]
             [else (type-error fn "function")])]
      [ifthenelse (i t e) (type-case Type (typecheck i env)
                             ;[boolT () (if (equal? (typecheck t env) (typecheck e env))
                            [boolT () (begin (local [(define then-ty (typecheck t env))
                                                    (define else-ty (typecheck t env))]
                                        (if (unify (typecheck t env) (typecheck e env) env)
                                            then-ty
                                           (type-error t "thenelse types different"))))]
                             [else (type-error i "bool")])]
      [rec (name ty rhs-expr body-expr)
           (local [(define rhs-ty (parse-type ty))
                   (define new-env (aBind name rhs-ty env))]
             (if (equal? rhs-ty (typecheck rhs-expr new-env))
                 (typecheck body-expr new-env)
                 (type-error rhs-expr (to-string rhs-ty))))]
      [with-type (type-name var1-name var1-te var2-name var2-te body-expr)
        (local [(define var1-ty (parse-type var1-te))
                (define var2-ty (parse-type var2-te))
                (define new-env (tBind type-name
                                       var1-name var1-ty
                                       var2-name var2-ty env))]
          (begin
            (validtype var1-ty new-env)
            (validtype var2-ty new-env)
            (typecheck body-expr   ;don't have t not in tau zero; so you need it
                       (aBind var1-name
                              (arrowT var1-ty
                                      (idT type-name))
                              (aBind var2-name
                                     (arrowT var2-ty
                                             (idT type-name))
                                     new-env)))))]
      [cases (type-name dispatch-expr var1-name var1-id var1-rhs
                        var2-name var2-id var2-rhs)
        (local [(define bind (find-type-id type-name env))]
          (if (and (equal? var1-name (tBind-var1-name bind))
                   (equal? var2-name (tBind-var2-name bind)))
              (type-case Type (typecheck dispatch-expr env)
                [idT (name)
                     (if (equal? name type-name)
                         (local [(define rhs1-ty
                                   (typecheck var1-rhs
                                              (aBind var1-id (tBind-var1-type bind) env)))
                                 (define rhs2-ty
                                   (typecheck var2-rhs
                                              (aBind var2-id (tBind-var2-type bind) env)))]
                           (if (equal? rhs1-ty rhs2-ty)
                               rhs1-ty
                               (type-error var2-rhs (to-string rhs1-ty))))
                         (type-error dispatch-expr (to-string type-name)))]
                [else (type-error dispatch-expr (to-string type-name))])
              (type-error expr "matching variant names")))]
      [tfun (s b) (polyT s (typecheck b (pBind s env)))]
      [tapp (b te) (local [(define t (parse-type te))
                           (define pexpr (typecheck b env))]
                     (begin
                       (validtype t env)
                       (type-case Type pexpr
                         [polyT (fa b) (replace fa b t env)] ;here b with replacements must be returend
                         [else (type-error b "polyT")])))])))

;type-error: symbol string -> (error symbol string)
;for defining type errors
(define (type-error expr rsn) (error 'type-error "no type"))  
;(define (type-error expr rsn) (error 'expr rsn))

;unify: Type Type -> TypeEnv
;for checking if types can be same and unify them
(define (unify t1 t2 env)
  (type-case Type t1
    [numT () (if (equal? t1 t2) #t (error 'unify "throw"))]
    [boolT () (if (equal? t1 t2) #t (error 'unify "throw"))]
    [idT (name) (if (idT? t2) #t (error 'unify "throw"))]
    [arrowT (param result) (if (arrowT? t2)
                               (begin (unify param (arrowT-param t2) env) (unify result (arrowT-result t2) env))
                               (error 'unify "throw"))]
    [polyT (forall body) (if (polyT? t2)
                             (unify body (polyT-body t2) env) ;not sure about polyT and tvT
                             (error 'unify "throw"))] 
    [tvT (name) (if (tvT? t2) #t (error 'unify "throw"))]))

;replace: symbol Type Type TypeEnv -> Type
;accepts symbol Typeb newt env, must return Type of Typeb with all symbol replaced  by newt
(define (replace a b t env)
  (type-case Type b
    [tvT (name) (if (symbol=? a name)
                    t
                    b)]
    [numT () b]
    [boolT () b]
    [arrowT (param result) (arrowT (replace a param t env) (replace a result t env))]
    [polyT (forall body) (if (symbol=? a forall) b (polyT forall (replace a body t env)))] ;should care about replacemant of alpha or bets, bcs you get rid of polyTs; when you encounter again polyT with same name, don't touch it
    [idT (name) b] ;animal fruit color
    ))

;; num-op : (number number -> number) -> (EXPR-Value EXPR-Value -> EXPR-Value)
; making binary operation on two numbers
(define (num-op op op-name)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))

(define num+ (num-op + '+))
(define num- (num-op - '-))


;interp: EXPR DefrdSub -> EXPR-Value
;; evaluates EXPR expressions by reducing them to EXPR-Value
(define (interp expr ds)
  (type-case EXPR expr
    [num (n) (numV n)]
    [bool (b) (boolV b)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [equ (l r) (boolV (equal? (interp l ds) (interp r ds)))]
    [id (n) (lookup n ds)]
    [fun (param paramty body) (closureV param body ds)]
    [app (fun-expr arg-expr)
         (local [(define fun-val (interp fun-expr ds))
                 (define arg-val (interp arg-expr ds))]
           (type-case EXPR-Value fun-val
             [closureV (param body ds)
                       (interp body (aSub param arg-val ds))]
             [constructorV (right?)
                           (variantV right? arg-val)]
             [else (error 'interp "not applicable")]))]
    [ifthenelse (test-expr then-expr else-expr)
         (if (boolV-b (interp test-expr ds))
             (interp then-expr ds)
             (interp else-expr ds))]
    [rec (bound-id type named-expr body-expr)
         (local [(define value-holder (box (numV 42)))
                 (define new-ds
                         (aRecSub bound-id value-holder ds))]
           (begin
             (set-box! value-holder (interp named-expr new-ds))
             (interp body-expr new-ds)))]
    [with-type (type-name var1-name var1-te
                          var2-name var2-te
                          body-expr)
      (interp body-expr
              (aSub var1-name
                    (constructorV false)
                    (aSub var2-name
                          (constructorV true)
                          ds)))]
    [cases (ty dispatch-expr
               var1-name var1-id var1-rhs
               var2-name var2-id var2-rhs)
       (type-case EXPR-Value (interp dispatch-expr ds)
         [variantV (right? val)
                   (if (not right?)
                       (interp var1-rhs (aSub var1-id val ds))
                       (interp var2-rhs (aSub var2-id val ds)))]
         [else (error 'interp "not a variant result")])]
    [tfun (n b) (interp b ds)]
    [tapp (b t) (interp b ds)]))


; lookup : symbol DefrdSub -> EXPR-Value 
; searches for value coreseponding to given symbol
(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name val rest-ds)
          (if (symbol=? sub-name name)
              val
              (lookup name rest-ds))]
    [aRecSub (sub-name val-box rest-ds)
             (if (symbol=? sub-name name)
                 (unbox val-box)
                 (lookup name rest-ds))]))



(test (typecheck (tfun 'alpha (num 3)) (mtEnv))
      (polyT 'alpha (numT)))
 
(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))
 
(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))
 
(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (mtEnv)))
      (arrowT (numT) (numT)))

(test (typecheck (tfun 'alpha (tfun 'beta (fun 'x (polyTE 'alpha (polyTE 'beta (tvTE 'alpha))) (id 'x)))) (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (polyT 'alpha (polyT 'beta (tvT 'alpha)))
                                         (polyT 'alpha (polyT 'beta (tvT 'alpha)))))))

(test (typecheck (tapp (tfun 'alpha (tfun 'beta (fun 'x (polyTE 'alpha (polyTE 'beta (tvTE 'alpha))) (id 'x)))) (numTE)) (mtEnv)) (polyT 'beta (arrowT (polyT 'alpha (polyT 'beta (tvT 'alpha))) (polyT 'alpha (polyT 'beta (tvT 'alpha))))))

(test (typecheck (fun 'x (polyTE 'alpha (tvTE 'alpha)) (id 'x)) (mtEnv)) (arrowT (polyT 'alpha (tvT 'alpha)) (polyT 'alpha (tvT 'alpha))))

(test/exn (typecheck (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'beta))) (id 'x)) (mtEnv)) "free")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtEnv)) "free")

(test/exn (typecheck (tapp (id 'f) (numTE)) (aBind 'f (arrowT (numT) (numT)) (mtEnv))) "no")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtEnv)) "free")

(test/exn (typecheck (tapp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (numTE)) (mtEnv)) "free")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (tfun 'beta (fun 'y (tvTE 'beta) (add (id 'x) (id 'y)))))) (mtEnv)) "no")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtEnv)) "free")

(test (interp (app (app (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (fun 'x (numTE) (id 'x))) (num 10)) (mtSub)) (numV 10))

(test (interp (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (mtSub)) (closureV 'f (id 'f) (mtSub)))

(test (interp (tapp (tapp (tfun 'alpha (tfun 'beta (num 3))) (numTE)) (numTE)) (mtSub)) (numV 3))

(test (interp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtSub)) (closureV 'x (id 'x) (mtSub)))

(test (interp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtSub)) (closureV 'x (id 'x) (mtSub)))

(test (interp (id 'x)
              (aSub 'x (numV 10) (mtSub)))
      (numV 10))

(test (interp (app (fun 'x (numTE)
                        (app (fun 'f (arrowTE (numTE) (numTE))
                                  (add (app (id 'f) (num 1))
                                       (app (fun 'x (numTE)
                                                 (app (id 'f)
                                                      (num 2)))
                                            (num 3))))
                             (fun 'y (numTE)
                                  (add (id 'x) (id 'y)))))
                   (num 0))
              (mtSub))
      (numV 3))

(test (typecheck (tfun 'alpha (num 3)) (mtEnv))
      (polyT 'alpha (numT)))

(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (mtEnv)))
      (arrowT (numT) (numT)))

(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (polyT 'alpha (tvT 'alpha))) (mtEnv)))
      (polyT 'alpha (tvT 'alpha)))
      
(test (interp (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (numTE))
              (mtSub))
      (closureV 'x (id 'x) (mtSub)))
      
(test (typecheck
       (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
             (polyTE 'beta (arrowTE (tvTE 'beta) (tvTE 'beta))))
       (mtEnv))
      (arrowT (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta)))
              (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta)))))
              
(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))

(test (interp (tfun 'alpha (tfun 'beta (num 3))) (mtSub))
      (numV 3))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))
      
(test (interp (app (app (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (fun 'x (numTE) (id 'x))) (num 10)) (mtSub)) (numV 10))

(test (interp (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (mtSub)) (closureV 'f (id 'f) (mtSub)))

(test (interp (tapp (tapp (tfun 'alpha (tfun 'beta (num 3))) (numTE)) (numTE)) (mtSub)) (numV 3))

(test (interp (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (mtSub)) (closureV 'f (id 'f) (mtSub)))

(test (typecheck (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x))))  (mtEnv)) (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (typecheck (ifthenelse (bool true)
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (ifthenelse (bool true)
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y)))
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))))
                 (mtEnv))
      (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta))))


(test (typecheck (ifthenelse (equ (num 8) (num 8))
                             (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x))))
                             (tfun 'beta (tfun 'gamma (fun 'x (tvTE 'beta) (id 'x)))))
                 (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha)
                                   (tfun 'beta (fun 'y (tvTE 'alpha)
                                                    (ifthenelse (bool true)
                                                                (id 'x)
                                                                (id 'y))))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha)
                            (polyT 'beta (arrowT (tvT 'alpha)
                                                 (tvT 'alpha))))))

(test (interp (app
               (tapp (ifthenelse (bool true)
                                 (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
                                 (tfun 'beta (fun 'x (tvTE 'beta) (id 'x))))
                     (numTE)) (num 30)) (mtSub))
      (numV 30))
      
(test (interp
       (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))
                 (app (tapp (id 'x) (numTE)) (num 10)))
        (tfun 'beta (fun 'y (tvTE 'beta) (id 'y)))) (mtSub)) (numV 10))
        
(test (typecheck
       (tfun 'alpha
             (fun 'alpha (arrowTE (numTE) (numTE))
                  (fun 'x (tvTE 'alpha)
                       (id 'x)))) (mtEnv))
      (polyT 'alpha (arrowT (arrowT (numT) (numT)) (arrowT (tvT 'alpha) (tvT 'alpha)))))
      
(test (typecheck
       (fun 'alpha (arrowTE (numTE) (numTE))
            (tfun 'alpha
                  (fun 'x (tvTE 'alpha)
                       (id 'x)))) (mtEnv))
      (arrowT (arrowT (numT) (numT)) (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (interp (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (num 5))) (numTE)) (mtSub)) (closureV 'x (num 5) (mtSub)))

(test (interp (tapp (tfun 'alpha (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha))) (id 'x))) (numTE)) (mtSub)) (closureV 'x (id 'x) (mtSub)))

(test (typecheck (tapp (tfun 'alpha (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha))) (id 'x))) (numTE)) (mtEnv)) (arrowT (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (typecheck (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (num 5))) (numTE)) (mtEnv)) (arrowT (numT) (numT)))

(test (interp (app (app (tapp (tapp (tfun 'alpha (tfun 'beta (fun 'x (arrowTE (tvTE 'alpha) (tvTE 'beta)) (id 'x))))
                                    (numTE))
                              (numTE))
                        (fun 'x (numTE) (add (num 5) (id 'x))))
                   (num 3))
              (mtSub))
      (numV 8))

(test (interp (app (app (tapp (tapp (tfun 'alpha (tfun 'alpha (fun 'x (arrowTE (tvTE 'alpha) (tvTE 'alpha)) (id 'x))))
                                    (numTE))
                              (numTE))
                        (fun 'x (numTE) (add (num 5) (id 'x))))
                   (num 3))
              (mtSub))
      (numV 8))
(test (typecheck (ifthenelse (equ (num 8) (num 10))
                             (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (fun 'y (tvTE 'beta) (id 'y)))))
                             (tfun 'beta (tfun 'alpha (fun 'x (tvTE 'beta) (fun 'y (tvTE 'alpha) (id 'y))))))
                 (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (arrowT (tvT 'beta) (tvT 'beta))))))

(test (typecheck (tapp (tfun 'alpha
                                 (fun 'alpha (tvTE 'alpha)
                                      (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))
                                           (app (tapp (id 'x) (numTE)) (num 10))) (tfun 'beta
                                                                                        (fun 'beta (tvTE 'beta)
                                                                                             (id 'beta)))))) (arrowTE (numTE) (numTE)))
          (mtEnv)) (arrowT (arrowT (numT) (numT)) (numT)))
(test (typecheck (tapp (tfun 'alpha
                                 (fun 'alpha (tvTE 'alpha)
                                      (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))
                                           (app (tapp (id 'x) (numTE)) (num 10))) (tfun 'beta
                                                                                        (fun 'beta (tvTE 'beta)
                                                                                             (id 'beta)))))) (numTE))
          (mtEnv)) (arrowT (numT) (numT)))
(test (typecheck (tapp (tfun 'alpha
                                 (fun 'alpha (tvTE 'alpha)
                                      (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))
                                           (app (tapp (id 'x) (numTE)) (num 10))) (tfun 'alpha
                                                                                        (fun 'alpha (tvTE 'alpha)
                                                                                             (id 'alpha)))))) (numTE))
          (mtEnv)) (arrowT (numT) (numT)))

(test (typecheck (tfun 'alpha (num 3)) (mtEnv))
      (polyT 'alpha (numT)))

(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (mtEnv)))
      (arrowT (numT) (numT)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test (typecheck (ifthenelse (bool true)
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (ifthenelse (bool true)
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y)))
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))))
                 (mtEnv))
      (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta))))


(test (typecheck (ifthenelse (bool true)
                             (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x))))
                             (tfun 'beta (tfun 'gamma (fun 'x (tvTE 'beta) (id 'x)))))
                 (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (tvT 'alpha)))))


(test (interp (tapp (tapp (tfun 'alpha (tfun 'beta (num 3))) (numTE)) (numTE)) (mtSub))
      (numV 3))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha)
                                   (tfun 'beta (fun 'y (tvTE 'alpha)
                                                    (ifthenelse (bool true)
                                                                (id 'x)
                                                                (id 'y))))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha)
                            (polyT 'beta (arrowT (tvT 'alpha)
                                                 (tvT 'alpha))))))

(test (typecheck (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha))) (num 42)) (id 'f)) (aBind 'f (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta))) (mtEnv))) (numT))

;;; tests on noah 234th article
(test (typecheck (fun 'x (polyTE 'alpha (tvTE 'alpha)) (id 'x)) (mtEnv))
      (arrowT (polyT 'alpha (tvT 'alpha)) (polyT 'alpha (tvT 'alpha))))

;;; tests on noah 236th article
(test (typecheck (tapp (tfun 'alpha (tfun 'beta (fun 'x (polyTE 'alpha (polyTE 'beta (tvTE 'alpha))) (id 'x)))) (numTE)) (mtEnv))
      (polyT 'beta (arrowT (polyT 'alpha (polyT 'beta (tvT 'alpha))) (polyT 'alpha (polyT 'beta (tvT 'alpha))))))

(test (typecheck (app (tapp (tapp (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x)))) (numTE)) (numTE)) (num 10)) (mtEnv)) (numT))
(test (interp (app (tapp (tapp (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x)))) (numTE)) (numTE)) (num 10)) (mtSub)) (numV 10))
#|
;mytests
(test/exn (typecheck (tapp (tfun 'alpha (tfun 'beta (fun 'x (polyTE 'alpha (polyTE 'beta (tvTE 'alpha))) (id 'y)))) (numTE)) (mtEnv)) "get-type: free variable, so no type")
(test (typecheck (tfun 'alpha (bool #t)) (mtEnv))
      (polyT 'alpha (boolT)))
(test (interp (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'x))) (arrowTE (numTE) (numTE))) (mtSub)) (closureV 'f (id 'x) (mtSub)))
(test (interp (tapp (tapp (tfun 'alpha (tfun 'beta (bool #f))) (numTE)) (numTE)) (mtSub)) (boolV #f))
(test (typecheck (tfun 'alpha (bool #t)) (mtEnv))
      (polyT 'alpha (boolT)))
(test (interp (app (fun 'x (numTE)
                        (app (fun 'f (arrowTE (numTE) (numTE))
                                  (add (app (id 'f) (num 1))
                                       (app (fun 'x (numTE)
                                                 (app (id 'f)
                                                      (num 2)))
                                            (num 3))))
                             (fun 'y (numTE)
                                  (sub (id 'x) (id 'y)))))
                   (num 0))
              (mtSub))
      (numV -3))
(test/exn (typecheck (tfun 'alpha (id 'alpha)) (mtEnv))
      "get-type: free variable, so no type")
(test (typecheck (tfun 'gamma (tfun 'beta (num 42))) (mtEnv))
      (polyT 'gamma (polyT 'beta (numT))))
(test (interp (tapp (tfun 'alpha (fun 'x (polyTE 'alpha (polyTE 'beta (tvTE 'alpha))) (num 5))) (numTE)) (mtSub)) (closureV 'x (num 5) (mtSub)))
(test (interp (tapp (tfun 'alpha (fun 'x (arrowTE (tvTE 'alpha) (tvTE 'alpha)) (id 'x))) (numTE)) (mtSub)) (closureV 'x (id 'x) (mtSub)))




;given tests
(test (typecheck (tfun 'alpha (num 3)) (mtEnv))
      (polyT 'alpha (numT)))
 
(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))
 
(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))
 
(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (mtEnv)))
      (arrowT (numT) (numT)))

(test (typecheck (tfun 'alpha (tfun 'beta (fun 'x (polyTE 'alpha (polyTE 'beta (tvTE 'alpha))) (id 'x)))) (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (polyT 'alpha (polyT 'beta (tvT 'alpha)))
                                         (polyT 'alpha (polyT 'beta (tvT 'alpha)))))))

(test (typecheck (tapp (tfun 'alpha (tfun 'beta (fun 'x (polyTE 'alpha (polyTE 'beta (tvTE 'alpha))) (id 'x)))) (numTE)) (mtEnv)) (polyT 'beta (arrowT (polyT 'alpha (polyT 'beta (tvT 'alpha))) (polyT 'alpha (polyT 'beta (tvT 'alpha))))))

(test (typecheck (fun 'x (polyTE 'alpha (tvTE 'alpha)) (id 'x)) (mtEnv)) (arrowT (polyT 'alpha (tvT 'alpha)) (polyT 'alpha (tvT 'alpha))))

(test/exn (typecheck (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'beta))) (id 'x)) (mtEnv)) "free")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtEnv)) "free")

(test/exn (typecheck (tapp (id 'f) (numTE)) (aBind 'f (arrowT (numT) (numT)) (mtEnv))) "no")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtEnv)) "free")

(test/exn (typecheck (tapp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (numTE)) (mtEnv)) "free")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (tfun 'beta (fun 'y (tvTE 'beta) (add (id 'x) (id 'y)))))) (mtEnv)) "no")

(test/exn (typecheck (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtEnv)) "free")

(test (interp (app (app (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (fun 'x (numTE) (id 'x))) (num 10)) (mtSub)) (numV 10))

(test (interp (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (mtSub)) (closureV 'f (id 'f) (mtSub)))

(test (interp (tapp (tapp (tfun 'alpha (tfun 'beta (num 3))) (numTE)) (numTE)) (mtSub)) (numV 3))

(test (interp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtSub)) (closureV 'x (id 'x) (mtSub)))

(test (interp (tfun 'alpha (fun 'x (tvTE 'beta) (id 'x))) (mtSub)) (closureV 'x (id 'x) (mtSub)))

(test (interp (id 'x)
              (aSub 'x (numV 10) (mtSub)))
      (numV 10))

(test (interp (app (fun 'x (numTE)
                        (app (fun 'f (arrowTE (numTE) (numTE))
                                  (add (app (id 'f) (num 1))
                                       (app (fun 'x (numTE)
                                                 (app (id 'f)
                                                      (num 2)))
                                            (num 3))))
                             (fun 'y (numTE)
                                  (add (id 'x) (id 'y)))))
                   (num 0))
              (mtSub))
      (numV 3))

(test (typecheck (tfun 'alpha (num 3)) (mtEnv))
      (polyT 'alpha (numT)))

(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (mtEnv)))
      (arrowT (numT) (numT)))

(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (polyT 'alpha (tvT 'alpha))) (mtEnv)))
      (polyT 'alpha (tvT 'alpha)))
      
(test (interp (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (numTE))
              (mtSub))
      (closureV 'x (id 'x) (mtSub)))
      
(test (typecheck
       (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
             (polyTE 'beta (arrowTE (tvTE 'beta) (tvTE 'beta))))
       (mtEnv))
      (arrowT (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta)))
              (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta)))))
              
(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))

(test (interp (tfun 'alpha (tfun 'beta (num 3))) (mtSub))
      (numV 3))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))
      
(test (interp (app (app (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (fun 'x (numTE) (id 'x))) (num 10)) (mtSub)) (numV 10))

(test (interp (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (mtSub)) (closureV 'f (id 'f) (mtSub)))

(test (interp (tapp (tapp (tfun 'alpha (tfun 'beta (num 3))) (numTE)) (numTE)) (mtSub)) (numV 3))

(test (interp (tapp (tfun 'alpha (fun 'f (tvTE 'alpha) (id 'f))) (arrowTE (numTE) (numTE))) (mtSub)) (closureV 'f (id 'f) (mtSub)))

(test (typecheck (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x))))  (mtEnv)) (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (typecheck (ifthenelse (bool true)
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (ifthenelse (bool true)
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y)))
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))))
                 (mtEnv))
      (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta))))


(test (typecheck (ifthenelse (equ (num 8) (num 8))
                             (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x))))
                             (tfun 'beta (tfun 'gamma (fun 'x (tvTE 'beta) (id 'x)))))
                 (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha)
                                   (tfun 'beta (fun 'y (tvTE 'alpha)
                                                    (ifthenelse (bool true)
                                                                (id 'x)
                                                                (id 'y))))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha)
                            (polyT 'beta (arrowT (tvT 'alpha)
                                                 (tvT 'alpha))))))

(test (interp (app
               (tapp (ifthenelse (bool true)
                                 (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
                                 (tfun 'beta (fun 'x (tvTE 'beta) (id 'x))))
                     (numTE)) (num 30)) (mtSub))
      (numV 30))
      
(test (interp
       (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))
                 (app (tapp (id 'x) (numTE)) (num 10)))
        (tfun 'beta (fun 'y (tvTE 'beta) (id 'y)))) (mtSub)) (numV 10))
        
(test (typecheck
       (tfun 'alpha
             (fun 'alpha (arrowTE (numTE) (numTE))
                  (fun 'x (tvTE 'alpha)
                       (id 'x)))) (mtEnv))
      (polyT 'alpha (arrowT (arrowT (numT) (numT)) (arrowT (tvT 'alpha) (tvT 'alpha)))))
      
(test (typecheck
       (fun 'alpha (arrowTE (numTE) (numTE))
            (tfun 'alpha
                  (fun 'x (tvTE 'alpha)
                       (id 'x)))) (mtEnv))
      (arrowT (arrowT (numT) (numT)) (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (interp (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (num 5))) (numTE)) (mtSub)) (closureV 'x (num 5) (mtSub)))

(test (interp (tapp (tfun 'alpha (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha))) (id 'x))) (numTE)) (mtSub)) (closureV 'x (id 'x) (mtSub)))

(test (typecheck (tapp (tfun 'alpha (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha))) (id 'x))) (numTE)) (mtEnv)) (arrowT (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha)))))

(test (typecheck (tapp (tfun 'alpha (fun 'x (tvTE 'alpha) (num 5))) (numTE)) (mtEnv)) (arrowT (numT) (numT)))

(test (interp (app (app (tapp (tapp (tfun 'alpha (tfun 'beta (fun 'x (arrowTE (tvTE 'alpha) (tvTE 'beta)) (id 'x))))
                                    (numTE))
                              (numTE))
                        (fun 'x (numTE) (add (num 5) (id 'x))))
                   (num 3))
              (mtSub))
      (numV 8))

(test (interp (app (app (tapp (tapp (tfun 'alpha (tfun 'alpha (fun 'x (arrowTE (tvTE 'alpha) (tvTE 'alpha)) (id 'x))))
                                    (numTE))
                              (numTE))
                        (fun 'x (numTE) (add (num 5) (id 'x))))
                   (num 3))
              (mtSub))
      (numV 8))
(test (typecheck (ifthenelse (equ (num 8) (num 10))
                             (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (fun 'y (tvTE 'beta) (id 'y)))))
                             (tfun 'beta (tfun 'alpha (fun 'x (tvTE 'beta) (fun 'y (tvTE 'alpha) (id 'y))))))
                 (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (arrowT (tvT 'beta) (tvT 'beta))))))

(test (typecheck (tapp (tfun 'alpha
                                 (fun 'alpha (tvTE 'alpha)
                                      (app (fun 'x (polyTE 'alpha (arrowTE (tvTE 'alpha) (tvTE 'alpha)))
                                           (app (tapp (id 'x) (numTE)) (num 10))) (tfun 'alpha
                                                                                        (fun 'alpha (tvTE 'alpha)
                                                                                             (id 'alpha)))))) (numTE))
          (mtEnv)) (arrowT (numT) (numT)))

(test (typecheck (tfun 'alpha (num 3)) (mtEnv))
      (polyT 'alpha (numT)))

(test (typecheck (tfun 'alpha (tfun 'beta (num 3))) (mtEnv))
      (polyT 'alpha (polyT 'beta (numT))))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))) (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (tapp (id 'f) (numTE)) (aBind 'f (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))) (mtEnv)))
      (arrowT (numT) (numT)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test (typecheck (ifthenelse (bool true)
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x)))
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha) (tvT 'alpha))))

(test (typecheck (ifthenelse (bool true)
                             (tfun 'beta (fun 'y (tvTE 'beta) (id 'y)))
                             (tfun 'alpha (fun 'x (tvTE 'alpha) (id 'x))))
                 (mtEnv))
      (polyT 'beta (arrowT (tvT 'beta) (tvT 'beta))))


(test (typecheck (ifthenelse (bool true)
                             (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x))))
                             (tfun 'beta (tfun 'gamma (fun 'x (tvTE 'beta) (id 'x)))))
                 (mtEnv))
      (polyT 'alpha (polyT 'beta (arrowT (tvT 'alpha) (tvT 'alpha)))))


(test (interp (tapp (tapp (tfun 'alpha (tfun 'beta (num 3))) (numTE)) (numTE)) (mtSub))
      (numV 3))

(test (typecheck (tfun 'alpha (fun 'x (tvTE 'alpha)
                                   (tfun 'beta (fun 'y (tvTE 'alpha)
                                                    (ifthenelse (bool true)
                                                                (id 'x)
                                                                (id 'y))))))
                 (mtEnv))
      (polyT 'alpha (arrowT (tvT 'alpha)
                            (polyT 'beta (arrowT (tvT 'alpha)
                                                 (tvT 'alpha))))))


;;; tests on noah 234th article
(test (typecheck (fun 'x (polyTE 'alpha (tvTE 'alpha)) (id 'x)) (mtEnv))
      (arrowT (polyT 'alpha (tvT 'alpha)) (polyT 'alpha (tvT 'alpha))))

;;; tests on noah 236th article
(test (typecheck (tapp (tfun 'alpha (tfun 'beta (fun 'x (polyTE 'alpha (polyTE 'beta (tvTE 'alpha))) (id 'x)))) (numTE)) (mtEnv))
      (polyT 'beta (arrowT (polyT 'alpha (polyT 'beta (tvT 'alpha))) (polyT 'alpha (polyT 'beta (tvT 'alpha))))))

(test (typecheck (app (tapp (tapp (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x)))) (numTE)) (numTE)) (num 10)) (mtEnv)) (numT))
(test (interp (app (tapp (tapp (tfun 'alpha (tfun 'beta (fun 'x (tvTE 'alpha) (id 'x)))) (numTE)) (numTE)) (num 10)) (mtSub)) (numV 10))  |#