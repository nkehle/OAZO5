#lang typed/racket
(require typed/rackunit)

;; Assignment 5
;; ...


;; OAZO Data Definitions
;;-----------------------------------------------------------------------------------
;; Expressions
(struct numC    ([n : Real])                                   #:transparent)
(struct idC     ([s : Symbol])                                 #:transparent)
(struct appC    ([exp : ExprC] [args : (Listof ExprC)])        #:transparent)
(struct ifC     ([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct stringC ([str : String])                               #:transparent)
(struct lamC    ([args : (Listof Symbol)] [body : ExprC])      #:transparent)
(define-type ExprC (U numC idC appC ifC stringC lamC))

;; Bindings
(struct binding ([name : Symbol] [val : Value])                #:transparent)
(struct Env     ([lst : (Listof binding)])                     #:transparent)
(define mt-env  '())
(define extend-env cons)

;; Values
(struct numV    ([n : Real])                                   #:transparent)
(struct boolV   ([b : Boolean])                                #:transparent)
(struct closeV  ([arg : Symbol] [body : ExprC] [env : Env])    #:transparent)
(struct primopV ([sym : Symbol])                               #:transparent)
(define-type Value (U numV closeV boolV primopV))

;; Top Level Environment
(define top-env
  (Env (list (binding 'true (boolV #t))
             (binding 'false (boolV #f))
             (binding '+ (primopV '+))
             (binding '- (primopV '-))
             (binding '* (primopV '*))
             (binding '/ (primopV '/))
             (binding '<= (primopV '<=))
             (binding 'equal? (primopV 'equal?))
             (binding 'error (primopV 'error)))))

;; TOP-INTERP
;;-----------------------------------------------------------------------------------
;; Interprets the entirely parsed program
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))


;; INTERP
;;-----------------------------------------------------------------------------------
;; Inteprets the given expression using list of funs to resolve appC's
(define (interp [e : ExprC] [env : Env]) : Value
  (match e
    [(numC n) (numV n)]
    [(idC s) (lookup s env)]  ;; Is this where the '+ '- '/ ... operators would be found?
    #;[(stringC str)         #;TODO]
    [(ifC test then else)    #;TODO
     (if (interp test env))
         (interp then env)
         (interp else env)]
    
    ;;So before we interp the appC there is no closure, only the current environment
    [(appC f args) (define ([define f-value (interp f env)]) ;;Current env
                     ;;(cond
                       ;;[(equal? f-value primopV) (primopV f-value env)]) ;;Probably don't use a cond here
                     (interp (closeV-body f-value)               ;;Current env
                             (extend-env (binding (closeV-arg f-value)
                                                  (map(lambda ([a : ExprC]) (interp a env)) args)) ;;possiblhy map interp
                                         env)))] 
    [(lamC a b) (closeV a b env)]))


;; SERIALIZE
;;-----------------------------------------------------------------------------------
;; Turns objects into string literals
(define (serialize [val : Any]) : String
  (match val
    [(? numV? n) (number->string (numV-n n))]
    [(? closeV? s) (format "~a" s)]
    [#t "true"]
    [#f "false"]
    #;[(? procedure? p) "#<procedure>"]
    #;[(? primop? p) "#<primop>"]
    [else (error 'serialize "Unsupported value: ~v" val)]))


;; LOOKUP
;;-----------------------------------------------------------------------------------
;; Helper that looks up a value in an environment
(define (lookup [for : Symbol] [env : Env]) : Number
    (match env
      ['() (error 'lookup "OAZO ERROR: name not found: ~e" for)]
      [(cons (binding name val) r) (cond
                    [(symbol=? for name) val]
                    [else (lookup for r)])]))

;; GET-PRIMOP
;;-----------------------------------------------------------------------------------
(define (get-primop [op : primopV] [env : Env]) : Value
  (cond
    [(> (length (Env-lst env)) 2) (error 'get-primop "OAZO ERROR:  illegal number of operands for primitave type: ~e" env)] 
    [else
     (match (binding-val (first (Env-lst env)))
       [(? numV?) (match (binding-val (first(rest (Env-lst env))))
                    [(? numV?)
                     (match op
                       [(primopV '+)(numV(+ (numV-n(cast (binding-val (first (Env-lst env))) numV)) (numV-n (cast (binding-val (first(rest (Env-lst env)))) numV))))]
                       [(primopV '-)(numV(- (numV-n(cast (binding-val (first (Env-lst env))) numV)) (numV-n (cast (binding-val (first(rest (Env-lst env)))) numV))))]
                       [(primopV '*)(numV(* (numV-n(cast (binding-val (first (Env-lst env))) numV)) (numV-n (cast (binding-val (first(rest (Env-lst env)))) numV))))]
                       [(primopV '/)(numV(/ (numV-n(cast (binding-val (first (Env-lst env))) numV)) (numV-n (cast (binding-val (first(rest (Env-lst env)))) numV))))]
                       [(primopV '<=)(boolV(<= (numV-n(cast (binding-val (first (Env-lst env))) numV)) (numV-n (cast (binding-val (first(rest (Env-lst env)))) numV))))] 
                       [else (error 'get_primop "OAZO ERROR: Not a number: ~e" (binding-val (first(rest (Env-lst env)))))])])])]))  

;; Get-primop Tests
(check-equal? (get-primop (primopV '+) (Env (list (binding 'x (numV 1)) (binding 'y (numV 2))))) (numV 3))
(check-equal? (get-primop (primopV '-) (Env (list (binding 'x (numV 4)) (binding 'y (numV 2))))) (numV 2)) 
(check-equal? (get-primop (primopV '*) (Env (list (binding 'x (numV 3)) (binding 'y (numV 2))))) (numV 6))
(check-equal? (get-primop (primopV '/) (Env (list (binding 'x (numV 10)) (binding 'y (numV 2))))) (numV 5))
(check-equal? (get-primop (primopV '<=) (Env (list (binding 'x (numV 10)) (binding 'y (numV 2))))) (boolV #f))


;; HELPER FUNCTIONS
;;-----------------------------------------------------------------------------------
;; Helper function to check if all elements of a list are symbols
(define (all-symbol-and-valid? [lst : (Listof Sexp)]) : Boolean
  (andmap (lambda (s)
            (and (symbol? s) (valid-id s)))
          lst))

;; Helper to determine if the id is valid for an idC
(define (valid-id [s : Symbol]) : Boolean
  (match s
    [(or '? 'else: 'with 'as 'blam) #f]
    [other #t]))


;; PARSE
;;-----------------------------------------------------------------------------------
;; Takes in a Sexp of concrete syntax and outputs the AST for the OAZO language
;; should only be in the form of the above defined data types
(define (parse [code : Sexp]) : ExprC
  (match code
    [(? real? n) (numC n)]                                 ;; numC
    [(list (? real? n)) (numC n)]                          ;; numC in {12}
    [(and (? symbol? s) (? valid-id s)) (idC s)]           ;; idC
    [(? string? str) (stringC str)]                        ;; stringC
    [(list 'if test 'then then 'else else)                 ;; ifC
     (ifC (parse test) (parse then) (parse else))]

    #;[(list 'let (list (and (? symbol? s) (? valid-id s)) '<- exp) ... body) ;;  {let [id <- Expr] ... Expr} 
     (appC let-helper lst)]          	                   

    [(list 'anon syms ': body args ...)                    ;; lamC
     (if (and (list? syms) (all-symbol-and-valid? syms))
         (lamC (cast syms(Listof Symbol)) (parse body))
         (error 'parse "OAZO Error: Expected a list of symbols for parameters"))]
    
    [(list func exps ...)                                  ;; appC
     (appC (parse func) (map (lambda ([exps : Sexp])
                    (parse exps)) exps))]
    
    [other (error 'parse "OAZO Syntax error in ~e" other)]))


;; Tests
(check-equal? (parse '{12}) (numC 12))
(check-equal? (parse 'x) (idC 'x))
(check-equal? (parse "string") (stringC "string"))
(check-equal? (parse '{anon {x y} : {+ x y}})
              
              (lamC (list 'x 'y)
                    (appC (idC '+)
                          (list (idC 'x) (idC 'y)))))

(check-equal? (parse '{{anon {x y} : {+ x y}} 5 7})
              
              (appC (lamC (list 'x 'y)
                          (appC (idC '+)
                                (list (idC 'x) (idC 'y))))
              (list (numC 5)
                    (numC 7))))

(check-equal? (parse '{f 4}) (appC (idC 'f) (list(numC 4))))

















;; OLD CODE
;;-----------------------------------------------------------------------------------
    
;; Helper to determine if the symbol is valid for an idC
#;(define (symbol-valid [s : Symbol]) : Boolean
  (match s
    [(or '+ '- '* '/ 'ifleq0? 'else: 'ifleq0? ': 'func) #f]
    [other #t]))

;; Helper to determine if its a valid operand
#;(define (operand-valid [s : Symbol]) : Boolean
  (match s
    [(or '+ '- '* '/) #t]
    [ other #f]))

;; Helper to check if a list of symbols is valid
#;(define (list-of-symbols? lst)
  (and (list? lst)
       (andmap symbol? lst)
       (andmap symbol-valid lst)))

;; Helper for searching through the list of funs
#;(define (get-fundef [n : Symbol] [fds : (Listof fdC)]) : fdC
  (cond
    [(empty? fds) (error 'get-fundef "OAZO Error: Reference to undefined function ~e" n)]
    [(cons? fds) (cond
                   [(equal? n (fdC-name (first fds))) (first fds)]
                   [else (get-fundef n (rest fds))])]))


#;[(list (and (? symbol? op) (? operand-valid s)) l r) ;; biopC
     (binopC s (parse l) (parse r))]
    
    #;[(list 'ifleq0? test then else)                      ;; ifleq0?
     (ifleq0? (parse test) (parse then) (parse else))]
    

;; Helper thats used to subsitutue values in place for identifiers inside of ExprC's
#;(define (sub [what : ExprC] [for : Symbol] [in : ExprC]) : ExprC
  (match in
    [(numC n) in]
    [(idC s) (if (equal? s for) what in)]
    [(binopC op l r) (binopC op (sub what for l) (sub what for r))]
    [(appC f args) (appC f (map (lambda ([arg : ExprC])
                                  (sub what for arg)) args))]
    [(ifleq0? test then else) (ifleq0? (sub what for test)
                                       (sub what for then)
                                       (sub what for else))]))

;; Helper that takes a list of ExprC and List of Symbol and an ExprC and replaces the
;; first exprc with the first symbol and then the second and so forth 
#;(define (sub-many [args : (Listof ExprC)] [syms : (Listof Symbol)] [in : ExprC] [fds : (Listof fdC)]) : ExprC
  (if (not (= (length args) (length syms)))
      (error 'sub-many "OAZO Error: Mismatched number of arguments and symbols")
      (match args
        ['() in] ;; base case: argument list is empty
        [(cons arg rest-args)
         (match syms
           [(cons sym rest-syms)
            (sub-many rest-args rest-syms
                      (sub (numC (interp arg fds)) sym in) fds)])])))

;; INTERP-FNS
;;-----------------------------------------------------------------------------------
;; Inteprets the function named main from the func definitons
#;(define (interp-fns [funs : (Listof fdC)]) : Real
  (let ([main-fd (get-fundef 'main funs)])
    (define body (fdC-body main-fd))
    (interp body funs)))



;; PARSE-PROG 
;;-----------------------------------------------------------------------------------
;; Takes in the whole program and parses the function definitions and outputs
;; the list of all fdC's
#;(define (parse-prog [s : Sexp]) : (Listof fdC)
  (match s
    ['() '()]
    [(cons f r) (cons (parse-fundef f) (parse-prog r))] 
    [other (error 'parse-prog "OAZO Syntax Error: Function with invalid syntax in ~e" other)]))


;; PARSE-FUNDEF
;;-----------------------------------------------------------------------------------
;; Takes in an Sexp and parses it into and function definition for the OAZO language
#;(define (parse-fundef [code : Sexp]) : fdC
  (match code
    [(list 'func (list 'main) ': body)
     (fdC 'main '() (parse body))]
    [(list 'func (list (and (? symbol? name) (? symbol-valid name)) args ...) ': body)
     (if (list-of-symbols? args) 
         (fdC name (cast args (Listof Symbol)) (parse body))
         (error 'parse-func-def "OAZO Syntax Error: ~e" code))]
    [else (error 'parse-func-def "OAZO Syntax Error: ~e" code)]))


#;[(binopC op a b) (match op
                       ['+ (+ (interp a fds) (interp b fds))]
                       ['- (- (interp a fds) (interp b fds))]
                       ['* (* (interp a fds) (interp b fds))]
                       ['/ (let ([right-val (interp b fds)])
                             (if (not (= right-val 0))
                                 (/ (interp a fds) right-val)
                                 (error 'interp "OAZO Arithmetic Error: Division by zero")))])]
;; TESTS
;;-----------------------------------------------------------------------------------
#|
;; Tests for symbol-valid
(check-equal? (symbol-valid '+) #f)
(check-equal? (symbol-valid '-) #f)
(check-equal? (symbol-valid '*) #f)
(check-equal? (symbol-valid '/) #f)
(check-equal? (symbol-valid 'ifleq0?) #f)
(check-equal? (symbol-valid 'else:) #f)
(check-equal? (symbol-valid ':) #f)
(check-equal? (symbol-valid 'func) #f)
(check-equal? (symbol-valid 'x) #t)

;; Tests for operand-valid
(check-equal? (operand-valid '+) #t)
(check-equal? (operand-valid '-) #t)
(check-equal? (operand-valid '*) #t)
(check-equal? (operand-valid '/) #t)

;; Parse Tests
(check-equal? (parse 5) (numC 5))
(check-equal? (parse '{+ 2 3}) (binopC '+ (numC 2) (numC 3)))
(check-equal? (parse '{* {+ 2 3} 4}) (binopC '* (binopC '+ (numC 2) (numC 3)) (numC 4)))
(check-equal? (parse '{ifleq0? x x {+ x 1}}) (ifleq0? (idC 'x) (idC 'x) (binopC '+ (idC 'x) (numC 1))))
(check-equal? (parse 'a) (idC 'a))
(check-equal? (parse '{f {* 2 1}}) (appC 'f (list (binopC '* (numC 2) (numC 1)))))
(check-exn #rx"Syntax error" (lambda() (parse '{* 2})))
(check-exn #rx"Syntax error" (lambda() (parse '{+ 2 3 4})))
(check-exn #rx"Syntax error" (lambda() (parse '{+ func a})))
(check-equal? (parse '{f 1 2 3}) (appC 'f (list (numC 1) (numC 2)(numC 3))))

;; Parse FunDef Tests
(check-equal? (parse-fundef '{func {f x} : {+ x 14}})
              (fdC 'f '(x) (binopC '+ (idC 'x) (numC 14))))

(check-equal? (parse-fundef '{func {f y} : {* y 2}})
              (fdC 'f '(y) (binopC '* (idC 'y) (numC 2))))

(check-equal? (parse-fundef '{func {f x} : {6}})
              (fdC 'f '(x) (numC 6)))

(check-equal? (parse-fundef '{func {main} : {6}})
              (fdC 'main '() (numC 6)))

(check-exn #rx"OAZO Syntax Error:" (lambda() (parse-fundef '{func {+ x} : 12})))
(check-exn #rx"OAZO Syntax Error:" (lambda() (parse-fundef '{func {f +} : 12})))

;; Parse-prog Tests
(check-equal? (parse-prog '{{func {f x} : {+ x 14}}
                            {func {main} : {f 2}}})
              (list (fdC 'f '(x) (binopC '+ (idC 'x) (numC 14)))
                    (fdC 'main '() (appC 'f (list (numC 2))))))

(check-exn #rx"parse-func-def" (lambda() (parse-prog '{12 {func {main} : {f 2}}})))
(check-exn #rx"parse-prog" (lambda() (parse-prog '12)))


;; Sub Tests
(check-equal? (sub (numC 5) 'x (idC 'x))
              (numC 5))
(check-equal? (sub (numC 5) 'x (binopC '+ (idC 'x) (numC 1)))
              (binopC '+ (numC 5) (numC 1)))
(check-equal? (sub (numC 5) 'y (idC 'x))
              (idC 'x))
(check-equal? (sub (numC 5) 'y (binopC '+ (idC 'x) (numC 1)))
              (binopC '+ (idC 'x) (numC 1)))
(check-equal? (sub (numC 5) 'y (appC 'f (list (idC 'y))))
              (appC 'f (list(numC 5))))
(check-equal? (sub (numC 5) 'y (ifleq0? (idC 'y) (numC 10) (numC 20)))
              (ifleq0? (numC 5) (numC 10) (numC 20)))

;; Interp Tests
(define fds(list (fdC 'f '(x) (binopC '+ (idC 'x) (numC 1)))
                 (fdC 'g '(x) (binopC '* (idC 'x) (numC 2)))))
(define fds-list (list (fdC 'f '(x y) (binopC '+ (idC 'x) (idC 'y)))))
(check-equal? (interp (numC 5) fds) 5)
(check-equal? (interp (binopC '+ (numC 3) (numC 2)) fds) 5)
(check-equal? (interp (binopC '- (numC 3) (numC 2)) fds) 1)
(check-equal? (interp (binopC '* (numC 3) (numC 2)) fds) 6)
(check-equal? (interp (binopC '/ (numC 10) (numC 5)) fds) 2)
(check-equal? (interp (binopC '+ (binopC '* (numC 2) (numC 3)) (numC 4)) fds) 10)
(check-equal? (interp (parse '{ifleq0? 10 3 -1}) fds) -1)
(check-equal? (interp (parse '{ifleq0? -12 3 -1}) fds) 3)
(check-equal? (interp (parse '{f 12}) fds) 13)
(check-equal? (interp (appC 'f (list (numC 2) (numC 3))) fds-list) 5)
(check-exn #rx"Interp of an idC" (lambda () (interp (idC 'x) fds)))
(check-exn #rx"OAZO"(lambda() (interp (binopC '/ (numC 10) (numC 0)) fds)))


;; Top-Interp Tests
(check-equal? (top-interp
               '{{func {minus-five x} : {+ x {* -1 5}}}
                 {func {main} : {minus-five {+ 8 0}}}}) 3)

(check-equal? (top-interp
               '{{func {minus-five x} : {+ x {* -1 5}}}
                 {func {main} : {minus-five {+ 8 0}}}}) 3)

(check-equal? (top-interp
               '{{func {f x} : {+ x 14}}
                 {func {main} : {f 2}}}) 16)

(check-equal? (top-interp
               '{{func {f x y z} : {+ (+ x y) z}}
                 {func {main} : {f 1 2 3}}}) 6)

(check-equal? (top-interp
               '{{func {realtwice x} : {+ x x}}
                 {func {main} : {twice 15}}
                 {func {twice x} : {realtwice x}}}) 30)


(check-equal? (top-interp
               '{{func {g x} : {ifleq0? x 0
                                        {+ {g {- x 1}} x}}}
                 {func {main} : {g 3}}}) 6)

(check-equal? (interp-fns
               (parse-prog '{{func {f x y} : {+ x y}}
                             {func {main} : {f 1 2}}}))
              3)

(check-equal? (interp-fns
               (parse-prog '{{func {f} : 5}
                             {func {main} : {+ {f} {f}}}}))
              10)

(check-exn #px"OAZO" (lambda ()
                       (interp-fns
                        (parse-prog '{{func {f x y} : {+ x y}}
                                      {func {main} : {f 1}}}))))

(check-exn #rx"OAZO" (lambda () (top-interp
                                 '{{func {f x y} : {+ x y}}
                                   {func {main} : {f 1 2 3}}})))

(check-exn #rx"OAZO" (lambda () (top-interp
                                 '{{func {f x y z} : {+ {+ x y} z}}
                                   {func {main} : {f 1 2}}})))

(check-exn #rx"OAZO" (lambda()         
                       (top-interp '{{func {f x y} : {+ x 2}}   
                                     {func {main} : {f 3}}})))  

(check-exn #rx"OAZO" (lambda()
                       (top-interp '{{func {f x y} : {+ × 2}}
                                     {func {main} : {f 3}}})))

(check-exn #rx"OAZO" (lambda() (top-interp
                                '12)))

(check-exn #rx"OAZO" (lambda() (top-interp
                                '{{func {f x} : {+ x 14}}
                                  {func {g y} : {f 2}}})))

(check-exn #rx"OAZO" (lambda() (top-interp
                                '{{func {ignoreit x}: {+ 3 4}}
                                  {func {main} : {ignoreit {/ 1 {+ 0 0}}}}})))

|#
;;---------------------------------------------------------------------------------