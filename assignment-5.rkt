#lang typed/racket
(require typed/rackunit)

;; Assignment - OAZO6
;; Full Project Implemented


;; OAZO Data Definitions
;;-----------------------------------------------------------------------------------
;; Expressions
(struct numC    ([n : Real])                                   #:transparent)
(struct idC     ([s : Symbol])                                 #:transparent)
(struct appC    ([exp : ExprC] [args : (Listof ExprC)])        #:transparent)
(struct ifC     ([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct strC    ([str : String])                               #:transparent)
(struct lamC    ([args : (Listof Symbol)] [body : ExprC])      #:transparent)
(struct arrC    ([args : (Listof ExprC)])                      #:transparent)
(struct setarrC ([array : ExprC] [val : ExprC])                #:transparent)
(define-type ExprC (U numC idC appC ifC strC lamC arrC setarrC))

;; Values
(struct numV    ([n : Real])                                   #:transparent)
(struct boolV   ([b : Boolean])                                #:transparent)
(struct strV    ([str : String])                               #:transparent)
(struct numarrV ([nums : (Listof Real)])                       #:transparent)
(struct closeV  ([arg : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct primopV ([sym : Symbol])                               #:transparent)
(struct nullV   ()                                             #:transparent)
(define-type Value (U numV closeV boolV primopV strV numarrV nullV))

;; Bindings
(struct env-binding   ([name : Symbol]  [val : Location])       #:transparent)
(struct store-binding ([loc : Location] [val : Value])          #:transparent)
(define-type Env (Listof env-binding))
(define mt-env  '())

;; Store
(define-type Location Real)
(struct Store ([bindings : (Listof store-binding)] [next : Real])       #:transparent)
(struct v*s   ([val : Value] [sto : Store])                             #:transparent)
(struct lv*s  ([lst : (Listof Value)] [sto : Store]))
(define overide-store cons)


;; Top Level Envirnment
(define top-env
  (list (env-binding 'false 0)
        (env-binding 'true 1)
        (env-binding '+ 2)
        (env-binding '- 3)
        (env-binding '* 4)
        (env-binding '/ 5)
        (env-binding '<= 6)
        (env-binding 'equal? 7)
        (env-binding 'num-eq? 8)
        (env-binding 'str-eq? 9)
        (env-binding 'error 10)
        (env-binding 'arr 11)
        (env-binding 'aref 12)
        (env-binding 'aset! 13)
        (env-binding 'alen 14)
        (env-binding 'seq 15)
        (env-binding 'substirng 16)))

;; Top Level Store
(define top-sto
  (Store
   (list (store-binding 0 (boolV #f))
         (store-binding 1 (boolV #t))
         (store-binding 2 (primopV '+))
         (store-binding 3 (primopV '-))
         (store-binding 4 (primopV '*))
         (store-binding 5 (primopV '/))
         (store-binding 6 (primopV '<=))
         (store-binding 7 (primopV 'equal?))
         (store-binding 8 (primopV 'num-eq?))
         (store-binding 9 (primopV 'str-eq?))
         (store-binding 10 (primopV 'error))
         (store-binding 11 (primopV 'arr))
         (store-binding 12 (primopV 'aref))
         (store-binding 13 (primopV 'aset!))
         (store-binding 14 (primopV 'alen))
         (store-binding 15 (primopV 'seq))
         (store-binding 16 (primopV 'substring))) 17))



;; TOP-INTERP
;;-----------------------------------------------------------------------------------
;; Interprets the entirely parsed program
(define (top-interp [s : Sexp]) : String
  (serialize (v*s-val (interp (parse s) top-env top-sto))))


;; INTERP
;;-----------------------------------------------------------------------------------
;; Inteprets the given expression using list of funs to resolve appC's
(define (interp [e : ExprC] [env : Env] [sto : Store]) : v*s
  (match e
    [(numC n) (v*s (numV n) sto)]                                       ;; numC 
    [(idC s) (v*s (fetch (lookup s env) (Store-bindings sto)) sto)]     ;; idC
    [(appC f a)
     (define func    (interp f env sto))
     (define args    (interp-args a env (v*s-sto func)))
     (define new-sto (lv*s-sto args))
     (match (v*s-val func)
       [(? primopV?) (apply-primop (v*s-val func) (lv*s-lst args) env new-sto)] 
       [else (error 'interp "OAZO Unsupported value for interp: ~v" func)])] 
    [other (error 'unimplemented)]))


;; Helper to interpret the args and thread the store through 
(define (interp-args [args : (Listof ExprC)] [env : Env] [sto : Store]) : lv*s
 (cond
   [(empty? args) (lv*s '() sto)]
   [else (define res (interp (first args) env sto))
         (define tail (interp-args (rest args) env (v*s-sto res)))
    (lv*s (cons (v*s-val res) (lv*s-lst tail)) (lv*s-sto tail))]))



    
    #;[(strC str) (strV str)]      ;; strC
    #;[(ifC test then else)        ;; ifC
     (define test-result (interp test env)) 
     (cond [(boolV? test-result)
            (cond [(boolV-b test-result) (interp then env)]
                  [else (interp else env)])]
           [else (error 'interp "OAZO: Test was not a boolean expression: ~e" e)])] 
    #;[(appC f args) (define f-value : Value (interp f env)) ;;Current env
                   (match f-value
                     [(? closeV?) (check-args (closeV-arg f-value) args)
                                   (interp (closeV-body f-value)               ;;Current env
                                          (extend-env (bind (closeV-arg f-value)
                                                            (map(lambda ([a : ExprC]) (interp a env)) args))
                                                      (closeV-env f-value)))]
                     [(? primopV?) (apply-primop f-value args env)] 
                     [else (error 'interp "OAZO Unsupported value for interp: ~v" f-value)])] 
     
    #;[(lamC a body) (closeV a body env)]

;; Helper to interp the args for apply primop
#;(define (interp-primop [args : (Listof ExprC)] [env : Env] [sto : Store]) : (Listof Value)
 (let ([arg-values (map (λ ([arg : ExprC])
                              (result-val (interp arg env sto))) args)]) arg-values))


;; Takes a primop an list of args and the environment and ouputs the value 
(define (apply-primop [primop : primopV] [args : (Listof Value)] [env : Env] [sto : Store]) : v*s
  (cond
    [(equal? args '()) (error 'apply "OAZO no args given ~v" args)]
    [else
     (define f      (first args))
     (define second (first (rest args)))
     (match primop 
       [(primopV '+)
        (if (and (numV? f) (numV? second)) (v*s (numV (+ (numV-n f) (numV-n second))) sto)
            (error 'apply-primop "OAZO ERROR: Non-numeric argument for add"))]
       [(primopV '-)
        (if (and (numV? f) (numV? second)) (v*s (numV (- (numV-n f) (numV-n second))) sto)
            (error 'apply-primop "OAZO ERROR: Non-numeric argument for sub"))]
       [(primopV '*)
        (if (and (numV? f) (numV? second)) (v*s (numV (* (numV-n f) (numV-n second))) sto)
            (error 'apply-primop "OAZO ERROR: Non-numeric argument for mult"))]
       [(primopV '/) 
        (cond
          [(equal? (numV 0) second) (error 'apply-primop "OAZO ERROR: Divide by zero!")]
          [else (if (and (numV? f) (numV? second)) (v*s (numV (/ (numV-n f) (numV-n second))) sto)
                    (error 'apply-primop "OAZO ERROR: Non-numeric argument for div"))])]
       [(primopV '<=)
        (if (and (numV? f) (numV? second)) (v*s (boolV (<= (numV-n f) (numV-n second))) sto)
            (error 'apply-primop "OAZO ERROR: Non-numeric argument for <="))]
       [(primopV 'num-eq?)
        (if (and (numV? f) (numV? second)) (v*s (boolV (equal? (numV-n f) (numV-n second))) sto)
            (error 'apply-primop "OAZO ERROR: Non-numeric argument for num-eq?"))]
      [(primopV 'str-eq?)
        (if (and (strV? f) (strV? second)) (v*s (boolV (equal? (strV-str f) (strV-str second))) sto)
            (error 'apply-primop "OAZO ERROR: Non-numeric argument for str-eq?"))]
       
       [(primopV 'arr)
        (if (and (numV? f) (numV? second)) (v*s (numarrV (arr (numV-n f) (numV-n second))) sto)
            (error 'apply-primop "OAZO ERROR: Non-numeric argument for <="))])]))


;; Creates a new array of given size and fills with a value
(define (arr [size : Real] [num : Real]) : (Listof Real)
  (if (zero? size) '()
      (cons num (arr (- size 1) num))))


;; Returns the elemnt of the numarray at a given index
#;(define (aref [array : numarrV] [idx : Real]) : Real
  (cond
    [(< idx 0) (error 'aref "OAZO: Index out of bounds: ~a" idx)]
    [(>= idx (length (numarrV-nums array))) (error 'aref "OAZO: Index out of bounds: ~a" idx)]
    #;[else (index idx (numarrV-nums array))])) 



;; Questions
;; What value does new-array make?
;; Is the contents of an array a bunch of boxes? or is a list of real?


;; PARSE
;;-----------------------------------------------------------------------------------
;; Takes in a Sexp of concrete syntax and outputs the AST for the OAZO language
;; should only be in the form of the above defined data types
(define (parse [code : Sexp]) : ExprC
  (match code
    [(? real? n) (numC n)]                                 ;; numC
    [(list (? real? n)) (numC n)]                          ;; numC in {12}
    [(and (? symbol? s) (? valid-id s)) (idC s)]           ;; idC
    [(? string? str) (strC str)]                           ;; stringC
    [(list 'if test 'then then 'else else)                 ;; ifC
     (ifC (parse test) (parse then) (parse else))]
    [(list _ '<- _) (error 'parse "OAZO")]                 ;; weird case of bindingds and body being switched
    [(list 'let bindings ... body)                         ;; letC
     (if (check-duplicates (parse-binding-syms (cast bindings (Listof Sexp)))) 
     (appC (lamC (parse-binding-syms (cast bindings (Listof Sexp))) 
                 (parse body))
           (parse-binding-args (cast bindings (Listof Sexp))))
     (error 'parse "OAZO Error: Expected a list of non-duplicate symbols for parameters"))]

    [(list 'anon syms ': body)                    ;; lamC
     (if (and (list? syms) (all-symbol-and-valid? syms) (check-body body))
         (lamC (cast syms(Listof Symbol)) (parse body))
         (error 'parse "OAZO Error: Expected a list of non-duplicate symbols for parameters in ~e" code))]
    
    [(list func exps ...)                                  ;; appC
     (appC (parse func) (map (lambda ([exps : Sexp])
                    (parse exps)) exps))]
    
    [other (error 'parse "OAZO Syntax error in ~e" other)]))


;; SERIALIZE
;;-----------------------------------------------------------------------------------
;; Turns objects into string literals
(define (serialize [val : Any]) : String
  (match val
    [(? numV? n) (number->string (numV-n n))]
    [(? real? n) (number->string n)]
    [(? closeV? s) "#<procedure>"]
    [(? strV? str) (string-append "\"" (strV-str str) "\"")] 
    [(boolV #t) "true"]
    [#t "true"]
    [(boolV #f) "false"]
    [#f "false"]
    [(? primopV? p) "#<primop>"]
    [(nullV) "null"]
    #;[(numarrV arr) (list->string arr)]
    [else (error 'serialize "OAZO Unsupported value: ~v" val)]))



;; HELPER FUNCTIONS
;;-----------------------------------------------------------------------------------

;; Helper to check the number of param vs given arguments
(define (check-args [param : (Listof Symbol)] [args : (Listof ExprC)]) : Boolean
  (if (>= (length param) (length args)) #t
      (error 'check-args "OAZO mismatch number of arguments")))


;; Helper that looks up a value in an environment
(define (lookup [for : Symbol] [env : Env]) : Location
    (match env
      ['() (error 'lookup "OAZO ERROR: name not found: ~e" for)]
      [(cons (env-binding name location) r) (cond
                                     [(symbol=? for name) location]
                                     [else (lookup for r)])]))

;; Helper that looks up a value in an environment
(define (fetch [loc : Location] [store : (Listof store-binding)]) : Value
    (match store
      ['() (error 'lookup "OAZO ERROR: location not found: ~e" loc)]
      [(cons (store-binding location val) r) (cond
                                     [(equal? location loc) val]
                                     [else (fetch loc r)])]))

;; Helper function to check if all elements of a list are symbols
(define (all-symbol-and-valid? [lst : (Listof Sexp)]) : Boolean
  (and (andmap (lambda (s)
            (and (symbol? s) (valid-id s)))
          lst) (check-duplicates lst)))

;; Helper to determine if the id is valid for an idC
(define (valid-id [s : Symbol]) : Boolean
  (match s
    [(or '? 'else: 'then 'with 'as 'blam ':) #f]
    [other #t]))

;; Checks for duplicate parameter names
(define (check-duplicates [lst : (Listof Sexp)]) : Boolean
  (cond
    [(null? lst) #t] 
    [(member (car lst) (cdr lst)) #f] 
    [else (check-duplicates (cdr lst))]))


;; Takes a list of bindings as an Sexp and turns it into a list of symbol
(define (parse-binding-syms [bindings : (Listof Sexp)]) : (Listof Symbol)
  (begin
    (for/list ([binding (in-list bindings)])
      (match binding
        [(list sym '<- _) (if (valid-id (cast sym Symbol)) (cast sym Symbol)
                              (error 'parse-binding-sym "OAZO: Invalid Binding"))]
        [else (error 'parse-binding-syms "OAZO: Invalid binding: ~a" binding)])))) 


;; Takes a list of bindings as an Sexp and turns it into a list of symbol
(define (parse-binding-args [bindings : (Listof Sexp)]) : (Listof ExprC)
  (begin
    (for/list ([binding (in-list bindings)])
      (match binding
        [(list _ '<- val) (parse val)]
        [else (error 'parse-binding-args "OAZO: Invalid binding: ~a" binding)]))))


;; Returns an environment given two environments
(define (extend-env [env1 : (Listof env-binding)] [env2 : (Listof env-binding)]) : Env
  (append env1 env2)) 


;; Returns a list of bindings given a list of Symbols and list of values
(define (bind [sym : (Listof Symbol)] [val : (Listof Location)]) : (Listof env-binding)
  (match sym
    ['() '()]
    [(cons s rest-s)
     (match val
       ['() (error 'bind "OAZO Error: Mismatched number of arguments and symbols")]
       [(cons v rest-v) (cons (env-binding s v) (bind rest-s rest-v))])]))


;; Checks the body of the lamC and ensures that it is either a single argument
;; or that there are proper {} around them
(define (check-body [body : Sexp]) : Boolean
  (match body
    [(list _ ...) #t]  
    [_ #t]))
 

;; Checks if an item is any of the ExprC types
(define (check-ExprC? [expr : Any]) : Boolean
  (match expr
    [(numC _) #t]
    [(idC _) #t]
    [(appC _ _) #t]
    [(ifC _ _ _) #t]
    [(strC _) #t]
    [else #f]))


;; Evaluate a sequence of args and return the result of the last
(define (seq [a : Value] [b : (Listof Value)] [env : Env]) : Value
   (if (empty? b) a
      (seq (first b) (rest b) env)))


;; OAZO7 TEST CASES
;;-----------------------------------------------------------------------------------

(check-equal? (top-interp '{+ 1 2}) "3")





;; TEST CASES
;;-----------------------------------------------------------------------------------
#|

;; test cases from backtesting OAZO5
(check-exn #rx"OAZO" (lambda () (parse '{let {: <- ""} "World"})))
(check-exn #rx"OAZO" (lambda () (parse '{anon {i} : "hello" 31/7 +})))

;; apply-primop tests
(check-equal? (apply-primop (primopV 'num-eq?) (list (numC 5) (numC 5)) top-env) (boolV #t))
(check-equal? (apply-primop (primopV 'str-eq?) (list (strC "hello") (strC "hello")) top-env) (boolV #t))
(check-exn #rx"OAZO" (lambda () (apply-primop (primopV 'num-eq?) (list (numC 5) (strC "5")) top-env)))
(check-exn #rx"OAZO" (lambda () (apply-primop (primopV 'str-eq?) (list (numC 5) (strC "5")) top-env)))


;; Top-Interp Tests
(check-equal? (top-interp '{if {<= 4 3} then 29387 else true})"true")
(check-equal? (top-interp '{if {<= 2 3} then 29387 else true})"29387")
(check-equal? (top-interp '{if {<= 2 3} then false else true})"false")


#;(check-exn #rx"OAZO"(lambda ()(top-interp '(+ 4 (error "1234")))))
(check-exn #rx"OAZO"(lambda ()(top-interp '(+ 4 #t))))
(check-exn #rx"OAZO"(lambda ()(top-interp '(- 4 "s"))))
(check-exn #rx"OAZO"(lambda ()(top-interp '(* 4 "s")))) 
(check-exn #rx"OAZO"(lambda ()(top-interp '(/ 4 "f"))))
#;(check-exn #rx"OAZO"(lambda ()(top-interp '(<= 4))))
(check-exn #rx"OAZO"(lambda ()(top-interp '(<= 4 "f"))))
(check-exn #rx"OAZO"(lambda ()(top-interp '(/ + + )))) 
(check-exn #rx"OAZO"(lambda ()(top-interp '(+ 4 (error)))))
#;(check-exn #rx"OAZO" (lambda ()(top-interp '((anon (e) : (e e)) error))))
(check-exn #rx"OAZO"(lambda ()(top-interp '(+ ))))
(check-exn #rx"OAZO"(lambda ()(top-interp '(+ else))))  
(check-exn #rx"OAZO" (lambda() (top-interp '(/ 1 (- 3 3)))))
(check-exn #rx"OAZO" (lambda() (top-interp '(3 4 5)))) 

 
(check-equal? (top-interp '{{anon {seven} : {seven}}
               {{anon {minus} :
                    {anon {} : {minus {+ 3 10} {* 2 3} }}}
               {anon {x y} : {+ x {* -1 y}}}}}) "7")
(check-equal? (top-interp '{let {x <- 5}
                                {y <- 7}
                                {+ x y}}) "12")
(check-equal? (top-interp '{let {z <- {+ 7 8}}
                                {y <- 5}
                                {+ z y}}) "20")
(check-equal? (top-interp '{{anon {x y} : {+ x y}} 5 7}) "12")
(check-equal? (top-interp '{{anon {x y z} :
                                 {+ x {+ y z}}} 1 2 3}) "6")
(check-equal? (top-interp '{let {f <- {anon {a} : {+ a 4}}}
                                {f 1}}) "5")
(check-exn #rx"OAZO" (lambda() (top-interp
                                  '{{func {ignoreit x}: {+ 3 4}}
                                    {func {main} : {ignoreit {/ 1 {+ 0 0}}}}})))
(check-exn #rx"OAZO" (lambda() (top-interp '{{anon {x x} : 3} 1 1})))


;; Recurisve Test
(check-equal? (top-interp '{let {f <- {anon {func x} : {if {<= x 10} then {func func {+ x 1}} else {-1}}}}
                                {f f 1}}) "-1")
(check-exn #rx"OAZO" (lambda () (top-interp
                                 '{let {f <- {anon {x} : {+ x 1}}}
                                       {y <- {anon {z} : {f 4}}}
                                       {y 3}})))
(check-exn #rx"OAZO" (lambda () (top-interp
                                 '{{anon {} : 12} 1})))

;; Interp tests
(check-equal? (interp (appC (idC '+) (list (numC 1) (numC 1))) top-env) (numV 2)) 
(check-equal? (interp (appC (idC '-) (list (numC 3) (numC 1))) top-env) (numV 2))
(check-equal? (interp (appC (idC '*) (list (numC 12)(numC 2))) top-env) (numV 24))  
(check-equal? (interp (appC (idC '/) (list (numC 6) (numC 2))) top-env) (numV 3))
(check-equal? (interp (appC (idC '<=) (list(numC 0) (numC 2))) top-env) (boolV true))
(check-equal? (interp (appC (lamC (list 'x)
                                  (appC (idC '+)
                                     (list (idC 'x) (numC 1))))
                            (list (numC 5))) top-env) (numV 6))
(check-equal? (interp (ifC (idC 'true) (numC 1) (numC 2)) top-env) (numV 1))

;; Parse Tests
(check-equal? (parse '{12}) (numC 12))
(check-equal? (parse 'x) (idC 'x))
(check-equal? (parse "string") (strC "string"))
(check-equal? (parse '{+ 1 2}) (appC (idC '+) (list (numC 1) (numC 2))))
(check-equal? (parse '{anon {x y} : {+ x y}})         
              (lamC (list 'x 'y)
                    (appC (idC '+)
                          (list (idC 'x) (idC 'y)))))
(check-equal? (parse '{let {x <- 5}
                           {y <- 7}
                        {+ x y}})
              
              (appC (lamC (list 'x 'y)
                          (appC (idC '+)
                                (list (idC 'x) (idC 'y))))
              (list (numC 5)
                    (numC 7))))
(check-equal? (parse '{if {<= x 1} then 1 else -1})
              (ifC (appC (idC '<=) (list (idC 'x) (numC 1))) (numC 1) (numC -1)))
(check-exn #rx"OAZO" (lambda () (parse '(let (z <- (anon () : 3)) (z <- 9) (z))))) 
(check-equal? (parse '{{anon {x y} : {+ x y}} 5 7})
              
              (appC (lamC (list 'x 'y)
                          (appC (idC '+)
                                (list (idC 'x) (idC 'y))))
              (list (numC 5)
                    (numC 7))))
(check-equal? (parse '{f 4}) (appC (idC 'f) (list(numC 4))))
(check-exn #rx"OAZO" (lambda() (parse '{{anon {2} : {1}} 1})))
(check-exn #rx"OAZO" (lambda() (parse '{let {c <- 5}})))
(check-exn #rx"OAZO" (lambda () (parse '(+ then 4))))



;; Parse-Binding-Args Tests
(define bds3 '{{x <- 5} {y <- 7}})
(define bds4 '{x <- q})
(define bds5 '{{z <- {+ 7 8}}
               {y <- 5}
               {+ z y}})

(check-equal? (parse-binding-args bds3)
              (list (numC 5) (numC 7)))


(check-exn #rx"OAZO" (lambda()
                       (parse-binding-syms bds4)))

;; Parse-Binding-Syms Tests
(define bds1 '{{x <- 5} {y <- 7}})
(define bds2 '{1 <- 5})
(define bds6 '{{meow} -> meow})
(define bds7 '{{{{not a symbol}}}  <- 1})
(check-equal? (parse-binding-syms bds1)
              (list 'x 'y))
(check-exn #rx"OAZO" (lambda()
                       (parse-binding-syms bds2)))
(check-exn #rx"OAZO" (lambda()
                       (parse-binding-args bds6)))

(check-exn #rx"OAZO" (lambda()
                       (parse-binding-syms bds7)))



;; Lookup Tests
(check-equal? (lookup 'true top-env) (boolV #t))
(check-exn #rx"OAZO" (lambda ()(lookup 'not-here top-env)))


;; Extend-env Tests
(check-equal? (extend-env (list (binding 'x (numV 1)) (binding 'y (numV 1))
                                (binding 'z (numV 1))) (list (binding 't (boolV #f))
                                                             (binding 'b (numV 2)) (binding 'dd (primopV '+))))
              (list (binding 'x (numV 1)) (binding 'y (numV 1)) (binding 'z (numV 1))
                    (binding 't (boolV #f)) (binding 'b (numV 2)) (binding 'dd (primopV '+))))

;; Error coverage


(check-exn #rx"OAZO" (lambda()(interp (ifC (numC 5) (numC 1) (numC 2)) top-env)))
(check-exn #rx"OAZO" (lambda()(interp (appC (idC '+) (list (strC "oops") (numC 1))) top-env)))


;;Serialize
(check-equal? (serialize (numV 1)) "1")
(check-equal? (serialize 1) "1")
(check-equal? (serialize #t) "true")
(check-equal? (serialize #f) "false")
(check-equal? (serialize (strV "Hello")) "\"Hello\"")
(check-equal? (serialize (primopV '+)) "#<primop>")  
(check-equal? (serialize (closeV (list 'x 'y) (appC (idC '+) (list (numC 1)
                  (numC 1))) (list (binding 'x (numV 4)) (binding 'y (numV 2))))) "#<procedure>")
(check-exn #rx"OAZO" (lambda()(serialize "string")))

;;helper
(check-equal? (bind (list 'x 'y 'z) (list (numV 1) (numV 2) (numV 3)))
              (list (binding 'x (numV 1)) (binding 'y (numV 2)) (binding 'z (numV 3))))
(check-equal? (bind (list 't 'b 'dd) (list (boolV #f) (numV 2) (primopV '+)))
              (list (binding 't (boolV #f)) (binding 'b (numV 2)) (binding 'dd (primopV '+))))
(check-equal? (bind (list 'a) (list (closeV (list 'v 'c 'd) (numC 2)
                                            (list (binding 'x (numV 1)) (binding 'y (numV 1)) (binding 'z (numV 1))))))
              (list (binding 'a (closeV (list 'v 'c 'd) (numC 2)
                                        (list (binding 'x (numV 1)) (binding 'y (numV 1)) (binding 'z (numV 1)))))))
(check-exn #rx"OAZO" (lambda()(bind '(a) '()))) 
(check-equal? (valid-id 'else:) #f) 


;; Check-duplicates tests
(define symbols1 '(a b c d))
(define symbols2 '(x y z y))

(check-equal? (check-duplicates symbols1) #t) ; Output: #f 
(check-equal? (check-duplicates symbols2) #f) ; Output: #t


;; Check-args test
(check-equal? (check-args (list 'x) (list (numC 1))) #t)
(check-exn #rx"OAZO" (lambda() (check-args (list 'x) (list (numC 1) (numC 2)))))
|#
