#lang typed/racket
(require typed/rackunit)

;; Assignment 5
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
(define-type ExprC (U numC idC appC ifC strC lamC))

;; Bindings
(struct binding ([name : Symbol] [val : Value])                #:transparent)
(define-type Env (Listof binding))
(define mt-env  '())

;; Values
(struct numV    ([n : Real])                                   #:transparent)
(struct boolV   ([b : Boolean])                                #:transparent)
(struct strV    ([str : String])                               #:transparent)
(struct closeV  ([arg : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct primopV ([sym : Symbol])                               #:transparent)
(define-type Value (U numV closeV boolV primopV strV))

;; Top Level Environment
(define top-env
  (list (binding 'true (boolV #t))
        (binding 'false (boolV #f))
        (binding '+ (primopV '+))
        (binding '- (primopV '-))
        (binding '* (primopV '*))
        (binding '/ (primopV '/))
        (binding '<= (primopV '<=))
        (binding 'equal? (primopV 'equal?))
        (binding 'println (primopV 'println))
        (binding 'read-num (primopV 'read-num))
        (binding '++ (primopV '++))
        (binding 'seq (primopV 'seq))
        (binding 'error (primopV 'error)))) 


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
    [(numC n) (numV n)]          ;; numC 
    [(idC s) (lookup s env)]     ;; idC
    [(strC str) (strV str)]      ;; strC
    [(ifC test then else)        ;; ifC
     (define test-result (interp test env)) 
     (cond [(boolV? test-result)
            (cond [(boolV-b test-result) (interp then env)]
                  [else (interp else env)])]
           [else (error 'interp "OAZO: Test was not a boolean expression: ~e" e)])] 
    [(appC f args) (define f-value : Value (interp f env)) ;;Current env
                   (match f-value
                     [(? closeV?) (check-args (closeV-arg f-value) args)
                                   (interp (closeV-body f-value)               ;;Current env
                                          (extend-env (bind (closeV-arg f-value)
                                                            (map(lambda ([a : ExprC]) (interp a env)) args))
                                                      (closeV-env f-value)))]
                     [(? primopV?) (apply-primop f-value args env)] 
                     [else (error 'interp "OAZO Unsupported value for interp: ~v" f-value)])] 
     
    [(lamC a body) (closeV a body env)]))

(define (interp-primop [args : (Listof ExprC)] [env : Env]) : (Listof Value)
 (let ([arg-values (map (λ ([arg : ExprC])
                              (interp arg env)) args)]) arg-values))


;; Takes a primop an list of args and the environment and ouputs the value 
(define (apply-primop [primop : primopV] [args : (Listof ExprC)] [env : Env]) : Value
  (cond
    [(equal? primop (primopV 'read-num)) (read-num)]
    #;[(> (length args) 2) (error 'apply "OAZO too many values for primitave operation ~v" args)]
    [(equal? args '()) (error 'apply "OAZO no args given ~v" args)]
    [else
     (define a-v : (Listof Value) (interp-primop args env))
     (match a-v
       [(list str)
        (match primop 
          [(primopV 'println) (displayln (serialize (first a-v))) (boolV #t)]
          [(primopV 'error) (error 'apply-primop "OAZO ERROR: user-error")]
          [else (error 'apply-primop "OAZO ERROR: Not enough args for primops")])]
      
       [else
        (define f : Value (first a-v))
        (define second : Value (first (rest a-v)))
       
        (match primop 
          [(primopV '+)
           (if (and (numV? f) (numV? second)) (numV (+ (numV-n f) (numV-n second)))
               (error 'apply-primop "OAZO ERROR: Non-numeric argument for add"))]
          [(primopV '-)
           (if (and (numV? f) (numV? second)) (numV (- (numV-n f) (numV-n second)))
               (error 'apply-primop "OAZO ERROR: Non-numeric argument for sub"))]
          [(primopV '*)
           (if (and (numV? f) (numV? second)) (numV (* (numV-n f) (numV-n second)))
               (error 'apply-primop "OAZO ERROR: Non-numeric argument for mult"))]
          [(primopV '/) 
           (cond
             [(equal? (numV 0) second) (error 'apply-primop "OAZO ERROR: Divide by zero!")]
             [else (if (and (numV? f) (numV? second)) (numV (/ (numV-n f) (numV-n second)))
                       (error 'apply-primop "OAZO ERROR: Non-numeric argument for div"))])]
          [(primopV '<=)
           (if (and (numV? f) (numV? second)) (boolV (<= (numV-n f) (numV-n second)))
               (error 'apply-primop "OAZO ERROR: Non-numeric argument for <="))] 
          [(primopV 'equal?) 
           (let ([operand1 f]
                 [operand2 second])   
             (cond   
               [(and(not(or(closeV? operand1)(closeV? operand2)))(not(or(primopV? operand1)(primopV? operand2))))
                (boolV (equal? operand1 operand2))]
               [else (boolV #f)]))]    
            #;[(primopV 'read-num) (read-num)] 
            [(primopV '++) (strV (++ (map serialize (map (lambda ([x : ExprC]) (interp x env)) args))))] 
            [(primopV 'seq) (seq (first a-v) (rest a-v) env)])])])) 

 
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
    [(? strV? str) (format "~a" (strV-str str))]
    [(boolV #t) "true"]
    [#t "true"]
    [(boolV #f) "false"]
    [#f "false"]
    [(? primopV? p) "#<primop>"]
    [else (error 'serialize "OAZO Unsupported value: ~v" val)]))



;; HELPER FUNCTIONS
;;-----------------------------------------------------------------------------------

;; Helper to check the number of param vs given arguments
(define (check-args [param : (Listof Symbol)] [args : (Listof ExprC)]) : Boolean
  (if (>= (length param) (length args)) #t
      (error 'check-args "OAZO mismatch number of arguments")))


;; Helper that looks up a value in an environment
(define (lookup [for : Symbol] [env : Env]) : Value
    (match env
      ['() (error 'lookup "OAZO ERROR: name not found: ~e" for)]
      [(cons (binding name val) r) (cond
                                     [(symbol=? for name) val]
                                     [else (lookup for r)])]))


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
(define (extend-env [env1 : (Listof binding)] [env2 : (Listof binding)]) : Env
  (append env1 env2)) 


;; Returns a list of bindings given a list of Symbols and list of values
(define (bind [sym : (Listof Symbol)] [val : (Listof Value)]) : (Listof binding)
  (match sym
    ['() '()]
    [(cons s rest-s)
     (match val
       ['() (error 'bind "OAZO Error: Mismatched number of arguments and symbols")]
      ;; [(list (? closeV? c)) (bind sym (closeV-body c))]
       [(cons v rest-v) (cons (binding s v) (bind rest-s rest-v))])]))


;; Checks the body of the lamC and ensures that it is either a single argument
;; or that there are proper {} around them
(define (check-body [body : Sexp]) : Boolean
  (match body
    [(list _ ...) #t]  
    [_ #t]
    #;[other #f]))
 

;; Prompts the user to give a number and errors if it is not a valid Real
;; and returns a numV if its valid
(define (read-num) : Value
  (display "> ")
  (flush-output)
  (define input (read-line))
  (cond
    [(eof-object? input) (error 'read-num "OAZO: Unexpected end of input")]
    [(string? input)
     (define num (string->number input))
     (if (real? num)
         (numV num)
         (error 'read-num "OAZO: Input is not a real number"))]
    [else (error 'read-num "OAZO: Invalid input format")]))


;; takes a string a and a list of strings b and concatenates them in order
(define (++ [a : (Listof String)]) : String
  (match a
    ['() ""] 
    [(cons f r) (string-append f (++ r))])) 
       
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


#;(top-interp '{seq
              {println "line1"}
              {println "line2"}
              {println "line3"}})


#;(top-interp '{seq
              {+ 1 2}
              {+ 2 3}
              {* 5 10}})

#;(cond
  [(empty? b) ((if (check-ExprC? a)
                   (interp (cast a ExprC) env)
                   (error 'seq "OAZO: Invalid input: ~a" a)))]
  [else ((if (check-ExprC? b)
                   (interp (cast b ExprC) env)
                   (error 'seq "OAZO: Invalid input: ~a" b)) (seq (first b) (rest b)))])

;; TEST CASES
;;-----------------------------------------------------------------------------------

;; seq tests
#;(check-equal? (top-interp '{seq
                             {+ 1 2}
                             {+ 2 3}}) "5")

#;(top-interp '{println{++ "pie" " " "hi"}})



(top-interp '{seq
              {println "What is your favorite integer between 6 and 7?"}
              {let {your-number <- {read-num}}
              {println {++ "Interesting. You picked " your-number ". good choice!"}}}})







;; a test to use once seq is working
#;{seq
  '{println "What is your favorite integer between 6 and 7?"}
  '{println "Interesting. You picked "}} 

                     
;; ++ tests
(check-equal? (++ {list "Hello, " "world" "!"}) "Hello, world!")
(check-equal? (++ {list "abc" "def" "ghi" "jkl"}) "abcdefghijkl")
(check-equal? (++ {list "" "one" "two" "three"}) "onetwothree") 


;; test cases from backtesting OAZO5
(check-exn #rx"OAZO" (lambda () (parse '{let {: <- ""} "World"})))
(check-exn #rx"OAZO" (lambda () (parse '{anon {i} : "hello" 31/7 +})))

;;println test
#;(check-equal? (apply-primop (primopV 'println) (list (strC "teehee")) top-env) (boolV #t))

;; test cases from backtesting OAZO5
(check-exn #rx"OAZO" (lambda () (parse '{let {: <- ""} "World"})))

(check-exn #rx"OAZO" (lambda () (parse '{anon {i} : "hello" 31/7 +})))



(check-equal? (apply-primop (primopV 'equal?) (list (numC 5) (numC 5)) top-env) (boolV #t))
(check-equal? (apply-primop (primopV 'equal?) (list (strC "hello") (strC "hello")) top-env) (boolV #t))
(check-equal? (apply-primop (primopV 'equal?) (list (numC 5) (strC "5")) top-env) (boolV #f)) 
(check-equal? (apply-primop (primopV 'equal?) (list (idC 'true) (idC 'true)) top-env) (boolV #t))
#;(check-equal? (apply-primop (primopV '+) (list (closeV 1 2 top-env)) top-env ()))
(check-equal?  (apply-primop (primopV 'equal?) (list (lamC '(x) (numC 3)) (numC 3)) top-env) (boolV #f))

(check-exn #rx"OAZO" (lambda() (parse '{let {c <- 5}})))

;; Top-Interp Tests
(check-equal? (top-interp '{if {<= 4 3} then 29387 else true})"true")
(check-equal? (top-interp '{if {<= 2 3} then 29387 else true})"29387")
(check-equal? (top-interp '{if {<= 2 3} then false else true})"false")



#;(check-equal? (top-interp '{{anon {} : {equal? + +}}}) "true")

#;(check-equal? (top-interp '{{anon {x} : {equal? x {anon {} : {1}}} 5}}) "false")

;;(check-equal? (serialize (strV "Hello")) "\"Hello\"")

(check-exn #rx"OAZO"(lambda ()(top-interp '(+ 4 (error "1234")))))
(check-exn #rx"OAZO"(lambda ()(top-interp '(+ 4 #t))))
(check-exn #rx"OAZO"(lambda ()(top-interp '(- 4 "s"))))
(check-exn #rx"OAZO"(lambda ()(top-interp '(* 4 "s")))) 
(check-exn #rx"OAZO"(lambda ()(top-interp '(/ 4 "f"))))
(check-exn #rx"OAZO"(lambda ()(top-interp '(<= 4))))
(check-exn #rx"OAZO"(lambda ()(top-interp '(<= 4 "f"))))
(check-exn #rx"OAZO"(lambda ()(top-interp '(/ + + )))) 
(check-equal?(top-interp '(equal? true true))"true")
(check-exn #rx"OAZO"(lambda ()(top-interp '(+ 4 (error)))))
(check-exn #rx"OAZO"(lambda ()(top-interp '(equal? 4 (-)))))
(check-exn #rx"OAZO" (lambda ()(top-interp '((anon (e) : (e e)) error))))
(check-exn #rx"OAZO"(lambda ()(top-interp '(+ ))))
;;(top-interp '(/ + + )) 
(check-exn #rx"OAZO"(lambda ()(top-interp '(+ else))))  
;;(interp(parse '(+ 4 (error "1234"))) top-env)

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



(check-exn #rx"OAZO" (lambda() (top-interp '{{anon {x x} : 3} 1 1})))


;; Recurisve Test
#;(check-equal? (top-interp '{let {f <- {anon {func x} : {if {<= x 10} then {func func {+ x 1}} else {-1}}}}
                                {f f 1}}) "-1")


#;(check-exn #rx"OAZO" (lambda () (top-interp '{let {f <- {anon {a} : {g 1}}}
                                {g <- {anon {b} : {+ a b}}}
                                {g 5}}) "6"))


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
(check-equal? (interp (appC (idC 'equal?) (list (idC '+) (numC 2))) top-env) (boolV #f))

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
#;(check-exn #rx"OAZO" (lambda() (interp (appC (lamC (list 'x 'y 'z)
                                  (appC (idC '+)
                                     (list (idC 'x) (idC 'y) (idC 'z))))
                            (list (numC 5) (numC 6) (numC 1))) top-env)))

(check-exn #rx"OAZO" (lambda()(interp (ifC (numC 5) (numC 1) (numC 2)) top-env)))

(check-exn #rx"OAZO" (lambda()(interp (appC (idC '+) (list (strC "oops") (numC 1))) top-env)))


;;Serialize
(check-equal? (serialize (numV 1)) "1")
(check-equal? (serialize 1) "1")
(check-equal? (serialize #t) "true")
(check-equal? (serialize #f) "false")

;;(check-equal? (serialize (interp (numC 1) top-env)) "#<procedure>")
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


#;(check-exn #rx"OAZO" (lambda() (top-interp
                                  '{{func {ignoreit x}: {+ 3 4}}
                                    {func {main} : {ignoreit {/ 1 {+ 0 0}}}}})))


;; Check-args test
(check-equal? (check-args (list 'x) (list (numC 1))) #t)
(check-exn #rx"OAZO" (lambda() (check-args (list 'x) (list (numC 1) (numC 2)))))