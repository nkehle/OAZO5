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
(struct setC    ([sym : Symbol]  [val : ExprC])                #:transparent)
(define-type ExprC (U numC idC appC ifC strC lamC arrC setarrC setC))

;; Values
(struct numV    ([n : Real])                                   #:transparent)
(struct boolV   ([b : Boolean])                                #:transparent)
(struct strV    ([str : String])                               #:transparent)
(struct arrV    ([loc : Location] [len : Real])                 #:transparent)
(struct closeV  ([args : (Listof Symbol)] [body : ExprC] [env : Env]) #:transparent)
(struct primopV ([sym : Symbol])                               #:transparent)
(struct nullV   ()                                             #:transparent)
(define-type Value (U numV closeV boolV primopV strV arrV nullV))

;; Bindings
(struct env-binding   ([name : Symbol]  [val : Location])       #:transparent)
(struct store-binding ([loc : Location] [val : Value])          #:transparent)
(define-type Env (Listof env-binding))
(define mt-env  '())

;; Store
(define-type Location Real)
(struct Store ([bindings : (Listof store-binding)] [next : Real])       #:transparent)
(struct v*s   ([val : Value] [sto : Store])                             #:transparent)
(struct lv*s  ([lst : (Listof Value)] [sto : Store])                    #:transparent)
(struct e*s   ([env : Env] [sto : Store])                               #:transparent)
(struct b*s   ([base : Location] [sto : Store])                         #:transparent)
(define add-store cons)

;; Top Level Environment
(define top-env
  (list (env-binding 'substring 17)
        (env-binding 'seq 16)
        (env-binding 'alen 15)
        (env-binding 'aset! 14)
        (env-binding 'aref 13)
        (env-binding 'arr 12)
        (env-binding 'error 11)
        (env-binding 'arr-eq? 10)
        (env-binding 'str-eq? 9)
        (env-binding 'num-eq? 8)
        (env-binding 'equal? 7)
        (env-binding '<= 6)
        (env-binding '/ 5)
        (env-binding '* 4)
        (env-binding '- 3)
        (env-binding '+ 2)
        (env-binding 'true 1)
        (env-binding 'false 0)))

;; Top Level Store
(define top-sto
  (Store
   (list (store-binding 17 (primopV 'substring))
         (store-binding 16 (primopV 'seq))
         (store-binding 15 (primopV 'alen))
         (store-binding 14 (primopV 'aset!))
         (store-binding 13 (primopV 'aref))
         (store-binding 12 (primopV 'arr))
         (store-binding 11 (primopV 'error))
         (store-binding 10 (primopV 'arr-eq?))
         (store-binding 9 (primopV 'str-eq?))
         (store-binding 8 (primopV 'num-eq?))
         (store-binding 7 (primopV 'equal?))
         (store-binding 6 (primopV '<=))
         (store-binding 5 (primopV '/))
         (store-binding 4 (primopV '*))
         (store-binding 3 (primopV '-))
         (store-binding 2 (primopV '+))
         (store-binding 1 (boolV #t))
         (store-binding 0 (boolV #f))) 18))


;; TOP-INTERP
;;-----------------------------------------------------------------------------------
;; Interprets the entirely parsed program
#;(define (top-interp [s : Sexp]) 
   (print-store (v*s-sto (interp (parse s) top-env top-sto))))

(define (top-interp [s : Sexp]) : String
   (serialize (v*s-val (interp (parse s) top-env top-sto))))

;; INTERP
;;-----------------------------------------------------------------------------------
;; Inteprets the given expression using list of funs to resolve appC's
(define (interp [e : ExprC] [env : Env] [sto : Store]) : v*s
  (match e
    [(numC n)       (v*s (numV n) sto)]
    [(strC str)     (v*s (strV str) sto)]
    [(idC s)        (v*s (fetch (lookup s env) (Store-bindings sto)) sto)]
    [(setC sym val) (define new-state (interp val env sto))
                    (v*s (nullV) (mutate-store sym (v*s-val new-state) env (v*s-sto new-state)))]
    [(appC f a) 
     (define func    (interp f env sto))
     (define args    (interp-args a env (v*s-sto func)))
     (define new-sto (lv*s-sto args))
     (match (v*s-val func)
       [(? primopV?) (apply-primop (v*s-val func) (lv*s-lst args) env new-sto)]
       
       [(? closeV? clos)  (check-args (closeV-args clos) (lv*s-lst args))
                                           (define new-es (extend-both
                                                           (closeV-env clos) (closeV-args clos)
                                                           (lv*s-lst args) new-sto))
                                           (interp (closeV-body clos) (e*s-env new-es) (e*s-sto new-es))]
       
       [else (error 'interp "OAZO: Error in appC ~v" func)])]
    [(ifC test then else)        ;; ifC
     (define test-result (interp test env sto))
     (cond [(boolV? (v*s-val test-result))
            (cond [(boolV-b (v*s-val test-result)) (interp then env (v*s-sto test-result))]
                  [else (interp else env (v*s-sto test-result))])]
           [else (error 'interp "OAZO: Test was not a boolean expression: ~e" e)])]
    
    [(lamC a body) (v*s (closeV a body env) sto)]
    [other (error 'unimplemented "~e" other)]))

#;(check-equal? (top-interp '{let {x <- 5}
                                {seq {x := 10} x}}) "10")

;; Helper that extends a current environemt/store and returns the updated e*s
(define (extend-both [env : Env] [params : (Listof Symbol)] [args : (Listof Value)] [sto : Store]) : e*s
  (cond
    [(empty? params) (e*s env sto)]
    [else (define cell (lookup (first params) env))
          (if (> cell -1) 
              (extend-both env (rest params) (rest args) (mutate-store (first params) (first args) env sto))
                           #;(Store (cons (store-binding cell (first args))
                                                                      (Store-bindings sto))
                                                                (+ 1 (Store-next sto)))

              (extend-both (cons (env-binding (first params)  (Store-next sto)) env)
                           (rest params) (rest args) (Store (cons (store-binding
                                                                   (Store-next sto) (first args)) (Store-bindings sto))
                                                            (+ 1 (Store-next sto)))))]))

;; updates store with duplicates
#;(define (env-extend [env : Env] [params : (Listof Symbol)] [args : (Listof Value)] [sto : Store]) : State
  (cond
    [(empty? params) (e*s env sto)]
    [else (define loc (lookup (first params) env))
          (if (> loc -1)
              (env-extend env (rest params) (rest args) (hash-set sto loc (first args)))
              
              (env-extend (cons (Binding (first params) (hash-count sto)) env)
                          (rest params) (rest args) (hash-set sto (hash-count sto) (first args))))]))



;; Helper to check the number of param vs given arguments
(define (check-args [param : (Listof Symbol)] [args : (Listof Value)]) : Boolean
  (if (>= (length param) (length args)) #t
      (error 'check-args "OAZO mismatch number of arguments")))


;; Helper to interpret the args and thread the store through 
(define (interp-args [args : (Listof ExprC)] [env : Env] [sto : Store]) : lv*s
 (cond
   [(empty? args) (lv*s '() sto)]
   [else (define res (interp (first args) env sto))
         (define tail (interp-args (rest args) env (v*s-sto res)))
    (lv*s (cons (v*s-val res) (lv*s-lst tail)) (lv*s-sto tail))]))


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
       [(primopV 'arr-eq?)
        (if (and (arrV? f) (arrV? second)) (v*s (boolV (equal? (arrV-loc f) (arrV-loc second))) sto)
            (error 'apply-primop "OAZO ERROR: Non-numeric argument for arr-eq?"))]
       [(primopV 'arr)
        (if (and (numV? f) (numV? second)) (v*s (arr (numV-n f) (Store-next sto)) (allocate (numV-n f) second sto))
            (error 'apply-primop "OAZO ERROR: Non-numeric argument for arr"))]
       [(primopV 'aref)
        (if (and (arrV? f) (numV? second)) (v*s (aref f (numV-n second) sto) sto)
            (error 'apply-primop "OAZO ERROR: Non-numeric argument for arr"))]
       #;[(primopV 'aset)
        (if (and (arrV? f) (numV? second)) (v*s (aref f (numV-n second) sto) sto)
            (error 'apply-primop "OAZO ERROR: Non-numeric argument for arr"))]
       #;[(primopV 'alen)
        (if (and (arrV? f) (numV? second)) (v*s (aref f (numV-n second) sto) sto)
            (error 'apply-primop "OAZO ERROR: Non-numeric argument for arr"))]
       [(primopV 'seq) (v*s (seq (first args) (rest args) env) sto)])]))


;; Creates a new array of given size and fills with a value
(define (arr [size : Real] [loc : Location]) : arrV
  (cond
    [(zero? size) (error 'arr "OAZO: arr must be of length 1 or more")]
    [else (arrV loc size)]))


;; Takes a store, size, value and the extended store with the added array
(define (allocate [size : Real] [val : Value] [sto : Store]) : Store
  (cond
    [(zero? size) sto]
    [else (allocate (- size 1) val (Store (cons (store-binding (Store-next sto) val)
                                                (Store-bindings sto)) (+ (Store-next sto) 1)))]))


;; Returns the element of the numarray at a given index
(define (aref [arr : arrV] [idx : Real] [sto : Store]) : Value
  (cond
    [(< idx 0) (error 'aref "OAZO: Index out of bounds: ~a" idx)]
    [(>= idx (arrV-len arr)) (error 'aref "OAZO: Index out of bounds: ~a" idx)]
    [else (fetch (+ (arrV-loc arr) idx) (Store-bindings sto))])) 

;; Given an index and an array and a value mutate the array to be the new val
(define (aset [arr : arrV] [idx : Real] [val : Value] [env : Env] [sto : Store])
  (cond
    [(or (< idx 0) (>= idx (arrV-len arr))) (error 'aset "OAZO: Index out of bounds")]
    [else (mutate-store (+ (arrV-loc arr) idx) val env sto)]))

;; Mutates the store and returns the new store
(define (mutate-store [location : Location] [value : Value] [env : Env] [store : Store]) : Store
  (define (update-store [lst : (Listof store-binding)] [index : Real] [cnt : Real] [val : Value]) : (Listof store-binding)
    (if (= location -1) (error 'mutate "OAZO: binding does not already exist")
        (cond
          [(empty? lst) lst]  
          [(= cnt 0)        
           (cons (store-binding index val) (rest lst))]
          [else             
           (cons (first lst) (update-store (rest lst) index (- cnt 1) val))])))
  (let ([updated-bindings (update-store (Store-bindings store) location
                                        (- (- (Store-next store) 1) location) value)])
    (Store updated-bindings (Store-next store))))

#;(define (mutate-store [symbol : Symbol] [value : Value] [env : Env] [store : Store]) : Store
    (let ([location (lookup symbol env)])
      (define (update-store [lst : (Listof store-binding)] [index : Real] [cnt : Real] [val : Value]) : (Listof store-binding)
        (if (= location -1) (error 'mutate "OAZO: binding does not already exist")
          (cond
            [(empty? lst) lst]  
            [(= cnt 0)        
             (cons (store-binding index val) (rest lst))]
            [else             
             (cons (first lst) (update-store (rest lst) index (- cnt 1) val))])))
    (let ([updated-bindings (update-store (Store-bindings store) location
                                          (- (- (Store-next store) 1) location) value)])
      (Store updated-bindings (Store-next store)))))


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
    [(list (? symbol? s) ':= val) (setC s (parse val))]    ;; setC
    [(list _ '<- _) (error 'parse "OAZO")]                 ;; weird case of bindingds and body being switched
    [(list 'let bindings ... body)                         ;; letC
     (if (check-duplicates (parse-binding-syms (cast bindings (Listof Sexp)))) 
     (appC (lamC (parse-binding-syms (cast bindings (Listof Sexp))) 
                 (parse body))
           (parse-binding-args (cast bindings (Listof Sexp))))
     (error 'parse "OAZO Error: Expected a list of non-duplicate symbols for parameters"))]
    

    [(list 'anon syms ': body)                             ;; lamC
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
    [(? nullV?) "null"]
    [(? arrV? arr) (string-append (number->string (arrV-loc arr)) "-" (number->string (arrV-len arr)))]
    [else (error 'serialize "OAZO Unsupported value: ~v" val)]))



;; HELPER FUNCTIONS
;;-----------------------------------------------------------------------------------

;; Helper that looks up a value in an environment
(define (lookup [for : Symbol] [env : Env]) : Location
    (match env
      ['() -1 #;(error 'lookup "OAZO ERROR: name not found: ~e" for)]
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
    [(or 'let ':= 'if 'then 'else ': '<- ) #f]
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
    [(numC _) #t] [(idC _) #t] [(appC _ _) #t] [(ifC _ _ _) #t] [(strC _) #t]
    [else #f]))


;; Evaluate a sequence of args and return the result of the last
(define (seq [a : Value] [b : (Listof Value)] [env : Env]) : Value
   (if (empty? b) a
      (seq (first b) (rest b) env)))


;; Helper to print out the store for debugging
(define (print-store [sto : Store]) : Void
  (define (print-binding [b : store-binding]) : Void
    (define loc (store-binding-loc b))
    (define val (store-binding-val b))
    (printf "~a -> ~a\n" loc val))
  (for-each print-binding (Store-bindings sto))
  (void))

;; OAZO7 TEST CASES
;;-----------------------------------------------------------------------------------


(top-interp '{arr-eq? {arr 2 3} {arr 4 1}})

(check-equal? (top-interp '{let {x <- 5}
                                {seq {x := 10} x}}) "10")

#;(top-interp '{{anon {x} : {x 1}}
              {anon {y} : {+ y 2}}})


#;(top-interp '{{anon {x y} : {+ x y}} 5 7})


(check-equal? (top-interp '{let {f1 <- {anon {x} : {x := {+ x 5}}}}
                                {a <- 10}
                                 a}) "15")


#;(top-interp '{let {f <- {anon {a} : {+ a 4}}}
                                {f 1}})


#;(check-equal? (top-interp '{seq
                             {+ 1 2}
                             {+ 2 3}}) "5")

(define test-env
  (list (env-binding 'r 5)
        (env-binding 'e 4)
        (env-binding 'w 3)
        (env-binding 'z 2)
        (env-binding 'y 1)
        (env-binding 'x 0)))

(define test-sto
  (Store
   (list (store-binding 5 (numV 5))
         (store-binding 4 (numV 4))
         (store-binding 3 (numV 3))
         (store-binding 2 (numV 2))
         (store-binding 1 (numV 1))
         (store-binding 0 (numV 0))) 6))


(check-equal? (top-interp '{arr 2 3}) "18-2")

(check-equal? (top-interp '{let {x <- {arr 2 3}}
                                {aref x 0}}) "3")



;; Top-Interp Tests
(check-equal? (top-interp '{+ 1 2}) "3")

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

(check-equal? (top-interp '{{anon {x y} : {+ x y}} 5 7}) "12")

(check-equal? (top-interp '{{anon {x y z} :
                                 {+ x {+ y z}}} 1 2 3}) "6")

(check-equal? (top-interp '{let {f <- {anon {a} : {+ a 4}}}
                                {f 1}}) "5")

(check-exn #rx"OAZO" (lambda() (top-interp '{{anon {x x} : 3} 1 1})))
(check-exn #rx"OAZO" (lambda() (top-interp '{{anon {x x} : 3} 1 1})))
(check-exn #rx"OAZO" (lambda () (top-interp
                                 '{let {f <- {anon {x} : {+ x 1}}}
                                       {y <- {anon {z} : {f 4}}}
                                       {y 3}})))
(check-exn #rx"OAZO" (lambda () (top-interp
                                 '{{anon {} : 12} 1})))
(check-exn #rx"OAZO" (lambda() (top-interp
                                  '{{func {ignoreit x}: {+ 3 4}}
                                    {func {main} : {ignoreit {/ 1 {+ 0 0}}}}})))
(check-exn #rx"OAZO" (lambda() (top-interp '{{anon {x x} : 3} 1 1})))


;; Interp Tests
(check-equal? (v*s-val (interp (appC (idC '+) (list (numC 1) (numC 1))) top-env top-sto)) (numV 2)) 
(check-equal? (v*s-val (interp (appC (idC '-) (list (numC 3) (numC 1))) top-env top-sto)) (numV 2))
(check-equal? (v*s-val (interp (appC (idC '*) (list (numC 12)(numC 2))) top-env top-sto)) (numV 24))  
(check-equal? (v*s-val (interp (appC (idC '/) (list (numC 6) (numC 2))) top-env top-sto)) (numV 3))
(check-equal? (v*s-val (interp (appC (idC '<=) (list(numC 0) (numC 2))) top-env top-sto)) (boolV true))
(check-equal? (v*s-val (interp (appC (idC 'num-eq?) (list (numC 21) (numC 21))) top-env top-sto)) (boolV true))
(check-equal? (v*s-val (interp (appC (idC 'str-eq?) (list (strC "hi") (strC "hi"))) top-env top-sto)) (boolV true))
(check-exn #rx"OAZO" (lambda()(interp (ifC (numC 5) (numC 1) (numC 2)) top-env top-sto)))
(check-exn #rx"OAZO" (lambda()(interp (appC (idC '+) (list (strC "oops") (numC 1))) top-env top-sto)))


;; IfC Tests
(check-equal? (top-interp '{if {<= 4 3} then 29387 else true})"true")
(check-equal? (top-interp '{if {<= 2 3} then 29387 else true})"29387")
(check-equal? (top-interp '{if {<= 2 3} then false else true})"false")

;; OAZO ERROR
#;(check-exn #rx"OAZO"(lambda ()(top-interp '(+ 4 (error "1234")))))
#;(check-exn #rx"OAZO"(lambda ()(top-interp '(<= 4))))
#;(check-exn #rx"OAZO"(lambda ()(top-interp '((anon (e) : (e e)) error))))
(check-exn #rx"OAZO"(lambda ()(top-interp '(+ 4 #t))))
(check-exn #rx"OAZO"(lambda ()(top-interp '(- 4 "s"))))
(check-exn #rx"OAZO"(lambda ()(top-interp '(* 4 "s")))) 
(check-exn #rx"OAZO"(lambda ()(top-interp '(/ 4 "f"))))
(check-exn #rx"OAZO"(lambda ()(top-interp '(<= 4 "f"))))
(check-exn #rx"OAZO"(lambda ()(top-interp '(/ + + )))) 
(check-exn #rx"OAZO"(lambda ()(top-interp '(+ 4 (error)))))
(check-exn #rx"OAZO"(lambda ()(top-interp '(+ ))))
(check-exn #rx"OAZO"(lambda ()(top-interp '(+ else))))  
(check-exn #rx"OAZO"(lambda() (top-interp '(/ 1 (- 3 3)))))
(check-exn #rx"OAZO"(lambda() (top-interp '(3 4 5)))) 

;; apply-primop tests
(check-equal? (v*s-val (apply-primop  (primopV 'num-eq?) (list (numV 5) (numV 5)) top-env top-sto)) (boolV #t))
(check-equal? (v*s-val (apply-primop  (primopV 'str-eq?) (list (strV "hello") (strV "hello")) top-env top-sto)) (boolV #t))
(check-exn #rx"OAZO" (lambda () (apply-primop (primopV 'num-eq?) (list (numV 5) (strV "5")) top-env top-sto)))
(check-exn #rx"OAZO" (lambda () (apply-primop (primopV 'str-eq?) (list (numV 5) (strV "5")) top-env top-sto)))

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
(check-equal? (parse '{{anon {x y} : {+ x y}} 5 7})
              
              (appC (lamC (list 'x 'y)
                          (appC (idC '+)
                                (list (idC 'x) (idC 'y))))
              (list (numC 5)
                    (numC 7))))
(check-equal? (parse '{f 4}) (appC (idC 'f) (list(numC 4))))
(check-exn #rx"OAZO" (lambda() (parse '(let (z <- (anon () : 3)) (z <- 9) (z))))) 
(check-exn #rx"OAZO" (lambda() (parse '{{anon {2} : {1}} 1})))
(check-exn #rx"OAZO" (lambda() (parse '{let {c <- 5}})))
(check-exn #rx"OAZO" (lambda() (parse '(+ then 4))))
(check-exn #rx"OAZO" (lambda() (parse '{let {: <- ""} "World"})))
(check-exn #rx"OAZO" (lambda() (parse '{anon {i} : "hello" 31/7 +})))

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


;;Serialize
(check-equal? (serialize (numV 1)) "1")
(check-equal? (serialize 1) "1")
(check-equal? (serialize #t) "true")
(check-equal? (serialize #f) "false")
(check-equal? (serialize (strV "Hello")) "\"Hello\"")
(check-equal? (serialize (primopV '+)) "#<primop>")  
(check-equal? (serialize (closeV (list 'x 'y) (appC (idC '+) (list (numC 1)
                                                                   (numC 1))) (list (env-binding 'x 0)
                                                                                    (env-binding 'y 1)))) "#<procedure>")
(check-exn #rx"OAZO" (lambda()(serialize "string")))


;; Check-duplicates tests
(define symbols1 '(a b c d))
(define symbols2 '(x y z y))
(check-equal? (check-duplicates symbols1) #t)
(check-equal? (check-duplicates symbols2) #f)


;;helper
#;(check-equal? (bind (list 'x 'y 'z) (list 1 2 3))
              (list (env-binding 'x 1) (env-binding 'y 2) (env-binding 'z 3)))
#;(check-equal? (bind (list 't 'b 'dd) (list (boolV #f) 2 (primopV '+)))
              (list (env-binding 't (boolV #f)) (env-binding 'b 2) (env-binding 'dd (primopV '+))))
#;(check-equal? (bind (list 'a) (list (closeV (list 'v 'c 'd) 2
                                            (list (env-binding 'x 1) (env-binding 'y 1) (env-binding 'z 1)))))
              (list (env-binding 'a (closeV (list 'v 'c 'd) 2
                                        (list (env-binding 'x 1) (env-binding 'y 1) (env-binding 'z 1))))))
(check-exn #rx"OAZO" (lambda()(bind '(a) '()))) 


