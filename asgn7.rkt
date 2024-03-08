#lang typed/racket
(require typed/rackunit)

;; Assignment - OAZO7
;; ... Project Implemented


;; OAZO Data Definitions
;;-----------------------------------------------------------------------------------

;; Expressions
(struct numC    ([n : Real])                                   #:transparent)
(struct idC     ([s : Symbol])                                 #:transparent)
(struct appC    ([exp : ExprC] [args : (Listof ExprC)])        #:transparent)
(struct ifC     ([test : ExprC] [then : ExprC] [else : ExprC]) #:transparent)
(struct strC    ([str : String])                               #:transparent)
(struct lamC    ([args : (Listof Symbol)] [types : (Listof Type)]
                                          [body : ExprC])      #:transparent)
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
(struct Tbinding ([name : Symbol] [type : Type])                #:transparent)
(define-type Env (Listof env-binding))
(define-type TEnv (Listof Tbinding))
(define mt-env  '())

;; Store
(define-type Location Real)
(struct Store ([bindings : (Listof store-binding)] [next : Real])       #:transparent)
(struct v*s   ([val : Value] [sto : Store])                             #:transparent)
(struct lv*s  ([lst : (Listof Value)] [sto : Store])                    #:transparent)
(struct e*s   ([env : Env] [sto : Store])                               #:transparent)
(struct b*s   ([base : Location] [sto : Store])                         #:transparent)
(define add-store cons)

;; Types
 #;(ty	 	=	 	num
 	 	|	 	bool
 	 	|	 	str
 	 	|	 	void
 	 	|	 	{ty ... -> ty}
 	 )

;; TODO Add numarray!
(struct numT  ()                          #:transparent)
(struct boolT ()                          #:transparent)
(struct strT  ()                          #:transparent)
(struct voidT ()                          #:transparent)
(struct arrT  ()                          #:transparent)
(struct funT ([in : (Listof Type)] [out : Type]) #:transparent)
(define-type Type (U numT boolT strT voidT funT arrT))

;; Top Level Environment
(define top-env
  (list (env-binding 'substring 16)
        (env-binding 'seq 15)
        (env-binding 'alen 14)
        (env-binding 'aset 13)
        (env-binding 'aref 12)
        (env-binding 'arr 11)
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
   (list (store-binding 16 (primopV 'substring))
         (store-binding 15 (primopV 'seq))
         (store-binding 14 (primopV 'alen))
         (store-binding 13 (primopV 'aset))
         (store-binding 12 (primopV 'aref))
         (store-binding 11 (primopV 'arr))
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
         (store-binding 0 (boolV #f))) 17))

;; top-type-env
(define type-env
  (list (Tbinding '+ (funT (list (numT) (numT)) (numT)))
        (Tbinding '- (funT (list (numT) (numT)) (numT)))
        (Tbinding '/ (funT (list (numT) (numT)) (numT)))
        (Tbinding '* (funT (list (numT) (numT)) (numT)))
        (Tbinding 'str-eq? (funT (list (strT) (strT)) (boolT)))
        (Tbinding 'num-eq? (funT(list (numT) (numT))(boolT)))
        (Tbinding 'arr (funT (list (numT) (numT)) (arrT)))
        (Tbinding 'aref (funT (list (arrT) (numT)) (numT)))
        (Tbinding 'aset (funT (list (arrT) (numT) (numT)) (voidT)))
        (Tbinding 'alen (funT (list (arrT)) (numT)))
        (Tbinding 'arr-eq? (funT (list (arrT) (arrT)) (boolT)))
        (Tbinding 'substring (funT (list (strT) (numT) (numT)) (strT)))
        (Tbinding 'true (boolT))
        (Tbinding 'false (boolT))))


;; TOP-INTERP
;;-----------------------------------------------------------------------------------
;; Interprets the entirely parsed program
(define (top-interp [s : Sexp]) : String
   (serialize (v*s-val (interp (parse s) top-env top-sto))))

;; with type checking
#;(define (top-interp [s : Sexp]) : String
  (define parsed (parse s))
  (type-check parsed type-env)
  (serialize (v*s-val (interp parsed top-env top-sto))))


;; INTERP
;;-----------------------------------------------------------------------------------
;; Inteprets the given expression using list of funs to resolve appC's
(define (interp [e : ExprC] [env : Env] [sto : Store]) : v*s
  (match e
    [(numC n)       (v*s (numV n) sto)]
    [(strC str)     (v*s (strV str) sto)]
    [(idC s)        (v*s (fetch (lookup s env) (Store-bindings sto)) sto)]
    [(setC sym val) (define new-state (interp val env sto))
                    (v*s (nullV) (mutate-store (lookup sym env) (v*s-val new-state) env (v*s-sto new-state)))]
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
      
       #;[else (error 'interp "OAZO: Error in appC ~v" func)])]
    [(ifC test then else)        ;; ifC
     (define test-result (interp test env sto))
     (cond [(boolV? (v*s-val test-result))
            (cond [(boolV-b (v*s-val test-result)) (interp then env (v*s-sto test-result))]
                  [else (interp else env (v*s-sto test-result))])]
           [else (error 'interp "OAZO: Test was not a boolean expression: ~e" e)])]
    
    [(lamC a ty body) (v*s (closeV a body env) sto)]))


;; Helper that extends a current environemt/store and returns the updated e*s
(define (extend-both [env : Env] [params : (Listof Symbol)] [args : (Listof Value)] [sto : Store]) : e*s
  (cond
    [(empty? params) (e*s env sto)]
    [else (define cell (lookup (first params) env))
          (if (> cell -1) 
              (extend-both env (rest params) (rest args)
                           (mutate-store (lookup (first params) env) (first args) env sto))

              (extend-both (cons (env-binding (first params)  (Store-next sto)) env)
                           (rest params) (rest args) (Store (cons (store-binding
                                                                   (Store-next sto) (first args)) (Store-bindings sto))
                                                            (+ 1 (Store-next sto)))))]))

;; Mutates the store by replacing the value at a locaiton and returns the new store
(define (mutate-store [loc : Location] [value : Value] [env : Env] [store : Store]) : Store
    (let ([location loc])
      (define (update-store [lst : (Listof store-binding)] [index : Real]
                            [cnt : Real] [val : Value]) : (Listof store-binding)
        (if (= location -1) (error 'mutate "OAZO: binding does not already exist")
          (cond
            #;[(empty? lst) lst]  
            [(= cnt 0)        
             (cons (store-binding index val) (rest lst))]
            [else             
             (cons (first lst) (update-store (rest lst) index (- cnt 1) val))])))
    (let ([updated-bindings (update-store (Store-bindings store) location
                                          (- (- (Store-next store) 1) location) value)])
      (Store updated-bindings (Store-next store)))))


;; Helper to check the number of param vs given arguments
(define (check-args [param : (Listof Symbol)] [args : (Listof Value)]) : Boolean
  (if (= (length param) (length args)) #t
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
    [(equal? primop (primopV 'alen))
     (if (arrV? (first args)) (v*s (alen (first args)) sto)
            (error 'apply-primop "OAZO ERROR: Wrong argument for alen"))]
    [(and (equal? primop (primopV 'seq)) (= (length args) 1))
      (v*s (first args) sto)]
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
            (error 'apply-primop "OAZO ERROR: Wrong argument/s for aref"))]
       [(primopV 'aset)
        (if (and (arrV? f) (numV? second) (numV? (first (rest (rest args)))))
                 (v*s (nullV) (aset f (numV-n second) (first (rest (rest args))) env sto))
                 (error 'apply-primop "OAZO ERROR: Wrong argument/s for arr"))]
       [(primopV 'substring) (sub-str args sto)]
       [(primopV 'seq) (v*s (seq (first args) (rest args) env) sto)])]))

;; returns substring of input String
(define (sub-str [args : (Listof Value)] [sto : Store]) : v*s
 (match args
   [(list (? strV? str) (? numV? start) (? numV? end))
    (cond
      [(or (< (numV-n start) 0)
           (> (numV-n end) (string-length (strV-str str)))
           (> (numV-n start) (numV-n end)))
       ((error 'OAZO "Index out of bounds for substring"))]
      #;[(not (and (integer? (numV-n start)) (integer? (numV-n end))))
       (error 'OAZO "Index for sub-str must be an integer")]
      [else (v*s (strV (substring (strV-str str)
                                     (cast (numV-n start) Integer)
                                     (cast (numV-n end) Integer))) sto)])]
   [other (error 'OAZO "Not a valid input for substring")]))


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
(define (aset [arr : arrV] [idx : Real] [val : Value] [env : Env] [sto : Store]) : Store
  (cond
    [(or (< idx 0) (>= idx (arrV-len arr))) (error 'aset "OAZO: Index out of bounds")]
    [else (mutate-store (+ (arrV-loc arr) idx) val env sto)]))

;; Given an index and an array and a value mutate the array to be the new val
(define (alen [arr : arrV]) : Value
  (cond
    #;[(= (arrV-loc arr) -1) (error 'alen "OAZO: Array Does not Exist")]
    [else (numV (arrV-len arr))]))


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
    [(list _ '<- _) (error 'parse "OAZO")]                 ;; weird case 
    [(list 'let (list(list ids ': ty) '<- args)...  body)                         ;; letC
     (if (check-duplicates (cast ids (Listof Sexp)))
         (let([types (map(lambda ([x : Sexp])(parse-type x)) (cast ty (Listof Sexp)))]) 
           (appC (lamC (cast ids(Listof Symbol)) types (parse body))
                 (map(lambda ([a : Sexp]) (parse a)) (cast args (Listof Sexp))))) 
         (error 'parse "OAZO Error: Expected a list of non-duplicate symbols for parameters"))]
  
    [(list 'anon (list(list ty ids) ...) ': body)          ;; lamC
     (if (and (list? ids) ( all-symbol-and-valid? (cast ids (Listof Sexp))) (check-body body))
         (let([types (map(lambda ([x : Sexp])(parse-type x)) (cast ty (Listof Sexp)))]) 
         (lamC (cast ids(Listof Symbol)) types (parse body))) 
         (error 'parse "OAZO Error: Expected a list of non-duplicate symbols for parameters in ~e" code))]
    
    [(list func exps ...)                                  ;; appC
     (appC (parse func) (map (lambda ([exps : Sexp])
                    (parse exps)) exps))]
    
    [other (error 'parse "OAZO Syntax error in ~e" other)]))

;; Parse-type helper function for parse
(define (parse-type [ty : Sexp]) : Type
   (match ty
    [(? symbol? 'num) (numT)]
    [(? symbol? 'str) (strT)]
    [(? symbol? 'bool) (boolT)]
    [(? symbol? 'void) (voidT)]
    [(? symbol? 'arr) (arrT)]
    [(? symbol? 'numarray) (arrT)]
    [(list in ... '-> out) (funT (map (lambda ([x : Sexp])(parse-type x))
                                      (cast in (Listof Sexp))) (parse-type out))]
    [else (error 'parse-type "OAZO Error: invalid type in given Sexp ~e" ty)]))

;; Recursive type check function that takes in an exprC and a type env and
;; outputs the correct type, if able to determine
(define (type-check [e : ExprC] [env : TEnv]) : Type 
  ;;CHECK THAT THE TEST VALUE OF THE IF IS A BOOL!
 (match e
   [(? numC?) (numT)]
   [(? strC?) (strT)]
   ;;sequence you just need to make sure that all of the types in the sequence are valid.
   [(appC (idC 'seq) args) (define s : (Listof Type) (map(lambda ([a : ExprC])
                                                           (type-check a env)) (cast args (Listof ExprC))))
                           (last s)]
   [(idC id) (lookupType id env)] 

   ;; setC is something like this, should return void but you need to
   ;; check that the variable type and the thing it is getting changed to are the same
   [(setC sym val) (if (equal? (lookupType sym env) (type-check val type-env))  
                       (voidT) 
                       (error 'type-check "OAZO Error: TYPE ERROR in a variable mutation!"))]
   
   [(ifC test then else) (if (equal? (type-check then env) (type-check else env))
                             (type-check else env)
                             (error 'type-check "OAZO Error: TYPE ERROR then and else
segments of ifC are different types!"))]
   ;;check number of args 
   [(appC f args) (define f-ty : Type (type-check f env))
                  #;(printf "f type: ~v, args: ~v\n" f-ty args)
                  (match f-ty 
                    [(funT in ret) (if (equal? in (map (lambda ([x : ExprC])(type-check x env)) args))
                                    ret
                                   (error 'type-check "OAZO Error: TYPE ERROR incorrect operand type!"))]
                    [_ (error 'type-check "OAZO Error: did not return a funT in type-checker")])]
                    
  [(lamC args ty body) (funT ty (type-check body (extend-Tenv (bindType args ty) env)))]))


;; SERIALIZE
;;-----------------------------------------------------------------------------------
;; Turns objects into string literals
(define (serialize [val : Any]) :  String
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
    [(? arrV? arr) (string-append (number->string (arrV-loc arr))
                                  "-" (number->string (arrV-len arr)))]
    [else (error 'serialize "OAZO Unsupported value: ~v" val)]))



;; HELPER FUNCTIONS
;;-----------------------------------------------------------------------------------

;; Helper that looks up a value in an environment
(define (lookup [for : Symbol] [env : Env]) : Location
    (match env
      ['() -1]
      [(cons (env-binding name location) r) (cond
                                              [(symbol=? for name) location]
                                              [else (lookup for r)])]))

;; Helper that looks up type in a type environment
(define (lookupType [for : Symbol] [env : TEnv]) : Type
    (match env
      ['() (error 'lookup "OAZO ERROR: name not found: ~e" for)]
      [(cons (Tbinding name ty) r) (cond
                                     [(symbol=? for name) ty]
                                     [else (lookupType for r)])]))

;; Helper to append two type environments
(define (extend-Tenv [env1 : (Listof Tbinding)] [env2 : (Listof Tbinding)]) : TEnv
  (append env1 env2))

;; Helper to bind the list of symbols with a list of types
(define (bindType [sym : (Listof Symbol)] [ty : (Listof Type)]) : (Listof Tbinding)
  (match sym
    ['() '()]
    [(cons s rest-s)
     (match ty
       ['() (error 'bind "OAZO Error: Mismatched number of arguments and symbols")]
      ;; [(list (? closeV? c)) (bind sym (closeV-body c))]
       [(cons v rest-v) (cons (Tbinding s v) (bindType rest-s rest-v))])]))

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

;; Checks the body of the lamC and ensures that it is either a single argument
;; or that there are proper {} around them
(define (check-body [body : Sexp]) : Boolean
  (match body
    [(list _ ...) #t]  
    [_ #t]))
 
;; Evaluate a sequence of args and return the result of the last
(define (seq [a : Value] [b : (Listof Value)] [env : Env]) : Value
   (if (empty? b) a
      (seq (first b) (rest b) env)))


;; Helper to print out the store for debugging
#;(define (print-store [sto : Store]) : Void
  (define (print-binding [b : store-binding]) : Void
    (define loc (store-binding-loc b))
    (define val (store-binding-val b))
    (printf "~a -> ~a\n" loc val))
  (for-each print-binding (Store-bindings sto))
  (void))

;; OAZO7 TEST CASES
;;-----------------------------------------------------------------------------------


(check-equal? (top-interp '{let {[a : numarray] <- {arr 1 0}}
                                {let {[a! : {num -> num}] <- {anon {[num expected]} :
                                                            {if {num-eq? {aref a 0} expected}
                                                                         then {seq {aset a 0 {+ 1 {aref a 0}}}
                                                                                   {aref a 0}}
                                                                         else {aref a 0}}}}
                                  {a! 1}}}) "0")


(check-equal? (top-interp '{let {[a : str] <- "test"}
                                {[start : num] <- 0}
                                {[end : num] <- 2}
                                {substring a start end}}) "\"te\"")

(check-exn #rx"OAZO" (lambda ()(top-interp '{let {[a : str] <- "test"}
                                              {[b : bool] <- "false"}
                                              {substring a b b}})))

(check-exn #rx"OAZO" (lambda ()(top-interp '{let {[a : str] <- "test"}
                                              {[start : num] <- 0}
                                              {[end : num] <- 5}
                                              {substring a start end}})))

(check-exn #rx"OAZO" (lambda () (top-interp '{+})))

;; aset tests
(check-equal? (top-interp '{let {[a : arr] <- {arr 10 3}}
                                {seq {aset a 7 999}
                                     {aref a 7}}}) "999")

(check-equal? (top-interp '{let {[a : numarray] <- {arr 10 3}}
                                {seq {aset a 7 999}
                                     {aref a 7}}}) "999")
(check-exn #rx"OAZO" (lambda () (top-interp '{let {[a : arr] <- {arr 10 3}}
                                                  {aset a -2 10}})))

(check-exn #rx"OAZO" (lambda () (top-interp '{let {[a : arr] <- {arr 10 3}}
                                                  {aset a 20 10}})))

(check-exn #rx"OAZO" (lambda () (top-interp '{let {[a : arr] <- {arr 10 3}}
                                                  {aset a "string" 10}})))

;; aref tests
(check-equal? (top-interp '{let {[a : arr] <- {arr 10 3}}
                                {aref a 2}}) "3")

(check-exn #rx"OAZO" (lambda () (top-interp '{let {[a : arr] <- {arr 10 3}}
                                                  {aref a -2}})))

(check-exn #rx"OAZO" (lambda () (top-interp '{let {[a : arr] <- {arr 10 3}}
                                                  {aref a 20}})))

(check-exn #rx"OAZO" (lambda () (top-interp '{let {[a : arr] <- {arr 10 3}}
                                                  {aref a "string"}})))

;; arr tests
(check-equal? (top-interp '{arr 10 3}) "17-10")
(check-exn #rx"OAZO" (lambda () (top-interp '{arr 0 0})))
(check-exn #rx"OAZO" (lambda () (top-interp '{arr "cat" "meow"})))

(check-equal? (top-interp '{seq 4}) "4")

;; Error Coverage
(check-exn #rx"OAZO" (lambda()(parse '{let {[a : str] <- "str"}
                                                      {[a : str] <- "pie"} a}) ))
(check-exn #rx"OAZO" (lambda()(type-check (parse '{let {[x : num] <- 10}
                                                    {x := "string"}}) type-env)))
(check-exn #rx"OAZO" (lambda () (type-check (appC (numC 1)
                                                  (list (numC 1) (numC 1))) type-env)))

(check-exn #rx"OAZO" (lambda()
                       (mutate-store -1 (numV 1) top-env top-sto)))

(check-exn #rx"OAZO" (lambda()
                       (check-args (list 's 's) (list (numV 1)))))

;; Parse-type tests
(check-equal? (parse-type 'num) (numT))
(check-exn #rx"OAZO" (lambda() (parse-type 't))) 
(check-equal? (parse-type 'str) (strT))
(check-equal? (parse-type 'bool) (boolT))
(check-equal? (parse-type 'void) (voidT))
(check-equal? (parse-type '{num -> num}) (funT (list (numT)) (numT)))
(check-equal? (parse-type '{str str -> bool}) (funT (list (strT) (strT)) (boolT)))
(check-exn #rx"OAZO" (lambda ()(parse '{{anon {[num x] [num x]} : {+ x x}} 1 1})))
(check-exn #rx"OAZO" (lambda ()(parse '{let {[x : num] -> 1}{[x : num] -> 1}{+ x x}})))
(check-exn #rx"OAZO" (lambda () (bindType '{x y} (list (numT)))))

;; Let parse Type Test
(check-equal? (parse '{let {[x : num] <- 5}
                           {[y : num] <- 7}
                        {+ x y}})
               
              (appC (lamC (list 'x 'y)
                          (list (numT) (numT))
                          (appC (idC '+)
                                (list (idC 'x) (idC 'y))))
              (list (numC 5)
                    (numC 7))))

(check-equal?(type-check (parse '{let {[a : str] <- "taco"}
                                      {[b : str] <- "pie"}
                                   {str-eq? a b}}) type-env)
             (boolT))

(check-exn #rx"OAZO" (lambda()(type-check (parse '{let {[a : str] <- 1}
                                      {[b : str] <- "pie"}
                                   {str-eq? a b}}) type-env)))


;; Too many operands type-check test
(check-exn #rx"OAZO" (lambda()
                       (type-check (parse '{let {[a : num] <- 1}
                                      {[b : num] <- 2}
                                      {[c : num] <- 3}
                                   {+ a b c}}) type-env))) 

(check-exn #rx"OAZO" (lambda()
                       (type-check (parse '{let {[a : num] <- 1}
                                      {[b : num] <- "bark"}
                                   {+ a b}}) type-env)))

(check-exn #rx"OAZO" (lambda()
                       (type-check (parse '{let {[a : num] <- 1}
                                      {[b : str] <- 2}
                                   {+ a b}}) type-env)))


;;TYPE CHECK TESTS 
#;(parse '{let {z <- {+ 7 8}}
                                {y <- 5}
                                {+ z y}})
#; '{{anon {seven} : {seven}}
               {{anon {minus} :
                    {anon {} : {minus {+ 3 10} {* 2 3} }}}
               {anon {x y} : {+ x {* -1 y}}}}}

#;(type-check(parse '{{anon {[{num -> num}seven]} : {seven}}
               {{anon {[{num -> num} minus]} :
                    {anon {} : {minus {+ 3 10} {* 2 3} }}}
               {anon {[num x] [num y]} : {+ x {* -1 y}}}}}) type-env )

(check-equal?(type-check (parse '{let {[f : {num -> num}] <- {anon {[num a]} : {+ a 4}}}
                                {f 1}}) type-env) (numT))

 
(check-equal? (type-check (appC (lamC '(x y) (list (numT) (numT))
                                      (appC (idC '+) (list (idC 'x) (idC 'y))))
                                (list (numC 5) (numC 7))) type-env) (numT))
(check-equal? (type-check (appC (idC '+) (list (numC 1) (numC 1))) type-env) (numT))
(check-equal? (type-check (appC (idC '/) (list (numC 1) (numC 1))) type-env) (numT))
(check-equal? (type-check (appC (idC '*) (list (numC 1) (numC 1))) type-env) (numT))
(check-equal? (type-check (appC (idC '-) (list (numC 1) (numC 1))) type-env) (numT))
;;(check-equal? (type-check (parse '{{anon {[num x]} : {anon {[{-> void} y]} :
;;{x := 10}}} 1}) type-env) (voidT))
#;'{let {[x : num] <- 5}
     {seq {x := 10} x}}
(check-equal? (type-check (parse '{seq
                             {+ 1 2}
                             {+ 2 3}}) type-env) (numT))

#;(check-equal? (type-check (parse ' {anon {[num x]}})))
 
(check-equal? (type-check (parse '{let {[x : num] <- 1}
                                   {let {[y : {-> void}] <- {anon {} : {x := 10}}}
                                     {y}}}) type-env) (voidT))


(check-equal? (type-check (appC (idC 'num-eq?) (list (numC 1) (numC 1))) type-env) (boolT))
(check-equal? (type-check (appC (idC 'str-eq?) (list (strC "pix") (strC "roop"))) type-env) (boolT))
(check-exn #rx"OAZO" (lambda() (type-check (appC (idC '+) (list (strC "1") (numC 1))) type-env)))
(check-exn #rx"OAZO" (lambda() (type-check (appC (idC 'p) (list (strC "1")
                                                                (numC 1))) type-env))) 
(check-equal? (type-check (strC "f") type-env) (strT))
(check-equal? (type-check (idC 'true) type-env) (boolT))
(check-equal? (type-check (idC 'false) type-env) (boolT))
(check-equal? (type-check (numC 1) type-env) (numT))
(check-equal? (type-check (ifC (idC 'true) (numC 2) (numC 1)) type-env) (numT))
;;(check-equal? (parse '{anon {{-> void} x} : }) (voidT))

(check-exn #rx"OAZO" (lambda() (type-check (ifC (idC 'true) (numC 2) (strC "str")) type-env)))

;; alen tests
(check-equal? (top-interp '{let {[a : arr] <- {arr 10 3}}
                                {alen a}}) "10")

(check-exn #rx"OAZO" (lambda ()(top-interp '{let {[a : arr] <- {arr 10 3}}
                                {alen "string"}})))

(check-exn #rx"OAZO" (lambda () (top-interp '{alen a})))

(check-exn #rx"OAZO" (lambda () (fetch 54 (Store-bindings top-sto))))

;; aset tests
(check-equal? (top-interp '{let {[a : arr] <- {arr 10 3}}
                                {seq {aset a 7 999}
                                     {aref a 7}}}) "999")

(check-exn #rx"OAZO" (lambda () (top-interp '{let {[a : arr] <- {arr 10 3}}
                                                  {aset a -2 10}})))

(check-exn #rx"OAZO" (lambda () (top-interp '{x := 1})))

(check-exn #rx"OAZO" (lambda () (top-interp '{let {[a : arr] <- {arr 10 3}}
                                                  {aset a 20 10}})))

(check-exn #rx"OAZO" (lambda () (top-interp '{let {[a : arr] <- {arr 10 3}}
                                                  {aset a "string" 10}})))

;; aref tests
(check-equal? (top-interp '{let {[a : arr] <- {arr 10 3}}
                                {aref a 2}}) "3")

(check-exn #rx"OAZO" (lambda () (top-interp '{let {[a : arr] <- {arr 10 3}}
                                                  {aref a -2}})))

(check-exn #rx"OAZO" (lambda () (top-interp '{let {[a : arr] <- {arr 10 3}}
                                                  {aref a 20}})))

(check-exn #rx"OAZO" (lambda () (top-interp '{let {[a : arr] <- {arr 10 3}}
                                                  {aref a "string"}})))


;; arr tests
(check-equal? (top-interp '{arr 10 3}) "17-10")
(check-exn #rx"OAZO" (lambda () (top-interp '{arr 0 0})))
(check-exn #rx"OAZO" (lambda () (top-interp '{arr "cat" "meow"})))


;;pickup aset is not updating the store, and also need to ask about passing by value

(check-equal? (top-interp '{arr-eq? {arr 2 3} {arr 4 1}}) "false")

(check-equal? (top-interp '{let {[x : num] <- 5}
                                {seq {x := 10} x}}) "10")

(check-equal? (top-interp '{let {[x : arr] <- {arr 5 3}}
                                {aset x 0 999}}) "null")


(check-equal? (top-interp '{let {[x : num] <- 33}
                                {let {[x : num] <- 11}
                                      x}}) "11")

#;(check-equal? (top-interp '{let {[f1 : {num -> num}] <- {anon {[num x]} : {x := {+ x 5}}}}
                                {[a : num] <- 10}
                                 a}) "10")


#;(check-equal? (top-interp '{let {[x : num] <- 10}
                           {let {[f : {void -> num}] <- {anon {} : {seq {x := 999}
                                                           7}}}
                                  {seq {f} x}}}) "999")


(check-exn #rx"OAZO" (lambda () (top-interp '{let {[a : num] <- 10}
                                                  {x := 5}})))
(check-equal? (top-interp '{seq
                             {+ 1 2}
                             {+ 2 3}}) "5")

(check-equal? (top-interp '{arr 2 3}) "17-2")

(check-equal? (top-interp '{let {[x : arr] <- {arr 2 3}}
                                {aref x 0}}) "3")

(check-exn #rx"OAZO" (lambda() (top-interp '{arr-eq? "string" "wont work"})))


;; Top-Interp Tests

(check-equal? (top-interp '{+ 1 2}) "3")

#;(check-equal? (top-interp '{{anon {[num seven]} : {seven}}
               {{anon {minus} :
                    {anon {} : {minus {+ 3 10} {* 2 3} }}}
               {anon {x y} : {+ x {* -1 y}}}}}) "7")


(check-equal? (top-interp '{let {[x : num] <- 5}
                                {[y : num] <- 7}
                                {+ x y}}) "12")

(check-equal? (top-interp '{let {[z : num] <- {+ 7 8}}
                                {[y : num] <- 5}
                                {+ z y}}) "20")


(check-equal? (top-interp '{{anon {[num x] [num y]} : {+ x y}} 5 7}) "12")

(check-equal? (top-interp '{{anon {[num x] [num y] [num z]} :
                                 {+ x {+ y z}}} 1 2 3}) "6")

(check-equal? (top-interp '{let {[f : [num -> num]] <- {anon {[num a]} : {+ a 4}}}
                                {f 1}}) "5")

(check-exn #rx"OAZO" (lambda() (top-interp '{{anon {[num x] [num x]} : 3} 1 1})))

(check-exn #rx"OAZO" (lambda () (top-interp
                                 '{let {[f : [num -> num]] <- {anon {[num x]} : {+ x 1}}}
                                       {[y : [num -> num]] <- {anon {[num z]} : {f 4}}}
                                       {y 3}})))

(check-exn #rx"OAZO" (lambda () (top-interp
                                 '{let {[seq : num] <- {anon {[num x]} : {+ x 1}}}
                                       {[y : [num -> num]] <- {anon {[num z]} : {f 4}}}
                                       {y 3}})))

(check-exn #rx"OAZO" (lambda () (top-interp
                                 '{{anon {} : 12} 1})))

#;(check-exn #rx"OAZO" (lambda() (top-interp
                                  '{{func {ignoreit x}: {+ 3 4}}
                                    {func {main} : {ignoreit {/ 1 {+ 0 0}}}}})))


;; Interp Tests
(check-equal? (v*s-val (interp (appC (idC '+)
                                     (list (numC 1) (numC 1))) top-env top-sto)) (numV 2)) 
(check-equal? (v*s-val (interp (appC (idC '-)
                                     (list (numC 3) (numC 1))) top-env top-sto)) (numV 2))
(check-equal? (v*s-val (interp (appC (idC '*)
                                     (list (numC 12)(numC 2))) top-env top-sto)) (numV 24))  
(check-equal? (v*s-val (interp (appC (idC '/)
                                     (list (numC 6) (numC 2))) top-env top-sto)) (numV 3))
(check-equal? (v*s-val (interp (appC (idC '<=)
                                     (list(numC 0) (numC 2))) top-env top-sto)) (boolV true))
(check-equal? (v*s-val (interp (appC (idC 'num-eq?)
                                     (list (numC 21) (numC 21))) top-env top-sto)) (boolV true))
(check-equal? (v*s-val (interp (appC (idC 'str-eq?)
                                     (list (strC "hi") (strC "hi"))) top-env top-sto)) (boolV true))
(check-exn #rx"OAZO" (lambda()(interp
                               (ifC (numC 5) (numC 1) (numC 2)) top-env top-sto)))
(check-exn #rx"OAZO" (lambda()(interp
                               (appC (idC '+) (list (strC "oops") (numC 1))) top-env top-sto)))


;; IfC Tests
(check-equal? (top-interp '{if {<= 4 3} then 29387 else 123})"123")
(check-equal? (top-interp '{if {<= 2 3} then 29387 else 123})"29387")

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

;; apply-primop tests
(check-equal? (v*s-val (apply-primop  (primopV 'num-eq?) (list (numV 5) (numV 5)) top-env top-sto)) (boolV #t))
(check-equal? (v*s-val (apply-primop  (primopV 'str-eq?) (list (strV "hello") (strV "hello"))
                                      top-env top-sto)) (boolV #t))
(check-exn #rx"OAZO" (lambda () (apply-primop (primopV 'num-eq?) (list (numV 5) (strV "5")) top-env top-sto)))
(check-exn #rx"OAZO" (lambda () (apply-primop (primopV 'str-eq?) (list (numV 5) (strV "5")) top-env top-sto)))

(check-exn #rx"OAZO" (lambda () (v*s-val (apply-primop  (primopV '+) '() top-env top-sto))))
(check-exn #rx"OAZO" (lambda () (v*s-val (apply-primop  (primopV '+) (list (strV "str") (numV 5)) top-env top-sto))))
(check-exn #rx"OAZO" (lambda () (v*s-val (apply-primop  (primopV '-) (list (strV "str") (numV 5)) top-env top-sto))))
(check-exn #rx"OAZO" (lambda () (v*s-val (apply-primop  (primopV '*) (list (strV "str") (numV 5)) top-env top-sto))))
(check-exn #rx"OAZO" (lambda () (v*s-val (apply-primop  (primopV '/) (list (strV "str") (numV 5)) top-env top-sto))))
(check-exn #rx"OAZO" (lambda () (v*s-val (apply-primop  (primopV 'num-eq?)
                                                        (list (strV "str") (numV 5)) top-env top-sto))))
(check-exn #rx"OAZO" (lambda () (v*s-val (apply-primop  (primopV 'str-eq?)
                                                        (list (strV "str") (numV 5)) top-env top-sto))))
(check-exn #rx"OAZO" (lambda () (v*s-val (apply-primop  (primopV 'arr-eq?)
                                                        (list (strV "str") (numV 5)) top-env top-sto))))
(check-exn #rx"OAZO" (lambda () (v*s-val (apply-primop  (primopV '<=)
                                                        (list (strV "str") (numV 5)) top-env top-sto))))
(check-exn #rx"OAZO" (lambda () (v*s-val (apply-primop  (primopV 'arr)
                                                        (list (strV "str") (numV 5)) top-env top-sto))))
(check-exn #rx"OAZO" (lambda () (v*s-val (apply-primop  (primopV 'aref)
                                                        (list (strV "str") (numV 5)) top-env top-sto))))
(check-exn #rx"OAZO" (lambda () (v*s-val (apply-primop  (primopV 'aset)
                                                        (list (strV "str") (numV 5)) top-env top-sto))))
(check-exn #rx"OAZO" (lambda () (v*s-val (apply-primop  (primopV 'alen)
                                                        (list (strV "str") (numV 5)) top-env top-sto))))
(check-exn #rx"OAZO" (lambda () (v*s-val (apply-primop  (primopV 'substring)
                                                        (list (strV "str") (numV 5)) top-env top-sto))))


;; Parse Tests

(check-equal? (parse '{12}) (numC 12))
(check-equal? (parse 'x) (idC 'x))
(check-equal? (parse "string") (strC "string"))
(check-equal? (parse '{+ 1 2}) (appC (idC '+) (list (numC 1) (numC 2))))
(check-equal? (parse '{if {<= x 1} then 1 else -1})
              (ifC (appC (idC '<=) (list (idC 'x) (numC 1))) (numC 1) (numC -1)))

(check-equal? (parse '{f 4}) (appC (idC 'f) (list(numC 4))))
(check-exn #rx"OAZO" (lambda() (parse '(let (z <- (anon () : 3)) (z <- 9) (z))))) 
(check-exn #rx"OAZO" (lambda() (parse '{{anon {2} : {1}} 1})))
(check-exn #rx"OAZO" (lambda() (parse '{let {[c : num] <- 5}})))
(check-exn #rx"OAZO" (lambda() (parse '(+ then 4))))
(check-exn #rx"OAZO" (lambda() (parse '{let {: <- ""} "World"})))
(check-exn #rx"OAZO" (lambda() (parse '{anon {i} : "hello" 31/7 +})))



;;Serialize
(check-equal? (serialize (numV 1)) "1")
(check-equal? (serialize 1) "1")
(check-equal? (serialize #t) "true")
(check-equal? (serialize (boolV #t)) "true")
(check-equal? (serialize #f) "false")
(check-equal? (serialize (strV "Hello")) "\"Hello\"")
(check-equal? (serialize (primopV '+)) "#<primop>")
(check-equal? (serialize (nullV)) "null")
(check-equal? (serialize (closeV (list 'x 'y) (appC (idC '+) (list (numC 1)
                                                                   (numC 1))) (list (env-binding 'x 0)
                                                                                    (env-binding 'y 1))))
              "#<procedure>")
(check-exn #rx"OAZO" (lambda()(serialize "string")))


;; Check-duplicates tests
(define symbols1 '(a b c d))
(define symbols2 '(x y z y))
(check-equal? (check-duplicates symbols1) #t)
(check-equal? (check-duplicates symbols2) #f)

;; parse tests:
(check-equal? (parse '{anon {[num x] [num y]} : {+ x y}})
              
              (lamC (list 'x 'y)
                    (list (numT) (numT))
                    (appC (idC '+)
                          (list (idC 'x) (idC 'y)))))

(check-equal? (parse '{anon {[str x] [str y]} : {+ x y}})
              
              (lamC (list 'x 'y)
                    (list (strT) (strT))
                    (appC (idC '+)
                          (list (idC 'x) (idC 'y)))))

(check-equal? (parse '{anon {[bool x] [bool y]} : {+ x y}})
              
              (lamC (list 'x 'y)
                    (list (boolT) (boolT))
                    (appC (idC '+)
                          (list (idC 'x) (idC 'y)))))

(check-equal? (parse '{anon {[void x] [void y]} : {+ x y}})
              
              (lamC (list 'x 'y) 
                    (list (voidT) (voidT))
                    (appC (idC '+)
                          (list (idC 'x) (idC 'y)))))




(check-equal? (parse '{if {<= x 1} then 1 else -1})
              
              (ifC (appC (idC '<=) (list (idC 'x) (numC 1))) (numC 1) (numC -1)))

(check-exn #rx"OAZO" (lambda () (parse '(let (z <- (anon () : 3)) (z <- 9) (z))))) 

(check-equal? (parse '{{anon {[num x] [num y]} : {+ x y}} 5 7})
              
              (appC (lamC (list 'x 'y)
                          (list (numT) (numT))
                          (appC (idC '+)
                                (list (idC 'x) (idC 'y))))
              (list (numC 5)
                    (numC 7))))

(check-equal? (parse '{f 4}) (appC (idC 'f) (list(numC 4))))
(check-exn #rx"OAZO" (lambda() (parse '{{anon {2} : {1}} 1})))

(check-exn #rx"OAZO" (lambda () (parse '(+ then 4))))


;;helper
#;(check-equal? (bind (list 'x 'y 'z) (list 1 2 3))
              (list (env-binding 'x 1) (env-binding 'y 2) (env-binding 'z 3)))
#;(check-equal? (bind (list 't 'b 'dd) (list (boolV #f) 2 (primopV '+)))
              (list (env-binding 't (boolV #f)) (env-binding 'b 2) (env-binding 'dd (primopV '+))))
#;(check-equal? (bind (list 'a) (list (closeV (list 'v 'c 'd) 2
                                            (list (env-binding 'x 1) (env-binding 'y 1) (env-binding 'z 1)))))
              (list (env-binding 'a (closeV (list 'v 'c 'd) 2
                                        (list (env-binding 'x 1) (env-binding 'y 1) (env-binding 'z 1))))))
