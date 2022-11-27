#lang plai

;<RLFAE> :: =       <num>
;                  | {+ <RLFAE> <RLFAE>}
;                  | {- <RLFAE> <RLFAE>}
;                  | {* <RLFAE> <RLFAE>}
;                  | {= <RLFAE> <RLFAE>}
;                  | <id>
;                  | {fun {<id>} <RLFAE>}
;                  | {<RLFAE> <RLFAE>}
;                  | {ifexp <RCFAE> <RCFAE> <RCFAE>}
;                  | {orop <RCFAE> <RCFAE>}

(define-type RLFAE
  [num (n number?)]
  [add (lhs RLFAE?) (rhs RLFAE?)]
  [sub (lhs RLFAE?) (rhs RLFAE?)]
  [mul (lhs RLFAE?) (rhs RLFAE?)]
  [eq (lhs RLFAE?) (rhs RLFAE?)]
  [id (name symbol?)]
  [fun(param symbol?)(body-expr RLFAE?)]
  [app (f RLFAE?) (a RLFAE?)]
  [ifexp (test-expr RLFAE?)
       (then-expr RLFAE?) (else-expr RLFAE?)]
  [rec (name symbol?) (named-expr RLFAE?) (fst-call RLFAE?)]
  [orop (lhs RLFAE?) (rhs RLFAE?)])


(define-type RLFAE-Value
  [numV (n number?)]
  [closureV (param symbol?)
            (body RLFAE?)
            (ds DefrdSub?)]
  [exprV (expr RLFAE?) (ds DefrdSub?)
         (value (box/c (or/c false
                             RLFAE-Value?)))])

;DefrdSub
(define-type DefrdSub
    [mtSub]
    [aSub (name symbol?) (value RLFAE-Value?) (ds DefrdSub?)]
    [aRecSub (name symbol?)
             (value-box (box/c RLFAE-Value?))
             (ds DefrdSub?)])

; [contract] strict:
(define (strict v)
  (type-case RLFAE-Value v
    [exprV (expr ds v-box)
           (if (not (unbox v-box))
               (local [(define v (strict (interp expr ds)))]
                 (begin (set-box! v-box v) v))
               (unbox v-box))]
    [else v]))

; [contract] num-op: (number number -> number) -> (RLFAE RLFAE -> RLFAE)
(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n (strict x)) (numV-n (strict y))))))
(define num+ (num-op +))
(define num- (num-op -))
(define num* (num-op *))

; [contract] RLFAE-Value -> boolean
(define (numzero? n)
  (zero? (numV-n n)))

(define (is-in-list list value)
 (cond
  [(empty? list) false]
  [(equal? (first list) value) true]
  [else (is-in-list (rest list) value)]))

;(if (is-in-list  '(qq oa 3 4 ifexp op or) 'ifexp) (print "yaho") (print "noyaho"))

;[contract] is-recursion: RLFAE DefrdSub->bool
;[purpose] to check wheter an RLFAE expression contains recursion
(define (is-recursion origin-ftn v n)
  (cond
    [(= n 0)
     (when (list? v)
      (for([i v]) ; when true
        (when (list? i)
          (print i)
          (when (is-in-list i 'ifexp)
            (display " yaho ")
            (is-recursion i origin-ftn 1))))
      ) ] ; first input
    [(= n 1)
     (when (list? v)
      (for([i v]) ; when true
        (when (list? i)
          ;(print i)
          (if (is-recursion i origin-ftn 2)
              (#t)
          (when (not (empty? (rest i))) (is-recursion i origin-ftn 2))))))] ; ifexp?
    [(= n 2)
     (when (list? v)
      (for([i v]) ; when true
        (when (list? i)
          (display origin-ftn)
          (is-in-list i origin-ftn)))
      )]
    [else #f]) ; rec?
  )




;    (if (empty? (rest l))
;        (#f)
;        (is-member (rest l) exp))))

;(when (and (list? v-arg) (member 'ifexp v-arg))
;                    (when (member origin-ftn (member'ifexp v-arg))
;                      (print "recursive"))
;                      (printf "first :~a\n" (second(last (rest (member'ifexp v-arg)))))
;                    #t)
;[contract] is-recursion: RLFAE DefrdSub->bool
;[purpose] to check wheter an RLFAE expression contains recursion
(define (desugar v)
  ;(print "desugar")
  v
  )


;[rec (bound-id named-expr fst-call)
;     (local [(define value-holder (box (numV 198)))
;              (define new-ds (aRecSub bound-id
;                                      value-holder
;                                      ds))]
;        (begin
;          (set-box! value-holder (interp named-expr new-ds))
;          (interp fst-call new-ds)))]

; [contract] lookup: symbol DefrdSub -> RCFAE-Value
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

; [contract] parse: sexp -> RLFAE
(define (parse sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse l) (parse r))]
    [(list '- l r) (sub (parse l) (parse r))]
    [(list '* l r) (mul (parse l) (parse r))]
    [(list '= l r) (eq (parse l) (parse r))]
    [(list 'with (list i v) e) (app (fun i (parse e)) (if (is-recursion i v 0)
                                                          (parse (desugar v))
                                                          (parse v)))] ; i에서 recursive check [(list 'with (list i v) e) (app (fun i (parse e)) (parse v))]
    ;(if (is-recursion i v)
                                                         ; (parse (desugar v))
                                                          ;(parse v))
    [(? symbol?) (id sexp)]
    [(list 'fun (list p) b) (fun p (parse b))]
    [(list f a) (app (parse f) (parse a))]
    [(list 'ifexp te th el) (ifexp (parse te) (parse th) (parse el))]
    [(list 'rec (list rfn ne) body) (rec rfn (parse ne) (parse body))]
    [(list 'orop l r) (orop (parse l) (parse r))]
    [else (error 'parse "bad syntax: ~a" sexp)]))

; [contract] interp: RLFAE DefrdSub -> RLFAE-Value
(define (interp rlfae ds)
  (type-case RLFAE rlfae
    [num (n) (numV n)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [mul (l r) (num* (interp l ds) (interp r ds))]
    [eq (l r) (equal? (interp l ds) (interp r ds))]
    [id (name) (lookup name ds)]
    [fun (param body-expr) (closureV param body-expr ds)]
    [app (f a)
             (local [(define ftn (interp f ds))]
                            (interp (closureV-body ftn)
                                         (aSub (closureV-param ftn)
                                                     (interp a ds)
                                                     (closureV-ds ftn))))]
    [ifexp (test-expr then-expr else-expr)
         (if (interp test-expr ds)
             (interp then-expr ds)
             (interp else-expr ds))]
    [rec (bound-id named-expr fst-call)
     (local [(define value-holder (box (numV 198)))
              (define new-ds (aRecSub bound-id
                                      value-holder
                                      ds))]
        (begin
          (set-box! value-holder (interp named-expr new-ds))
          (interp fst-call new-ds)))]
    [orop (l r)
          (or (interp l ds) (interp r ds))]))


(define (run sexp ds)
  (interp (parse sexp) ds))

(parse '{rec {fac {fun {n}
                       {ifexp {= n 0}
                            1
                            {* n {fac {- n 1}}}}}}
          {fac 3}})

(parse '{rec {fib {fun {n}
                        {ifexp {orop {= n 0} {= n 1}}
                               1
                               {+{fib {- n 1}} {fib {- n 2}}}}}}
           {fib 3}})

(parse '{with {fac {fun {n}
                       {ifexp {= n 0}
                            1
                            {* n {fac {- n 1}}}}}}
          {fac 3}} )

(parse '{with {fib {fun {n}
                        {ifexp {orop {= n 0} {= n 1}}
                               1
                               {+{fib {- n 1}} {fib {- n 2}}}}}}
           {fib 3}})

(run '{rec {fac {fun {n}
                       {ifexp {= n 0}
                            1
                            {* n {fac {- n 1}}}}}}
          {fac 3}} (mtSub))

(run '{rec {fib {fun {n}
                        {ifexp {orop {= n 0} {= n 1}}
                               1
                               {+{fib {- n 1}} {fib {- n 2}}}}}}
           {fib 3}}(mtSub))


(parse '{orop {= 2 2} {= 1 0}})
(run '{orop {= 1 2} {= 1 0}} (mtSub))
;(parse '{with{fun {x} {+ x x}}} )
(run'{+ {with {x 10} {+ x x}} 4} (mtSub))


(parse '{with {fac {fun {x} 1}} {with {fac {fun {n}
                                                 {ifexp {= n 0}
                                                     1
                                                     {* n {fac {- n 1}}}}}} {fac 10}}})

(parse '{with {fac {fun {n}
                        {ifexp {= n 0}
                               1
                               {* n {fac {- n 1}}}}}} {fac 10}})

;(run '{with {fac {fun {x} 1}} {with {fac {fun {n}
;                                                 {ifexp {= n 0}
;                                                     1
;                                                     {* n {fac {- n 1}}}}}} {fac 4}}} (mtSub))
;(run '{rec {fac {fun {n}
;                        {ifexp {= n 0}
;                               1
;                               {* n {fac {- n 1}}}}}} {fac 10}} (mtSub))

(parse '{with {sum {fun {x} {+ x x}}} {sum 10}})
(parse '{with {sum {fun {n} {ifexp {= n 0} 0 {+ {sum {- n 1}} n}}}} {sum 10}})
'{with {sum {fun {n} {ifexp {= n 0} 0 {+ {sum {- n 1}} n}}}} {sum 10}}
(app (fun 'sum (app (id 'sum) (num 10))) (fun 'n (ifexp (eq (id 'n) (num 0)) (num 0) (add (app (id 'sum) (sub (id 'n) (num 1))) (id 'n)))))
(rec 'fac (fun 'n (ifexp (eq (id 'n) (num 0)) (num 1) (mul (id 'n) (app (id 'fac) (sub (id 'n) (num 1)))))) (app (id 'fac) (num 3)))
(app (fun 'fac (app (id 'fac) (num 3))) (fun 'n (ifexp (eq (id 'n) (num 0)) (num 1) (mul (id 'n) (app (id 'fac) (sub (id 'n) (num 1)))))))

