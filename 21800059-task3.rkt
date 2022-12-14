#lang plai

;<RCFAEDS> ::= <num>
;                  | {+ <RCFAEDS> <RCFAEDS>}
;                  | {- <RCFAEDS> <RCFAEDS>}
;                  | {* <RCFAEDS> <RCFAEDS>}
;                  | {= <RCFAEDS> <RCFAEDS>}
;                  | <id>
;                  | {fun {<id>} <RCFAEDS>}
;                  | {<RLFAE> <RCFAEDS>}
;                  | {ifexp <RCFAEDS> <RCFAEDS> <RCFAEDS>}
;                  | {orop <RCFAEDS> <RCFAEDS>}

(define-type RCFAEDS
  [num (n number?)]
  [add (lhs RCFAEDS?) (rhs RCFAEDS?)]
  [sub (lhs RCFAEDS?) (rhs RCFAEDS?)]
  [mul (lhs RCFAEDS?) (rhs RCFAEDS?)]
  [eq (lhs RCFAEDS?) (rhs RCFAEDS?)]
  [id (name symbol?)]
  [fun(param symbol?)(body-expr RCFAEDS?)]
  [app (f RCFAEDS?) (a RCFAEDS?)]
  [ifexp (test-expr RCFAEDS?)
       (then-expr RCFAEDS?) (else-expr RCFAEDS?)]
  [orop (lhs RCFAEDS?) (rhs RCFAEDS?)])

(define-type RCFAEDS-Value
  [numV (n number?)]
  [closureV (param symbol?)
            (body RCFAEDS?)
            (ds DefrdSub?)]
  [exprV (expr RCFAEDS?) (ds DefrdSub?)
         (value (box/c (or/c false
                             RCFAEDS-Value?)))])


;DefrdSub
(define-type DefrdSub
    [mtSub]
    [aSub (name symbol?) (value RCFAEDS-Value?) (ds DefrdSub?)]
    [aRecSub (name symbol?)
             (value-box (box/c RCFAEDS-Value?))
             (ds DefrdSub?)])

; [contract] strict: RCFAEDS-Value -> RCFAEDS-Value
; [purpose] forcing program to work
(define (strict v)
  (type-case RCFAEDS-Value v
    [exprV (expr ds v-box)
           (if (not (unbox v-box))
               (local [(define v (strict (interp expr ds)))]
                 (begin (set-box! v-box v) v))
               (unbox v-box))]
    [else v]))

; [contract] num-op: (number number -> number) -> (RCFAEDS RCFAEDS -> RCFAEDS)
; [purpose] to make number operation abstrct
(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n (strict x)) (numV-n (strict y))))))
(define num+ (num-op +))
(define num- (num-op -))
(define num* (num-op *))

; [contract] interp: RCFAEDS DefrdSub -> RCFAEDS-Value
; [purpose] to get RCFAEDS value
; [test] tests are merged into run function
(define (interp rcfaeds ds)
  (type-case RCFAEDS rcfaeds
    [num (n) (numV n)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [mul (l r) (num* (interp l ds) (interp r ds))]
    [id (name) (lookup name ds)]
    [fun (param body-expr)
         (closureV param body-expr ds)]
    [app (f a)
         (if (and (and (and (fun? f) (fun? a)) (not (fun? (closureV-body (interp f ds))))) (is-not-in-ds (closureV-param (interp f ds)) ds))
             (local [(define value-holder (box (numV 198)))
                     (define ftn (interp f ds))
                     (define new-ds (aRecSub (closureV-param ftn)
                                             value-holder
                                             ds))]
               (begin
                 (set-box! value-holder (interp a new-ds))
                 (interp (closureV-body ftn) new-ds)))
             
             (local [(define ftn (interp f ds))]
                            (interp (closureV-body ftn)
                                         (aSub (closureV-param ftn)
                                                     (interp a ds)
                                                     (closureV-ds ftn)))))]
    [ifexp (test-expr then-expr else-expr)
         (if (interp test-expr ds)
             (interp then-expr ds)
             (interp else-expr ds))]
    [orop (l r)
          (or (interp l ds) (interp r ds))]
    [eq (l r) (equal? (interp l ds) (interp r ds))]))

; [contract] is-not-in-ds: id DefrdSub -> bool
; [purpose] to check wheter id is already in ds
(define (is-not-in-ds name ds)
  (type-case DefrdSub ds
    [mtSub () #t]
    [aSub (sub-name val rest-ds)
          (is-not-in-ds name rest-ds)]
    [aRecSub (sub-name val-box rest-ds)
             (if (symbol=? sub-name name)
                  #f
              (is-not-in-ds name rest-ds))]))

; [contract] lookup: symbol DefrdSub -> RCFAE-Value
; [purpose] to find the looking value
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

; [contract] parse: sexp -> RCFAEDS
; [purpose] to convert sexp to RCFAEDS
; [test] (test (parse '{{fun {x} {+ {+ x x} {+ x x}}} {- {+ 4 5} {+ 8 9}}} (app (fun 'x (add (add (id 'x) (id 'x)) (add (id 'x) (id 'x)))) (sub (add (num 4) (num 5)) (add (num 8) (num 9)))))
;   (test (parse '{with {fac {fun {n} {ifexp {= n 0} 1 {* n {fac {- n 1}}}}}} {fac 10}}) (app (fun 'fac (app (id 'fac) (num 10))) (fun 'n (ifexp (eq (id 'n) (num 0)) (num 1) (mul (id 'n) (app (id 'fac) (sub (id 'n) (num 1))))))))
(define (parse sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse l) (parse r))]
    [(list '- l r) (sub (parse l) (parse r))]
    [(list '* l r) (mul (parse l) (parse r))]
    [(list 'with (list i v) e) (app (fun i (parse e)) (parse v))]
    [(? symbol?) (id sexp)]
    [(list 'fun (list p) b) (fun p (parse b))]
    [(list f a) (app (parse f) (parse a))]
    [(list 'ifexp te th el) (ifexp (parse te) (parse th) (parse el))]
    [(list 'orop l r) (orop (parse l) (parse r))]
    [(list '= l r) (eq (parse l) (parse r))]
    [else (error 'parse "bad syntax: ~a" sexp)]))

(test (parse '{{fun {x} {+ {+ x x} {+ x x}}} {- {+ 4 5} {+ 8 9}}} ) (app (fun 'x (add (add (id 'x) (id 'x)) (add (id 'x) (id 'x)))) (sub (add (num 4) (num 5)) (add (num 8) (num 9)))))
(test (parse '{with {fac {fun {n} {ifexp {= n 0} 1 {* n {fac {- n 1}}}}}} {fac 10}}) (app (fun 'fac (app (id 'fac) (num 10))) (fun 'n (ifexp (eq (id 'n) (num 0)) (num 1) (mul (id 'n) (app (id 'fac) (sub (id 'n) (num 1))))))))


; [contract] run sexp -> RLFAE-Value
; [purpose] to run desired program
; [test] (test (run '{with {x 3} {+ x 9}}) (numV 12))
;        (test (run '{with {fac {fun {x} 2}} {with {fac {fun {n} {ifexp {= n 0} 1 {* n {fac {- n 1}}}}}} {fac 10}}}) (numV 20))
;        (test (run  '{with {fac {fun {n} {ifexp {= n 0} 1 {* n {fac {- n 1}}}}}} {fac 6}}) (numV 720))
;        (test (run '{with {fib {fun {n} {ifexp {orop {= n 0} {= n 1}} 1 {+{fib {- n 1}} {fib {- n 2}}}}}} {fib 10}}) (numV 89))
;        (test (run '{with {fac {fun {x} 2}} {with {fac {fun {n}{ifexp {= n 0}1{* n {fac {- n 1}}}}}} {fac 10}}}) (numV 20))
;        (test (run '{with {count {fun {n} {ifexp {= n 0} 0 {+ 1 {count {- n 1}}}}}}{count 8}}) (numV 8))
;        (test (run '{with {x 3} {with {fib {fun {n} {ifexp {orop {= n 0} {= n 1}} 1 {+ {fib {- n 1}} {fib {- n 2}}}}}} {fib 10}}}) (numV 89))

(define (run sexp)
  (interp (parse sexp) (mtSub)))


(test (run '{with {x 3} {+ x 9}}) (numV 12))
(test (run '{with {fac {fun {x} 2}} {with {fac {fun {n} {ifexp {= n 0} 1 {* n {fac {- n 1}}}}}} {fac 10}}}) (numV 20))
(test (run  '{with {fac {fun {n} {ifexp {= n 0} 1 {* n {fac {- n 1}}}}}} {fac 6}}) (numV 720))
(test (run '{with {fib {fun {n} {ifexp {orop {= n 0} {= n 1}} 1 {+{fib {- n 1}} {fib {- n 2}}}}}} {fib 10}}) (numV 89))
(test (run '{with {fac {fun {x} 2}} {with {fac {fun {n}{ifexp {= n 0}1{* n {fac {- n 1}}}}}} {fac 10}}}) (numV 20))
(test (run '{with {count {fun {n} {ifexp {= n 0} 0 {+ 1 {count {- n 1}}}}}}{count 8}}) (numV 8))
(test (run '{with {x 3} {with {fib {fun {n} {ifexp {orop {= n 0} {= n 1}} 1 {+ {fib {- n 1}} {fib {- n 2}}}}}} {fib 10}}}) (numV 89))