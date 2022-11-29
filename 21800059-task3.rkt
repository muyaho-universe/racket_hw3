#lang plai

;<RCFAEDS> ::= <num>
;                  | {+ <RLFAE> <RLFAE>}
;                  | {- <RLFAE> <RLFAE>}
;                  | {* <RLFAE> <RLFAE>}
;                  | {= <RLFAE> <RLFAE>}
;                  | <id>
;                  | {fun {<id>} <RLFAE>}
;                  | {<RLFAE> <RLFAE>}
;                  | {ifexp <RCFAE> <RCFAE> <RCFAE>}
;                  | {orop <RCFAE> <RCFAE>}

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

; [contract] strict:
(define (strict v)
  (type-case RCFAEDS-Value v
    [exprV (expr ds v-box)
           (if (not (unbox v-box))
               (local [(define v (strict (interp expr ds)))]
                 (begin (set-box! v-box v) v))
               (unbox v-box))]
    [else v]))

; [contract] num-op: (number number -> number) -> (FWAE FWAE -> FWAE)
(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n (strict x)) (numV-n (strict y))))))
(define num+ (num-op +))
(define num- (num-op -))
(define num* (num-op *))

; [contract] RCFAE-Value -> boolean
(define (numzero? n)
  (zero? (numV-n n)))

; [contract] interp: RCFAE DefrdSub -> RCFAE-Value
(define (interp rcfaeds ds)
  (type-case RCFAEDS rcfaeds
    [num (n) (numV n)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [mul (l r) (num* (interp l ds) (interp r ds))]
    [id (name) (lookup name ds)]
    [fun (param body-expr) (closureV param body-expr ds)]
    [app (f a)
         (display "========app=========\n")
         (display "f: ")
         (display f)
         (display "\n")
         (display "a: ")
         (display a)
         (display "\n")
             (local [(define ftn (interp f ds))]
                            (interp (closureV-body ftn)
                                         (aSub (closureV-param ftn)
                                                     (interp a ds)
                                                     (closureV-ds ftn))))]
    [ifexp (test-expr then-expr else-expr)
         (if (interp test-expr ds)
             (interp then-expr ds)
             (interp else-expr ds))]
    [orop (l r)
          (or (interp l ds) (interp r ds))]
    [eq (l r) (equal? (interp l ds) (interp r ds))]))

; [contract] lookip: symbol DefrdSub -> RCFAE-Value
(define (lookup name ds)
  (display "========look up======\n")
  (display "name: ")
  (display name)
  (display "\n")
  (display "ds: ")
  (display ds)
  (display "\n")
  (display "=====================\n")
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name val rest-ds)
          (display "sub-name: ")
          (display sub-name)
          (display "\n")
          (display "val: ")
          (display val)
          (display "\n")
          (display "rest-ds: ")
          (display rest-ds)
          (display "\n")
          (if (symbol=? sub-name name)
              val
              (lookup name rest-ds))]
    [aRecSub (sub-name val-box rest-ds)
             (if (symbol=? sub-name name)
                 (unbox val-box)
                 (lookup name rest-ds))]))

; [contract] parse: sexp -> RCFAE
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

(define (run sexp)
  (interp (parse sexp) (mtSub)))


(parse '{with {fac {fun {n}
                       {ifexp n
                            1
                            {* n {fac {- n 1}}}}}}
          {fac 10}})
(parse '{with {w {fun {n} 2}} {with {w {fun {x} {ifexp {= x 0} 1 {* 8 {w {- x 1}}}}}} {w 6}}})
(run '{with {w {fun {n} 2}} {with {w {fun {x} {ifexp {= x 0} 1 {* 8 {w {- x 1}}}}}} {w 6}}} )
;(run '{with {fac {fun {n} {ifexp n 1 {* n {fac {- n 1}}}}}} {fac 10}})

;(run '{with {count {fun {n} {ifexp n 0 {+ 1 {count {- n 1}}}}}} {count 8}} )