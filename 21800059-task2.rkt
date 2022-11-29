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
;                  | {eq <RCFAE> <RCFAE>}

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
    )

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

; [contract] is-in-list list value -> boolean
(define (is-in-list list value)
  (cond
    [(empty? list) false]
    [(list? (first list)) (is-in-list (first list) value)]
    [(equal? (first list) value) true]
    [else (is-in-list (rest list) value)]))

;[contract] is-recursion: sexp -> bool
;[purpose] to check wheter an RLFAE expression contains recursion
(define (is-recursion sexp)
  (match sexp
    [(list 'with (list i v) e) (if (is-recursion-in-v i  v 0)
                                   #t
                                   (if (equal? 'with (first e)) (is-recursion-e i e) #f))]
    [else #f])
  )
(define (is-recursion-e origin-i sexp)
  (match sexp
    [(list 'with (list i v) e) (if (and (not (equal? origin-i i)) (is-recursion-in-v i v 0))
                                   #t
                                   (if (equal? 'with (first e)) (is-recursion e) #f))]
    [else #f])
  )


;[contract] is-recursion: RLFAE n -> bool
(define (is-recursion-in-v i v n)
  (if (and (list? v) (not (empty? v)))
      (cond
         [(= n 0)
          (if (and (list? (first v)) (is-in-list (first v) 'ifexp))
              (is-recursion-in-v i (rest (first v)) 1)
              (if (list? (rest v)) (is-recursion-in-v i (rest v) 0) #f))]
         [(= n 1)
          (if (and (list? (first v)) (is-in-list (first v) i))
              #t
              (if (and (list? (rest v)) (is-in-list (rest v) i))
                  #t
                  #f))])
      #f))
(is-recursion '{with {x 3} {with {fib {fun {n} {ifexp {orop {= n 0} {= n 1}} 1 {+ {fib {- n 1}} {fib {- n 2}}}}}} {fib 10}}})   ; #t
(display "=========================\n")
(is-recursion '{with {fib {fun {x} 3}} {with {fib {fun {n} {ifexp {orop {= n 0} {= n 1}} 1 {+ {fib {- n 1}} {fib {- n 2}}}}}} {fib 10}}}) ; #f
(display "=========================\n")
(is-recursion '{with {sum {fun {x} 3}} {with {fib {fun {n} {ifexp {orop {= n 0} {= n 1}} 1 {+ {fib {- n 1}} {fib {- n 2}}}}}} {fib 10}}}) ; #t
(display "=========================\n")
(test (is-recursion '{with {fib {fun {n} {ifexp {orop {= n 0} {= n 1}} 1 {+ {fib {- n 1}} {fib {- n 2}}}}}} {fib 10}}) #t)
(test (is-recursion '{with {fac {fun {x} 1}} {with {fac {fun {n} {ifexp {= n 0} 1 {* n {fac {- n 1}}}}}} {fac 10}}}) #f)
(test (is-recursion '{with {fac {fun {n} {ifexp {= n 0} 1 {* n {fac {- n 1}}}}}} {fac 10}}) #t)
(test (is-recursion '{{fun {x} {+ 1 x}} 10}) #f)
(test (is-recursion '{with {x 3} {with {f {fun {y} {+ x y}}} {with {x 5} {f 4}}}}) #f)
(test (is-recursion '{with {x 3} {with {fib {fun {n} {ifexp {orop {= n 0} {= n 1}} 1 {+ {fib {- n 1}} {fib {- n 2}}}}}} {fib 10}}}) #t)
(test (is-recursion '{with {fac {fun {n} {ifexp {= n 0} 1 {* n {fac {- n 1}}}}}} {fac 10}}) #t)
(test (is-recursion '{{fun {x} {+ 1 x}} 10}) #f)
(test (is-recursion '{with {count {fun {n} {ifexp {= n 0} 0 {+ 1 {count {- n 1}}}}}} {count 8}}) #t)
(test (is-recursion '{{fun {x} {+ x x}} {+ 1 {{fun {y} 2} 1}}}) #f)
(test (is-recursion '{{fun {x} {+ {+ x x} {+ x x}}} {- {+ 4 5} {+ 8 9}}}) #f)
(display "=========================\n")

;[contract] desugar sexp -> sexp
;[purpose] to check wheter an RLFAE expression contains recursion
(define (desugar sexp)
  (match sexp
    [(list 'with (list i v) e)
     (if (is-recursion-in-v i  v 0)
         (make-it-work (list 'with (list i v) e))
         (if (is-recursion-e i e) (make-it-work e) sexp))
     ]
    [else sexp])
  )

(define (make-it-work sexp)
  (match sexp
    [(list 'with (list i v) e)
     (list 'with (list 'mk-rec
                       (list 'fun '(body-proc)
                             (list 'with
                                   (list 'fX
                                         (list 'fun '(fY)
                                               (list 'with
                                                     (list 'f
                                                           (list 'fun '(x)
                                                                 (list (list 'fY 'fY) 'x)))
                                                     (list 'body-proc 'f)))) (list 'fX 'fX))))
           (list 'with (list i (list 'mk-rec (list 'fun (list i)  v))) e))]
    [else sexp])
  )
(display "=========desugar!!===========\n")
(desugar '{with {x 3} {with {fib {fun {n} {ifexp {orop {= n 0} {= n 1}} 1 {+ {fib {- n 1}} {fib {- n 2}}}}}} {fib 10}}})
(display "=========================\n")
; [contract] lookup: symbol DefrdSub -> RCFAE-Value
(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable")]
    [aSub (sub-name val rest-ds)
          (if (symbol=? sub-name name)
              val
              (lookup name rest-ds))]))

; [contract] parse: sexp -> RLFAE
(define (parse sexp)
  (match sexp
    [(? number?) (num sexp)]
    [(list '+ l r) (add (parse l) (parse r))]
    [(list '- l r) (sub (parse l) (parse r))]
    [(list '* l r) (mul (parse l) (parse r))]
    [(list '= l r) (eq (parse l) (parse r))]
    [(list 'with (list i v) e) (app (fun i (parse e)) (parse v))]
    [(? symbol?) (id sexp)]
    [(list 'fun (list p) b) (fun p (parse b))]
    [(list f a) (app (parse f) (parse a))]
    [(list 'ifexp te th el) (ifexp (parse te) (parse th) (parse el))]
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
    [orop (l r)
          (or (interp l ds) (interp r ds))]))


(define (run sexp)
     (if (equal? (is-recursion sexp) #t)
         (interp (parse (desugar sexp)) (mtSub))
         (interp (parse sexp) (mtSub))))


; language definition end point
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

;(parse '{with {fib {fun {n}
;                        {ifexp {orop {= n 0} {= n 1}}
;                               1
;                               {+{fib {- n 1}} {fib {- n 2}}}}}}
;           {fib 3}});

;(parse '{with {fac {fun {x} 1}} {with {fac {fun {n}
;                                                 {ifexp {= n 0}
;                                                     1
;                                                     {* n {fac {- n 1}}}}}} {fac 10}}})

;(parse '{with {fac {fun {n}
 ;                       {ifexp {= n 0}
 ;                              1
 ;                              {* n {fac {- n 1}}}}}} {fac 10}})

;(run '{with {fac {fun {x} 1}} {with {fac {fun {n}
 ;                                                {ifexp {= n 0}
;                                                     1
;                                                     {* n {fac {- n 1}}}}}} {fac 4}}})
(display "===============\n")

;'{with {mk-rec {fun {body-proc}
;                          {with {fX {fun {fY}
;                                         {with {f {fun {x}
;                                                       {{fY fY} x}}}
;                                               {body-proc f}}}}
;                                {fX fX}}}}
;             {with {fac {mk-rec
;                         {fun {fac} ; Exactly like original fac
;                              {fun {n}
;                                   {ifexp {= n 0}
;                                          1
;                                          {* n {fac {- n 1}}}}}}}}
;                   {fac 10}}}
;(run'{with {mk-rec {fun {body-proc}
;                          {with {fX {fun {fY}
;                                         {with {f {fun {x}
;                                                       {{fY fY} x}}}
;                                               {body-proc f}}}}
;                                {fX fX}}}}
;             {with {fac {mk-rec
;                         {fun {fac} ; Exactly like original fac
;                              {fun {n}
;                                   {ifexp {= n 0}
;                                          1
;                                          {* n {fac {- n 1}}}}}}}}
;                   {fac 10}}})

(display "===============\n")
(display "This is parsing of given code\n")
(parse '{with {mk-rec {fun {body-proc}
                          {with {fX {fun {fY}
                                         {with {f {fun {x}
                                                       {{fY fY} x}}}
                                               {body-proc f}}}}
                                {fX fX}}}}
             {with {fac {mk-rec
                         {fun {fac} ; Exactly like original fac
                              {fun {n}
                                   {ifexp {= n 0}
                                          1
                                          {* n {fac {- n 1}}}}}}}}
                   {fac 5}}})

(display "===============\n")
(display "This is parsing of desugar\n")
(parse (desugar '{with {fac {fun {n}
                        {ifexp {= n 0}
                               1
                               {* n {fac {- n 1}}}}}} {fac 5}}))
(display "===============\n")
'{with {mk-rec {fun {body-proc}
                          {with {fX {fun {fY}
                                         {with {f {fun {x}
                                                       {{fY fY} x}}}
                                               {body-proc f}}}}
                                {fX fX}}}}
             {with {fac {mk-rec
                         {fun {fac} ; Exactly like original fac
                              {fun {n}
                                   {ifexp {= n 0}
                                          1
                                          {* n {fac {- n 1}}}}}}}}
                   {fac 5}}}
(display "========last=======\n")
;(run '{with {x 3} {with {fib {fun {n} {ifexp {orop {= n 0} {= n 1}} 1 {+ {fib {- n 1}} {fib {- n 2}}}}}} {fib 10}}})
(run '{with {fib {fun {x} 3}} {with {fib {fun {n} {ifexp {orop {= n 0} {= n 1}} 1 {+ {fib {- n 1}} {fib {- n 2}}}}}} {fib 4}}})
(display "=========================\n")

(desugar '{with {fac {fun {n}
                       {ifexp {= n 0}
                            1
                            {* n {fac {- n 1}}}}}}
          {fac 10}})
(display "=========================\n")
(is-recursion '{with {x 1} {+ x 2}})
(display "=========================\n")
(is-recursion '{with {fac {fun {x} 1}} {with {fac {fun {n}
                                                 {ifexp {= n 0}
                                                     1
                                                     {* n {fac {- n 1}}}}}} {fac 10}}})
(display "=========================\n")
(if (is-recursion '{with {fib {fun {n}
                        {ifexp {orop {= n 0} {= n 1}}
                               1
                               {+{fib {- n 1}} {fib {- n 2}}}}}}
           {fib 3}}) (desugar '{with {fib {fun {n}
                        {ifexp {orop {= n 0} {= n 1}}
                               1
                               {+{fib {- n 1}} {fib {- n 2}}}}}}
           {fib 3}}) (display "okok"))
(display "=========================\n")
(is-recursion '{with {fib {fun {x} x}} {with {fib {fun {n}
                        {ifexp {orop {= n 0} {= n 1}}
                               1
                               {+{fib {- n 1}} {fib {- n 2}}}}}}
           {fib 5}}})
(display "=========================\n")

(run  '{with {fac {fun {n} {ifexp {= n 0} 1 {* n {fac {- n 1}}}}}} {fac 6}})
(run '{with {fib {fun {n} {ifexp {orop {= n 0} {= n 1}} 1 {+{fib {- n 1}} {fib {- n 2}}}}}} {fib 10}})
(run '{with {fac {fun {x} 2}} {with {fac {fun {n}{ifexp {= n 0}1{* n {fac {- n 1}}}}}} {fac 10}}})

(run '{with {count {fun {n} {ifexp {= n 0} 0 {+ 1 {count {- n 1}}}}}}{count 8}})



(run '{with {x 3} {with {fib {fun {n} {ifexp {orop {= n 0} {= n 1}} 1 {+ {fib {- n 1}} {fib {- n 2}}}}}} {fib 10}}})