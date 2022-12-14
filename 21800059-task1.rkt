#lang plai

;<LFAE> :: =       <num>
;                  | {+ <LFAE> <LFAE>}
;                  | {- <LFAE> <LFAE>}
;                  | <id>
;                  | {fun {<id>} <LFAE>}
;                  | {<LFAE> <LFAE>}

(define-type LFAE
  [num (n number?)]
  [add (lhs LFAE?) (rhs LFAE?)]
  [sub (lhs LFAE?) (rhs LFAE?)]
  [id (name symbol?)]
  [fun(param symbol?)(body-expr LFAE?)]
  [app (f LFAE?) (a LFAE?)])

;Implementing LFAE: LFAE Values
(define-type LFAE-Value
  [numV (n number?)]
  [closureV (param symbol?)
            (body LFAE?)
            (ds DefrdSub?)]
  [exprV (expr LFAE?) (ds DefrdSub?)
         (value (box/c (or/c false LFAE-Value?)))])

;DefrdSub
(define-type DefrdSub
    [mtSub]
    [aSub (name symbol?) (value LFAE-Value?) (ds DefrdSub?)])

; [contract] strict: LFAE-Value -> LFAE-Value
; [purpose] forcing program to work
(define (strict v)
  (type-case LFAE-Value v
    [exprV (expr ds v-box)
           (if (not (unbox v-box))
               (local [(define v (strict (interp expr ds)))]
                 (begin (set-box! v-box v)
                        v))
               (unbox v-box))]
    [else v]))

; [contract] lookup: symbol DefrdSub -> symbol
; [purpose] to find the looking value
(define (lookup name ds)
      (type-case DefrdSub ds
            [mtSub       ()                  (error 'lookup "free identifier")]
            [aSub      (i v saved)      (if (symbol=? i name)
                                                                     v
                                                                     (lookup name saved))]))

; [contract] num-op: (number number -> number) -> (LFAE LFAE -> LFAE)
; [purpose] to make number operation abstrct
(define (num-op op x y)
    (numV (op (numV-n (strict x))
                        (numV-n (strict y)))))
(define (num+ x y) (num-op + x y))
(define (num- x y) (num-op - x y))

; [contract] parse: sexp -> LFAE
; [purpose] to convert sexp to LFAE
; [test] (test (parse x) (id 'x))
;   (test (parse '{{fun {x} {+x 2}} 3}) (app (fun 'x (app (id '+x) (num 2))) (num 3)))
(define (parse sexp)
   (match sexp
        [(? number?) (num sexp)]
        [(list '+ l r) (add (parse l) (parse r))]
        [(list '- l r) (sub (parse l) (parse r))]
        [(? symbol?) (id sexp)]
        [(list 'fun (list p) b) (fun p (parse b))]  ;; e.g., {fun {x} {+ x 1}}
        [(list f a) (app (parse f) (parse a))]
        [else  (error 'parse "bad syntax: ~a" sexp)]))

(test (parse 'x) (id 'x))
(test (parse '{{fun {x} {+x 2}} 3}) (app (fun 'x (app (id '+x) (num 2))) (num 3)))

; [contract] interp : LFAE DefrdSub -> LFAE-Value
; [purpose] to get LFAE value
; [test] (test (interp (parse '{{fun {x} {+ x 2}} 3}) (mtSub)) (numv 5))
;        (test (interp (parse '{{fun {x} 10} {+ 1 {fun {y} 2}}}) (mtSub)) (numV 10))
(define (interp lfae ds)
  (type-case LFAE lfae
     [num (n)      (numV n)]
     [add (l r)    (num+ (interp l ds) (interp r ds))]
     [sub (l r)    (num- (interp l ds) (interp r ds))]
     [id  (s)     (lookup s ds)]
     [fun (p b)  (closureV p b ds)]
     [app (f a)   (local [(define f-val (strict (interp f ds)))
                          (define a-val (exprV a ds (box #f)))]
                   (strict(interp (closureV-body f-val)
                           (aSub (closureV-param f-val)
                                 a-val
                                 (closureV-ds f-val)))))]))

(test (interp (parse '{{fun {x} {+ x 2}} 3}) (mtSub)) (numV 5))
(test (interp (parse '{{fun {x} 10} {+ 1 {fun {y} 2}}}) (mtSub)) (numV 10))