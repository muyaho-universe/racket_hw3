#lang plai

;<LFAE> :: =       <num>
;                  | {+ <LFAE> <LFAE>}
;                  | {- <LFAE> <LFAE>}
;                  | <id>
;                  | {fun {<id>} <LFAE>}
;                  | {<LFAE> <LFAE>}

;concrete to abstract
(define-type LFAE
  [num (n number?)]
  [add (lhs LFAE?) (rhs LFAE?)]
  [sub (lhs LFAE?) (rhs LFAE?)]
  [id (name symbol?)]
  [fun(param symbol?)(body-expr LFAE?)]
  [app (f LFAE?) (a LFAE?)])

; num-op: (number number -> number) -> (FWAE FWAE -> FWAE)
(define (num-op op)
     (lambda (x y)
          (num (op (num-n x) (num-n y)))))
(define num+ (num-op +))
(define num- (num-op -))


;Implementing LFAE
(define (interp lfae ds)
  (type-case LFAE lfae
    [num (n) (numV n)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [id (name) (lookup name ds)]
    [fun (param body-expr) (closureV param body-expr ds)]
    [app (f a) (local[(define ftn-v (strict(interp f ds (box #f))))
                      (difine arg-v (exprV a ds))]
                 (interp (closureV-body ftn-v)
                         (aSub (closureV-param ftn-v)
                               arg-v
                               (clousreV-ds ftn-v))))]))

;Implementing LFAE: LFAE Values
(define-type LFAE-Value
  [numV (n number?)]
  [closureV (param symbol?)
            (body LFAE?)
            (ds DefrdSub?)]
  [exprV (expr LFAE?) (ds DefrdSub?)
         (value (box/c (or/c false LFAE-Value?)))])

;strict: LFAE-Value -> LFAE-Value
(define (strict v)
  (type-case LFAE-Value v
    [exprV (expr ds v-box)
           (if (not (unbox v-box))
               (local [(define v (strict (interp expr ds)))]
                 (begin (set-box! v-box v)
                        v))
               (unbox v-box))]
    [else v]))