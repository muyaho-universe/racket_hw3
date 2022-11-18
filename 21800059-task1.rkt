#lang plai

;<LFAE> :: = <num>
;                  | {+ <LFAE> <LFAE>}
;                  | {- <LFAE> <LFAE>}
;                  | <id>
;                  | {fun {<id>} <LFAE>}
;                  | {<LFAE> <LFAE>}

(define (interp lfae ds)
  (type-case LFAE lfae
    [num (n) (numV n)]
    [add (l r) (num+ (interp l ds) (interp r ds))]
    [sub (l r) (num- (interp l ds) (interp r ds))]
    [id (name) (lookup name ds)]
    [fun (param body-expr) (closureV param body-expr ds)]
    [app (f a) (local[(define ftn-v (interp f ds))
                      (difine arg-v (interp a ds))]
                 (interp (closureV-body ftn-v)
                         (aSub (closureV-param ftn-v)
                               arg-v
                               (clousreV-ds ftn-v))))]))