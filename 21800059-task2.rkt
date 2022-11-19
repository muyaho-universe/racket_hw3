#lang plai

;<RLFAE> :: =       <num>
;                  | {+ <RLFAE> <RLFAE>}
;                  | {- <RLFAE> <RLFAE>}
;                  | <id>
;                  | {fun {<id>} <RLFAE>}
;                  | {<RLFAE> <RLFAE>}
;                  | {ifexp <RCFAE> <RCFAE> <RCFAE>}
;                  | {rec {<id> <RCFAE>} <RCFAE>}


  