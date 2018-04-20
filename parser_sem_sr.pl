% ==================================
% Phrase Structure Rules 
% ==================================

rule(s(Y),[np(X^Y),vp(X)]).                

rule(vp(X^W),[tv(X^Y),np(Y^W)]).
rule(vp(X),[iv(X)]).

rule(np(Y),[dt(X^Y),n(X)]).
rule(np(X),[pn(X)]).

rule(n(Y),[adj(X^Y),n(X)]).

rule(n(X^Z),[n(X^Y),pp((X^Y)^Z)]).
rule(pp(Z),[p(X^Y^Z),np(X^Y)]).

% ==================================
% Lexicon
% ==================================

lex(pn((tom^X)^X),tom).
lex(pn((sue^X)^X),sue).

lex(n(X^bus(X)),bus).
lex(n(X^weapon(X)),weapon).
lex(n(X^passenger(X)),passenger).
lex(n(X^man(X)),man).

lex(p((Y^in(X,Y))^Q^(X^P)^and(P,Q)),in).
lex(p((Y^on(X,Y))^Q^(X^P)^and(P,Q)),on).

lex(adj((X^P)^X^and(P,big(X))),yellow).
lex(adj((X^P)^X^and(P,old(X))),old).
lex(adj((X^P)^X^and(P,illegal(X))),illegal).

lex(dt((X^P)^(X^Q)^exists(X,(and(P,Q)))),a).
lex(dt((X^P)^(X^Q)^exists(X,(and(P,Q)))),an).
lex(dt((X^P)^(X^Q)^the(X,(and(P,Q)))),the).
lex(dt((X^P)^(X^Q)^exists(X,(and(P,Q)))),some).
lex(dt((X^P)^(X^Q)^forall(X,(imp(P,Q)))),each).
lex(dt((X^P)^(X^Q)^forall(X,(imp(P,Q)))),every).

lex(iv(X^sneezed(X)),sneezed).
lex(tv(X^Y^saw(X,Y)),saw).
lex(tv(X^Y^have(X,Y)),had).

% Execution example:
% sr_parse([every,passenger,on,the,bus,had,an,illegal,weapon]).


% =======================================
% Example: Shift-Reduce Parse 
% =======================================

sr_parse(Sentence):-
        srparse([],Sentence).
 
srparse([X],[]):- 
  numbervars(X,0,_),
  write(X).

srparse([Y,X|MoreStack],Words):-
       rule(LHS,[X,Y]),
       srparse([LHS|MoreStack],Words).

srparse([X|MoreStack],Words):-
       rule(LHS,[X]),
       srparse([LHS|MoreStack],Words).

srparse(Stack,[Word|Words]):-
        lex(X,Word),
        srparse([X|Stack],Words).


