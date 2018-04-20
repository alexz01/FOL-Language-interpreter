rule(s,[np,vp]).
rule(vp,[tv,np]).
rule(vp,[sv,s]).
rule(vp,[vp,pp]).
rule(vp,[iv]).

rule(np,[dt,n]).
rule(np,[pn]).
rule(np,[prp]).
rule(n,[adj,n]).
rule(n,[n,pp]).
rule(pp,[p,np]).

lex(p,in).
lex(p,near).

lex(pn,tom).
lex(pn,sue).
lex(prp,you).

lex(adj,big).

lex(dt,the).

lex(tv,saw).
lex(iv,broke).
lex(sv,claimed).
lex(sv,denied).
lex(sv,said).

lex(n,cat).
lex(n,hat).
lex(n,kitchen).
lex(n,gate).
lex(n,attack).
lex(n,captain).
lex(n,sergeant).
lex(n,antenna).
lex(n,hangar).


large([the,captain,said,you,claimed,the,sergeant,denied,the,antenna,in,the,hangar,broke,in,the,attack,near,the,gate]).



% = SR =================================================

sr_parse(Sentence):-
        srparse([],Sentence).
 
srparse([_],[]).
 
srparse([Y,X|MoreStack],Words):-
       rule(LHS,[X,Y]),
       srparse([LHS|MoreStack],Words).

srparse([X|MoreStack],Words):-
       rule(LHS,[X]),
       srparse([LHS|MoreStack],Words).

srparse(Stack,[Word|Words]):-
        lex(X,Word),
        srparse([X|Stack],Words).


% =SR P=================================================

sr_parse_tree(Sentence,Parse):-
        srparse([],Sentence,[],Parse),
        prettyprint(Parse).
 
srparse([_],[],[X],X).
 
srparse([Y,X|MoreStack],Words,[Z,W|ListNodes],Parse):-
       rule(LHS,[X,Y]),
       Node =.. [LHS,W,Z],
       srparse([LHS|MoreStack],Words,[Node|ListNodes],Parse).

srparse([X|MoreStack],Words,[Y|ListNodes],Parse):-
       rule(LHS,[X]),
       Node =.. [LHS,Y],
       srparse([LHS|MoreStack],Words,[Node|ListNodes],Parse).

srparse(Stack,[Word|Words],ListNodes,Parse):-
        lex(X,Word),
        Node =.. [X,Word],
        srparse([X|Stack],Words,[Node|ListNodes],Parse).



prettyprint(E) :- 
 prettyprint2(E, 0).

prettyprint2(A, Indent) :-
 A =.. [Type, Subtree1, Subtree2],
  !,
  nl, tab(Indent), write(Type),
   Indent2 is Indent + 3,
   prettyprint2(Subtree1, Indent2),
   prettyprint2(Subtree2, Indent2).

prettyprint2(A, Indent) :-
   A =.. [Type, Subtree],
   !,
    nl, tab(Indent), write(Type),
    Indent2 is Indent + 3,
    prettyprint2(Subtree, Indent2).

prettyprint2(A, Indent) :-
    !,
    nl, tab(Indent), write([A]).


% = LC =================================================

lc_parse(String) :-
    leftcorner_recognize(s,String,[]).

leftcorner_recognize(Cat,[Word|StringIn],StringOut) :-
    lex(WCat,Word),
    complete(Cat,WCat,StringIn,StringOut).

complete(Cat,Cat,String,String).

complete(Cat,SubCat,StringIn,StringOut) :-
    rule(LHS,[SubCat|Cats]),
    matches(Cats,StringIn,String1),
    complete(Cat,LHS,String1,StringOut).

matches([],String,String).
matches([Cat|Cats],StringIn,StringOut) :-
    leftcorner_recognize(Cat,StringIn,String1),
    matches(Cats,String1,StringOut).





% =STATS=================================================

stat_inf(S,sr,Total):- 
    statistics(inferences,I1),
    findall(S2, (S2=S, sr_parse(S)),_),
    statistics(inferences,I2), 
    Total is I2 - I1.

stat_inf(S,lc,Total):- 
    statistics(inferences,I1),
    findall(S2, (S2=S, lc_parse(S)),_),
    statistics(inferences,I2), 
    Total is I2 - I1.
 
stats_t(S,sr,Total):- 
    statistics(cputime,I1),
    findall(S2, (S2=S, sr_parse(S)),_),
    statistics(cputime,I2), 
    Total is I2 - I1.

stats_t(S,lc,Total):- 
    statistics(cputime,I1),
    findall(S2, (S2=S, lc_parse(S)),_),
    statistics(cputime,I2), 
    Total is I2 - I1.
 

