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



% = CHART BOTTOM-UP PASSIVE =======================================


chart_recognize_bottomup(Input) :-
        cleanup,
        initialize_chart(Input, 0),
        process_chart_bottomup,
        length(Input, N),
        arc(0, N, s).
 

cleanup :-  
        retractall(scan(_,_,_)),
        retractall(arc(_,_,_)).
 

initialize_chart([], _).
initialize_chart([Word|Input], From) :-
        To is From + 1,
        assertz(scan(From, To, Word)),
        initialize_chart(Input, To).
 

process_chart_bottomup :-
         doall(
              (scan(From, To, Word),
               lex(Cat,Word),
               add_arc(arc(From, To, Cat)))
          ).
 

add_arc(Arc) :-
        \+ Arc,
        assert(Arc),
        new_arcs(Arc).
 

new_arcs(arc(J, K, Cat)) :-
         doall(
               (rule(LHS,RHS),
               append(Before, [Cat], RHS),
               path(I, J, Before),
               add_arc(arc(I, K, LHS)))
                ).
 

path(I, I, []).
path(I, K, [Cat|Cats]) :-
        arc(I, J, Cat),
        J =< K,
        path(J, K, Cats).
 
%%% doall(+goal)

doall(Goal) :-  
        Goal, fail.
doall(_) :- true.



% =STATS=================================================

stat_inf(S,buc,Total):- 
    statistics(inferences,I1),
    chart_recognize_bottomup(S),
    statistics(inferences,I2), 
    Total is I2 - I1.

stats_t(S,buc,Total):- 
    statistics(cputime,I1),
    chart_recognize_bottomup(S),
    statistics(cputime,I2), 
    Total is I2 - I1.
 

