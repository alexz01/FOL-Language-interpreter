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



% = CHART TOP-DOWN ACTIVE  =======================================

:- dynamic scan/3, arc/5.


active_chart_recognize(Input) :-
	cleanup,
	initialize_chart_topdown(Input, 0),
	initialize_agenda_topdown(Agenda),
	process_agenda(Agenda),
	length(Input, N),
	arc(0, N, s, _, []).

cleanup :- 
	retractall(scan(_,_,_)),
	retractall(arc(_,_,_,_,_)).



initialize_chart_topdown([], _).
initialize_chart_topdown([Word|Input], From) :-
	To is From + 1,
	assert(scan(From, To, Word)),
	doall(
	     (lex(Cat,Word), assert(arc(From,To,Cat,[Word],[]))
             )
	),
	initialize_chart_topdown(Input, To).



initialize_agenda_topdown(Agenda) :-
	findall(arc(0, 0, s, [], RHS), rule(s,RHS), Agenda).



process_agenda([]).
process_agenda([Arc|Agenda]) :-
	\+ Arc,!,
	assert(Arc),
	make_new_arcs_topdown(Arc, NewArcs),
	append(NewArcs, Agenda, NewAgenda),
	process_agenda(NewAgenda).

process_agenda([_|Agenda]) :-
        process_agenda(Agenda).


make_new_arcs_topdown(Arc, NewArcs) :-
	Arc = arc(_,_,_,_,[_|_]),
	apply_fundamental_rule(Arc, NewArcs1),
	predict_new_arcs_topdown(Arc, NewArcs2),
	append(NewArcs1,NewArcs2,NewArcs).


make_new_arcs_topdown(Arc, NewArcs) :-
	Arc = arc(_,_,_,_,[]),
	apply_fundamental_rule(Arc, NewArcs).


apply_fundamental_rule(arc(I, J, Cat, Done, [SubCat|SubCats]), NewArcs) :-
	findall(arc(I, K, Cat, [SubCat|Done], SubCats),
	        arc(J, K, SubCat, _, []),
	        NewArcs
	       ).	

apply_fundamental_rule(arc(J, K, Cat, _, []), NewArcs) :-
	findall(arc(I, K, SuperCat, [Cat|Done], Cats),
	        arc(I, J, SuperCat, Done, [Cat|Cats]),
	        NewArcs
	    ).

predict_new_arcs_topdown(arc(_, J, _, _, [ToFindCat|_]), NewArcs) :-
	findall(arc(J, J, ToFindCat, [], RHS),
	        rule(ToFindCat,RHS),
	        NewArcs
	    ).


doall(Goal) :-  
        Goal, fail.
doall(_) :- true.



% =STATS=================================================

stat_inf(S,tdc,Total):- 
    statistics(inferences,I1),
    active_chart_recognize(S),
    statistics(inferences,I2), 
    Total is I2 - I1.

stats_t(S,tdc,Total):- 
    statistics(cputime,I1),
    active_chart_recognize(S),
    statistics(cputime,I2), 
    Total is I2 - I1.
 

