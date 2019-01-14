
% ===========================================================
% Main loop:
% 1. Repeat "input-response" cycle until input starts with "bye"
%    Each "input-response" cycle consists of:
%               1.1 Reading an input string and convert it to a tokenized list
%               1.2 Processing tokenized list
% ===========================================================

chat:-
 repeat,
   readinput(Input), %format('~a ~a',['input='| Input]), nl,
   process(Input),
  (Input = [bye| _] ),!.
  

% ===========================================================
% Read input:
% 1. Read char string from keyboard. 
% 2. Convert char string to atom char list.
% 3. Convert char list to lower case.
% 4. Tokenize (based on spaces).
% ===========================================================

readinput(TokenList):-
   read_line_to_codes(user_input,InputString),
   string_to_atom(InputString,CharList),
   string_lower(CharList,LoweredCharList),
   tokenize_atom(LoweredCharList,TokenList).


% ===========================================================
%  Process tokenized input
% 1. Parse morphology and syntax, to obtain semantic representation
% 2. Evaluate input in the model
% If input starts with "bye" terminate.
% ===========================================================

process(Input):-
        parse(Input,SemanticRepresentation),
        modelchecker(SemanticRepresentation,Evaluation),
        respond(Evaluation),!,
        nl,nl.
        
process([bye|_]):-
   write('> bye!').


% ===================	========================================
%  Parse:
% 1. Morphologically parse each token and tag it.
% 2. Add semantic representation to each tagged token
% 3. Obtain FOL representation for input sentence
% ===========================================================

%parse(Input, SemanticRepresentation):-
% ...
parse(Sentence, SemanticRepresentation):-
        srparse([],Sentence, SemanticRepresentation).

srparse([X],[],X). %:- numbervars(X,0,_).
	
srparse([Y,X|MoreStack],Words,SemanticRepresentation):-
       rule(LHS,[X,Y]),
       srparse([LHS|MoreStack],Words, SemanticRepresentation).

srparse([X|MoreStack],Words, SemanticRepresentation):-
       rule(LHS,[X]),
       srparse([LHS|MoreStack],Words, SemanticRepresentation).

srparse(Stack,[Word|Words], SemanticRepresentation):-
        lex(X,Word),
        srparse([X|Stack],Words, SemanticRepresentation).


% ===========================================================
% Grammar
% 1. List of lemmas
% 2. Lexical items
% 3. Phrasal rules
% ===========================================================

% --------------------------------------------------------------------
% Lemmas are uninflected, except for irregular inflection
% lemma(+Lemma,+Category)
% --------------------------------------------------------------------
lemma(a,dtexists).
lemma(all,dtforall).
lemma(almond, adj).
lemma(almond, n).
lemma(an,dtexists).
lemma(are, be).
lemma(banana, n).
lemma(belong,tv).
lemma(blue,adj).
lemma(bottom, adj).
lemma(bowl, n).
lemma(box,n).
lemma(contain, ppred).
lemma(contain,tv).
lemma(container, n).
lemma(did, aux).
lemma(does, aux).
lemma(drank, tv).
lemma(drink, tv).
lemma(each,dtforall).
lemma(eat,tv).
lemma(egg,n).
lemma(empty, adj).
lemma(every,dtforall).
lemma(freezer,n).
lemma(fridge, n).
lemma(green,adj).
lemma(ham,n).
lemma(has,tv).
lemma(in,p).
lemma(inside,p).
lemma(is,be).
lemma(meat, n).
lemma(mia,pn).
lemma(middle, adj ).
lemma(milk, n).
lemma(no,dtnot).
lemma(not, dtnot).
lemma(of,p).
lemma(on,vacp).   
lemma(popsicle, n).
lemma(red,adj).
lemma(sam, pn).
lemma(sandwich,n).
lemma(saw,tv).
lemma(see,tv).
lemma(shelf, n).
lemma(sneeze,iv).
lemma(some,dtexists).
lemma(sue,pn).
lemma(that,rel).
lemma(the,dt).
lemma(there,aux).
lemma(to,aux).
lemma(to,vacp).
lemma(tom,pn).
lemma(top, adj).
lemma(two,dt).
lemma(under,p).
lemma(was,be).
lemma(watermelon, n).
lemma(what,whthing).
lemma(which, whthing).
lemma(white,adj).
lemma(who, whperson).
lemma(yellow,adj).

% --------------------------------------------------------------------
% Constructing lexical items:
% word = lemma + suffix (for "suffix" of size 0 or bigger)
% --------------------------------------------------------------------



lex(pn((Name^X)^X),Name):-
        lemma(Name, pn).
                       
lex(dt((X^P)^(X^Q)^forall(X,imp(P,Q))),Lemma):-
        lemma(Lemma,dtforall).

lex(dt((X^P)^(X^Q)^exists(X,and(P,Q))),Lemma):-
		lemma(Lemma,dtexists).
		
lex(aux,Word):- lemma(Word,aux).

lex(rel,Word):- lemma(Word,rel).

lex(be,Word):- lemma(Word,be).

lex(dt((X^P)^(X^Q)^R),Lemma):-
		lemma(Lemma,dt),
		R=..[Lemma,X,and(P,Q)].
		
lex(dt((X^P)^(X^Q)^not(exists(X,and(P,Q)))),Lemma):-
		lemma(Lemma,dtnot).

lex(n(X^P),Word):-
        lemma(Word,n), P=.. [Word,X];
		stem_suffix(Word,Lemma), lemma(Lemma,n), P=.. [Lemma,X].
		
lex(iv(X^P,[]),Word):-
		lemma(Word,iv) -> P=.. [Word,X];
		stem_suffix(Word,Lemma), lemma(Lemma,iv), P=.. [Lemma,X].
                   
lex(tv(X^Y^P,[]),Word):-
        lemma(Word,tv) -> P=.. [Word,X,Y];
        stem_suffix(Word,Lemma), lemma(Lemma,tv), P=.. [Lemma,X,Y].

lex(adj((X^P)^X^and(P, Q)),Lemma):-
		lemma(Lemma,adj), Q=.. [Lemma,X].

lex(p((Y^in(X,Y))^Q^(X^P)^and(P,Q)),in).		
lex(p((Y^R)^Q^(X^P)^and(P, Q)), Lemma):-
		lemma(Lemma,p), R=.. [Lemma,X,Y].

lex(whpr((X^P)^q(X,person(X),P)),WH):- lemma(WH,whperson).
lex(whpr((X^P)^q(X,thing(X),P)),WH):- lemma(WH,whthing).
		
% ...

% --------------------------------------------------------------------
% Suffix types : get Lemma from lemma predicate after removing suffix
% --------------------------------------------------------------------

% ...
suffix(es).
suffix(s).
suffix(ed).
suffix(ing).

stem_suffix(Word,Lemma):-
                             suffix(X),
                             atom_concat(Lemma_frag,X,Word),
                             atom_length(Lemma_frag,Len),
                             lemma(Lemma,_),
                             sub_atom(Lemma,0,Len,_,Lemma_frag).

% --------------------------------------------------------------------
% Phrasal rules           |used for Beta reduction
% rule(+LHS,+ListOfRHS)   |see syn-sem2 & syn-sem3
% --------------------------------------------------------------------

rule(np(X),[pn(X)]).
rule(np((X^P)^exists(X,and(Q,P))),[n(X^Q)]).
rule(np(X),[prp(X)]).
rule(np(Y),[dt(X^Y),n(X)]).
rule(n(X^K),[n(X^Y),pp((X^Y)^K)]).
rule(n(X),[adj(Y^X),n(Y)]).
rule(pp(K),[p(X^Y^K),np(X^Y)]).
rule(ynq(Y), [be, aux, np(X^Y), ppred(X)]).
rule(iv(X^P,[Y]),[tv(X^Y^P,[])]).
rule(tv(X^Y^P,[]),[tv(Y^P,[X])]).
rule(rc(X,[]),[rel,s(X,[])] ).
rule(rc(X,[Y]),[rel,s(X,[Y])] ).
rule(vp(X^K,[]),[tv(X^Y,[]),np(Y^K)]).
rule(vp(X,WH),[iv(X,WH)]).
rule(s(Y,WH),[np(X^Y),vp(X,WH)]).
rule(vp(K,[WH]),[tv(Y,[WH]),np(Y^K)]).
rule(s(X,[WH]),[vp(X,[WH])]).
rule(Y,[whpr(X^Y),vp(X,[])]).
rule(ynq(Y),[aux, np(X^Y),vp(X,[])]).
rule(Z,[whpr((X^Y)^Z), inv_s(Y,[X])]).
rule(inv_s(Y,[WH]),[aux, np(X^Y),vp(X,[WH])]).
rule(n(X^and(Y,Z)),[n(X^Y),rc(X^Z,[])]).
rule(n(X^and(Y,Z)),[n(X^Y),rc(Z,[X])]).


% ===========================================================
%  Modelchecker:
%  1. If input is a declarative, check if true
%  2. If input is a yes-no question, check if true
%  3. If input is a content question, find answer
% ===========================================================

modelchecker(SemanticRepresentation,Evaluation):-
	sat([],SemanticRepresentation,Evaluation).
	
%=============================================================
% Model 
%=============================================================

model([a,b,c,d,e,f,g,h,i,k,l,n,r],
			[[box,[a,b,c]],[bowl,[d]],[white,[b,d]],[blue,[a,b]],[green,[c]],[yellow,[n]],[ham,[e,f]],[meat,[e,f]],[freezer,[g,h]],[sue,[i]],[egg,[k,l]],[contain,[[b,e],[a,f],[b,g],[a,k],[a,l],[c,l]]],[belong,[b,i]],[put,[d,n]]]).

model([a,b,c,d,e,f,g,h,i], [[blue,[a]], [ container,[a,f]], [top,[b]], [shelf,[b,g]], [on,[[a,b],[f,g]]], [contain,[[a,b],[c,d],[b,e],[f,g]]], [sandwich,[b,c]], [ham,[d]], [chicken,[e]], [meat,[d,e]], [white,[f]], [bottom,[g]], [banana,[h]] ]).

model([a,b,c,d,e,f,g], [ [yellow,[a]], [bowl,[a]], [middle,[b]],[egg,[c,d]], [contain,[[a,c],[a,d]]], [shelf,[b]], [on,[a,b]], [watermelon,[e,f]], [fridge,[g]], [in,[[e,g],[f,g]]] ]).

model([a,b,c,d,e,f], [ [milk,[a,b]], [almond,[a]], [skim,[b]], [drank,[c,a]], [drink,[c,b]], [sam,[c]], [empty,[d]], [box,[d]], [popsicle,[e]], [type,[d,e]], [in,[d,f]], [freezer,[f]] ]).

			
% ==================================================
% Function i
% Determines the value of a variable/constant in an assignment G
% ==================================================

i(Var,G,Value):- 
    var(Var),
    member([Var2,Value],G), 
    Var == Var2.   

i(C,_,Value):- 
   nonvar(C),
   f(C,Value).


% ==================================================
% Function F
% Determines if a value is in the denotation of a Predicate/Relation
% ==================================================

f(Symbol,Value):- 
   model(_,F),
    member([Symbol,ListOfValues],F), 
    member(Value,ListOfValues).  


% ==================================================
% Extension of a variable assignment
% ==================================================

extend(G,X,[ [X,Val] | G]):-
   model(D,_),
   member(Val,D).


% ==================================================
% Existential quantifier
% ==================================================

sat(G1,exists(X,Formula),G3):-
   extend(G1,X,G2),
   sat(G2,Formula,G3).


% ==================================================
% Definite quantifier (semantic rather than pragmatic account)
% ==================================================

 sat(G1,the(X,and(A,B)),G3):-
   sat(G1,exists(X,and(A,B)),G3),
   i(X,G3,Value), 
   \+ ( ( sat(G1,exists(X,A),G2), i(X,G2,Value2), \+(Value = Value2)) ).




% ==================================================
% Negation 
% ==================================================

sat(G,not(Formula2),G):-
   \+ sat(G,Formula2,_).

% ==================================================
% Universal quantifier
% ==================================================

sat(G, forall(X,Formula2),G):-
  sat(G,not( exists(X,not(Formula2) ) ),G).


% ==================================================
% Conjunction
% ==================================================

sat(G1,and(Formula1,Formula2),G3):-
  sat(G1,Formula1,G2), 
  sat(G2,Formula2,G3). 


% ==================================================
% Disjunction
% ==================================================


sat(G1,or(Formula1,Formula2),G2):-
  ( sat(G1,Formula1,G2) ;
    sat(G1,Formula2,G2) ).


% ==================================================
% Implication
% ==================================================

sat(G1,imp(Formula1,Formula2),G2):-
   sat(G1,or(not(Formula1),Formula2),G2).


% ==================================================
% Predicates
% ==================================================

sat(G,Predicate,G):-
   Predicate =.. [P,Var],
   \+ (P = not),
   i(Var,G,Value),
   f(P,Value).

% ==================================================
% Two-place Relations
% ==================================================

sat(G,Rel,G):-
   Rel =.. [R,Var1,Var2],
   \+ ( member(R,[exists,forall,and,or,imp,the]) ),
   i(Var1,G,Value1),
   i(Var2,G,Value2),
   f(R,[Value1,Value2]).


% ===========================================================
%  Respond
%  For each input type, react appropriately.
% ===========================================================

% Declarative true in the model
respond(Evaluation) :- 
                Evaluation = [true_in_the_model], 
                write('That is correct'),!.

% Declarative false in the model
respond(Evaluation) :- 
                Evaluation = [not_true_in_the_model],  
                write('That is not correct'),!.

% Yes-No interrogative true in the model
respond(Evaluation) :- 
                Evaluation = [yes_to_question],                 
                write('yes').

% Yes-No interrogative false in the model               
respond(Evaluation) :- 
                Evaluation = [no_to_question],                  
                write('no').

% wh-interrogative true in the model
% ...                                                   

% wh-interrogative false in the model
% ...                                                   
