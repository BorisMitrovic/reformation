%% Utility functions for Revising the ontology %%
%% Boris Mitrovic, 16.05.13; revised 11.06.16 %%

% converting clauses using convert
/*
Input:
	In is the set of axioms.
Output:
	Out is a whole aixom in clasual form.
*/
convertClause(In,Out) :-
	maplist(convertTerm,In,Out).

convertTerm(+In,+Out) :-
	convert(In,Out).

convertTerm(-In,-Out) :-
	convert(In,Out).


% all elements of a clause after a term
afterClause(C,[C|AfterOnt],AfterOnt) :-!.
afterClause(C,[_|Ont],AfterOnt) :-
	afterClause(C,Ont,AfterOnt).


% Does the repair make sense for a given clause? Specifies necessary conditions.
% sensibleRep([insert_var(_,V)],Cl) :- !, occurs(V,Cl).
% TODO: define sensibility for other repairs
sensibleRep(_,_).

oppositeSigns(+L,-R,L,R) :- !.
oppositeSigns(-L,+R,L,R).


% produces a list of integers up to a number in reversed order.
enum(0,[]) :- !.
enum(N,List) :-
	N1 is N-1,
	enum(N1,Rest),
	List = [N|Rest].

% remove all occurances of an element from a list
remove(_,[],[]).
remove(A, [A|B], C) :- !,
	remove(A,B,C).
remove(A, [B|R], [B|N]) :-
	remove(A, R, N).

% prints  alist line by line
printAll([]) :- !.
printAll([C|Cs]) :-
	print(C),nl, printAll(Cs).

% gives the resulting clause assuming the resolution was successful.
resultingClause(C1,I1,C2,I2,NewC) :-
	I11 is I1-1, I21 is I2-1,
	append(B1,[_|E1],C1), length(B1,I11),  % B1 is the list of first I11 elements of C1
	append(B2,[_|E2],C2), length(B2,I21),  % B2 is the list of first I21 elements of C2
	append(B1,B2,B),  % the lengh of B is I11+I21 = I1 + I2 - 2
	append(E1,E2,E),  % the lengh of E is LenghC1 + LenghC2 - I1 - I2
	append(B,E,NewC), !.


unifiableShallow(X,Y) :- %  transformation if needed
	\+(X=vble(_)),
	\+(X=[_|_]),
	unifiableShallow([X],Y).

unifiableShallow(X,Y) :- %  transformation if needed
	\+(Y=vble(_)),
	\+(Y=[_|_]),
	unifiableShallow(X,[Y]).

% Does the current unification problem unify, without the recursive steps
unifiableShallow(vble(_),vble(_)).

unifiableShallow([F1|Args1], [F2|Args2]) :- %  CC
    F1==F2,
    length(Args1,L), length(Args2,L).

unifiableShallow([F|Args],vble(_)) :- %  CV
	unifiableShallow(vble(_),[F|Args]). %  VC

unifiableShallow(vble(_),[_|_]).

% set heuristic to `iter` mode -> will try every possible combination of repairs (exponential). `best` is a local best repair at each stage, according to a heuristic
:- dynamic heuristic/1.
heuristic("iter").

setHeuristic(H) :- retractall(heuristic(_)),assert(heuristic(H)).
