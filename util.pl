%% Utility Procedures %%
%% Alan Bundy, 31.1.12 %%
%% Revised By Boris Mitrovic, 16.05.13; 11.06.16 %%


% some functions that should not be changed as repairs
:- dynamic function/1.
function(==).
function(=/=).

%% pprint(E): convert to input form and print

pprint(vble(X)) :- print(X),!.

pprint(vble(X)) :- print(X),!.

pprint([F|Args]) :- atomic(F), !,
    convert(E,[F|Args]), print(E).

pprint([]).

pprint([NE1=NE2|NEL]) :- !,
    convert(E1,NE1), convert(E2,NE2),
    print(E1=E2), print(', '),  pprint(NEL).

pprint([NE1/NE2|NEL]) :- !,
    convert(E1,NE1), convert(E2,NE2),
    print(E1/E2), print(', '), pprint(NEL).

% verbose(Switch): if Switch is on, use pretty printing

:- dynamic verbose/1.

verbose(off).

%% switch verbose on or off

switch :- verbose(S),retractall(verbose(S)), opposite(S,NS), assert(verbose(NS)),!.

%% opposite(S,NS): S and NS are opposites
opposite(on,off).
opposite(off,on).

% Keeps track of the current result of unification (FS) which is known at the end of recursion in reform2.
:- dynamic refsuccess/0.
refsuccess(success) :- refsuccess,!.
refsuccess(fail) :- \+(refsuccess),!.

%% convert(In,Out): convert normal Prolog syntax to internal representation or
%% vice versa.

%% These variable/constant conventions need revisiting for serious use

% Defination of protected element, which is not input axioms.
convert(protect(_),_):-!.
/*
% X maybe a protected element which should not be changed.
convert(X,Out):-
   setof(Ps, protect(Ps), Protect), % [[],[],[]]  % There is no caracter in the ontology.
   convert2(X,Out,Protect),!.
*/
% X is a variable
convert($X,vble(X)) :-  !.                      % Convert X into a variable
/*    atom_chars(X,[?|T]),              % variable is start with ?
    Out = vble(T),!.
    atomic(X), atom_chars(X,[H|_]),             % if first letter
    char_code(H,N), 109<N, N<123, !.            % is n-z

*/
% A is a constant
convert(A,[A]) :-                           % Convert A into a constant
    atomic(A), !.            % If first letter

% A is a number
convert(A,[A]) :-             % Convert A into a constant
    number(A),!.

% A is a opreator
convert(A,[A]) :-             % Convert A into a constant
    function(A), !.          % if it is a number



% E is compound
convert(E,[F|NArgs]) :-
    var(E), !,                                  % If E is output and input compound
    maplist(convert,Args,NArgs), E=..[F|Args].  % Recurse on all args of F


convert(E,[F|NArgs]) :-                     % If E is input and compound then
    \+ var(E), \+ atomic(E), \+ E = protected(_), !,  % protected is an internal form which do not needed convert any more.
    E=..[F|Args],  % break it into components
    maplist(convert,Args,NArgs).                % and recurse on them

% A is in the protected list
convert2(A,Output,Ps) :-                           % Convert A into a constant
  member([A],Ps) -> % Output = protect(A),!.
  string_concat("protect",A,ProtectA), atom_to_stem_list(ProtectA,Output), !.

/*renvert internal representation to normal Prolog syntax */

% X is a variable
revert(vble(X),$X) :-  !.                     % Convert a variable

% A is a constant or number
revert([A],A) :- !.                          % Convert a constant and number

%% These variable/constant conventions need revisiting for serious use
% E is compound
revert(E,E) :-
    atomic(E), !.                               % If E is output and input compound

% E is compound: F(NArgs).
revert(E,FactE) :-
    \+ var(E), \+ atomic(E),!,                                  % If E is output and input compound
    E =.. [F|Args],
    maplist(revert,Args,NArgs), FactE=..[F|NArgs].  % Recurse on all args of F



%% orlist(F,List): check F true on any element of List

% Step case
orlist(F,[H|T]) :- (call(F,H); orlist(F,T)).    % True if either true on head or tail


%% pairwise(L1,L2,Pairlist): pairs up corresponding elements of two lists.

% Base case
pairwise([],[],[]).             % If input two empty lists then return one.

% Step case
pairwise([H1|T1],[H2|T2],[H1=H2|T]) :- % Otherwise, pair up the heads
     pairwise(T1,T2,T).                % and recurse on the tails.


%% disjoin(D1,D2,D): return either D1 or D2 as D

% If they are the same, just return one.
disjoin(D,D,D) :- !.

% If either is empty, return the other.

disjoin([],D,D) :- !.
disjoin(D,[],D) :- !.

% Otherwise, just return one

disjoin(D1,D2,D) :- !, (D1=D ; D2=D).



% contains(vble(X):Sx,Rest): is vble(X):Sx contained in the Rest on either side
contains(vble(X),Rest) :- orlist(contains2(vble(X)),Rest), !.

contains2(vble(X),vble(X)=_) :- !.
contains2(vble(X),_=vble(X)) :- !.

contains2(vble(X),[_|Args]=_) :- orlist(contains2(vble(X)),Args), !.
contains2(vble(X),_=[_|Args]) :- orlist(contains2(vble(X)),Args), !.



containsR(X,Rep,Reps) :- orlist(containsRep(X,Rep),Reps).
containsRep(X,Rep,Rep) :- Rep =..[_|Args], orlist(containsA(X), Args),!.   % TODO: get all Repairs
containsA(X,X) :- !.

% containsDifferent(vble(X):Sx,Rest): is vble(X):Sx contained in the Rest on either side,
%   and is it unified against a different term (TODO: make it ununifiable)
containsDifferent(vble(X),Term,Rest) :- orlist(containsDifferent2(vble(X),Term),Rest), !.

containsDifferent2(vble(X),Term,vble(X)=Term2) :- Term \== Term2,!.
containsDifferent2(vble(X),Term,Term2=vble(X)) :- Term \== Term2,!.

containsDifferent2(vble(X),[_|Args]=Term) :- orlist(containsDifferent2(vble(X),Term),Args), !.
containsDifferent2(vble(X),Term=[_|Args]) :- orlist(containsDifferent2(vble(X),Term),Args), !.


%% occurs(vble(X):Sx,E): variable vble(X):Sx occurs in compound expression E

% Occurs check succeeds if it succeeds on any argument
occurs(vble(X),[_|Args]) :- orlist(occurs2(vble(X)),Args), !.


occurs(V,+T) :- !, occurs(V,T).
occurs(V,-T) :- !, occurs(V,T).
occurs(V,Clause) :- !, orlist(occurs(V),Clause).

%% occurs2(vble(X),E): variable vble(X) occurs in any expression E
% Base case
occurs2(vble(X),vble(X)) :- !.

% Step case
occurs2(vble(X),[_|Args]) :- !, orlist(occurs2(vble(X)),Args).

% subst(V/E,E1,E2): E2 is the result of substituting E for V in E1.

subst(vble(X)/C, vble(X), C) :- !.
subst(vble(X)/_, vble(Y), vble(Y)) :- X\==Y, !.

subst(Subst,[F|Args1],[F|Args2]) :-
   atomic(F), maplist(subst(Subst),Args1,Args2),!. % If E1 is compound then recurse on args.

subst(Subst,[E1=E2|Tl],[NE1=NE2|NTl]) :-       % If E1 is unification problem then
   subst(Subst,E1,NE1), subst(Subst,E2,NE2),   % apply substitution to both sides
   subst(Subst,Tl,NTl),!.                        % then recurse on tails

subst(Subst,[+E|T],[+NE|NT]) :-         % for substituting resolution ready clauses
   subst(Subst,E,NE),
   subst(Subst,T,NT),!.

subst(Subst,[-E|T],[-NE|NT]) :-
   subst(Subst,E,NE),
   subst(Subst,T,NT),!.

subst(Subst,[V/E|T],[V/NE|NT]) :-          % If E1 is substitution then
   subst(Subst,E,NE),                    % apply substitution to value
   subst(Subst,T,NT),!.                    % then recurse on tails

subst([Subst|Substs], E,NE) :- subst(Subst,E,NE1), subst(Substs,NE1,NE), !.
subst(_,[],[]) :-!.                          % If E1 is empty problem then do nothing
subst([],E,E) :-!.

substR(X/Y,Old,New) :- Old=..[F|Args], New=..[F|NewArgs], substA(X/Y,Args,NewArgs),!.
substA(X/Y,[X|Rest],[Y|NewRest]) :- substA(X/Y,Rest,NewRest),!.
substA(X/Y,[Z|Rest],[Z|NewRest]) :- Z\==X, substA(X/Y,Rest,NewRest),!.
substA(_,[],[]).

%% compose(Sub,SublistIn,SublistOut): SublistOut is the result of composing
%% singleton substitution Subst with substitution SublistIn

compose(Sub,SublistIn,[Sub|SublistMid]) :-     % Append new substitution
    subst(Sub,SublistIn,SublistMid).           % after applying it to the old one


%% and(FS1,FS2,FS): conjoin FS1 and FS2 to get FS

and(fail,fail,fail).
and(fail,success,fail).
and(success,fail,fail).
and(success,success,success).


%% gensym(In,Out): generate new symbol Out as In with suffix

gensym(In,Out) :-
    function(In), fail,!;
    atom_chars(In,InList),                    % Turn atom into list of characters
    append(InList,[d,a,s,h],Outlist),         % Append a dash to the list
    atom_chars(Out,Outlist).                  % and turn it back into an atom

% This simplistic renaming needs rethinking for serious use


%% position(Sub,Exp,Posn): Sub is at position Posn in Exp

% Base Case

position(Exp,Exp,[]).               % The current expression is at the empty position

% Step Case
/*  Otherwise, get the args of a compound expression;
    untill get the Arg equals Sub then the position(Sub,Arg,Posn) equals position(Exp,Exp,[]).
    Finish recursive, get the position I of Sub in Args
*/
position(Sub,[_|Args],[I|Posn]) :-  % skip the first element which is the function name.
    append(Front,[Arg|_],Args),     % Use append backwards to identify each argument Arg in turn
    length(Front,I1), I is I1+1,    % Work out I :what position of Arg in Args is
    position(Sub,Arg,Posn).         % Recurse on each argument


%% replace(P,E1,Sub,E2): replace position P in E1 with Sub to get E2

% Base case: found position.
replace([],_,Sub,Sub).              % To replace the current position return Sub

% Step case: find Ith argument and recurse on it
replace([I|Posn],[F|Args1],Sub,[F|Args2]) :-    % To replace anyother position
    I1 is I-1, length(Front,I1),                % Front is the first I-1 args
    append(Front,[Arg1|Back],Args1),            % Arg1 is the Ith
    replace(Posn,Arg1,Sub,Arg2),                % Recurse on the Ith arg then
    append(Front,[Arg2|Back],Args2).            % place new Ith arg back in the expression.



% quick sort by value for a list of pairs (value, repair)
quicksort(List,Sorted):-q_sort(List,[],Sorted).
q_sort([],Acc,Acc) :- !.
q_sort([H|T],Acc,Sorted):-
  pivoting(H,T,L1,L2),
  q_sort(L1,Acc,Sorted1),q_sort(L2,[H|Sorted1],Sorted).

pivoting(_,[],[],[]) :- !.
pivoting(((H1,H2),Vh),[((X1,X2),Vx)|T],[((X1,X2),Vx)|L],G):- (X1>H1; X1==H1,X2=<H2),  pivoting(((H1,H2),Vh),T,L,G), !.
pivoting(((H1,H2),Vh),[((X1,X2),Vx)|T],L,[((X1,X2),Vx)|G]):- pivoting(((H1,H2),Vh),T,L,G).


pickSnds(Pairs,Snds) :- maplist(pickSnd,Pairs,Snds).
pickSnd((_,Y),Y).


% detect negation
truefalse(-_,fail) :-!.
truefalse(_,success).


% converting between lists and tuples
list2tuple([A],A) :-!.
list2tuple([A|B1],','(A,B)) :- !, list2tuple(B1,B).

tuple2list(','(A,B), [A|B1]) :- !, tuple2list(B,B1).
tuple2list(A,[A]).

vprint(X) :- verbose(on),!, print(X); true.
vprintAll(X) :- verbose(on),!, printAll(X); true.

vnl :- verbose(on),!,nl; true.


%% switch(L,R): switch left for right and vice versa

switch(left,right).
switch(right,left).


/* Procedures not in Sictus, but in SWI
maplist(Pred,InList,Outlist): apply Pred to each element in Inlist to form Outlist
Every element is a proposition, like -cap_of(x,y), or +(x==z)
*/
maplist(_, [], []).
maplist(Pred, [H1|T1], [H2|T2]) :-
    Pred =.. PL,
    append(PL, [H1, H2], NewPred),
    Call =.. NewPred,
    call(Call),
    maplist(Pred, T1, T2).

/* Procedures not in Sictus, but in SWI
maplistGoal(Pred,InList,Outlist,OutGoalTree): apply Pred to each element in Inlist to form Outlist
Every element is a proposition, like -cap_of(x,y), or +(x==z)
Arg1: Predicate
Arg2: Input which is an axiom
Arg3: Output which is a clausal form of aiom(Cluase)
Arg4: The set of subgoals/goal in this axiom
*/
maplistGoal(_, [], [], []).
maplistGoal(Pred, [H1|T1], [H2|T2] ,[H3|T3]) :-
    Pred =.. PL,
    append(PL, [H1, H2, H3], NewPred),    % NewPred = Pred(H1,H2,H3)
    Call =.. NewPred,                     % call Pred(H1,H2,H3)

    call(Call),
    maplistGoal(Pred, T1, T2, T3).

%% nth1(N,List,Element): Element is Nth element of List

nth1(1,[X|_],X) :- !.
nth1(Idx,[_|List],X) :-
    Idx > 1,
    Idx1 is Idx-1,
    nth1(Idx1,List,X).


%% is_list(List): List is a list

is_list([_|_]).
is_list([]).

/*
Function name: getfunction: find the function named F in Df1.
Argument1:    the name of target function
Argument2:    the original function Df1
Argument3[A,B]: A is the list of function named F in Df1,
				B is the position of A in Df1
*/
% Argument2 itself is the function named F.
getfunction(F,[F|Args],[[F|Args],0]).

% get the function named F in Df1. Notice: every function is a list term.
% only one F in Df1
getfunction(F,Df1,[Tf1,PosI]):-
  member(Tf1,Df1),                 % find the deeper function Df2 in Df1 which is always started with [
  is_list(Tf1),
  [F|_] = Tf1,
  append(Front,[Tf1|_],Df1),
  length(Front,I), PosI is I+1.  % Work out I :what position of Arg in Args is
