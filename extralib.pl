% Some extra functions.
% Chenghao Cai. 18th August, 2016.


info(1,_):-!.
info(1,Y):-
    nl,print(Y),nl.

info(2,_):-!.
info(2,Y):-
    nl,print(Y),nl.

info(3,Y):-!.
info(3,Y):-
    nl,print(Y),nl.

info(4,Y):-
    nl,print(Y),nl.

% Remove duplicated repairs.
removeDuplicatedRepairs([],[]):-!.
removeDuplicatedRepairs([X|L],R1):-
    member(X,L),
    removeDuplicatedRepairs(L,R1),!.
removeDuplicatedRepairs([X|L],[X|R1]):-
    removeDuplicatedRepairs(L,R1),!.

prtinf(X):-
  print("HERE: "),
  print(X),nl.
printByLine([]).
printByLine([X|L]):-
  print(X),nl,
  printByLine(L).

pred_to_list(X,[X]):-
  (
    atom(X)
    ;
    number(X)
  ),
  !.
pred_to_list(vble(X),vble(X)):-!.
pred_to_list(P,[X|Res]):-
  P =.. [X|L],
  pred_to_list2(L,Res).

pred_to_list2([],[]):-!.
pred_to_list2([X|L],[Rx|Rl]):-
  pred_to_list(X,Rx),
  pred_to_list2(L,Rl).

list_to_pred([X],X):-
  (
    atom(X)
    ;
    number(X)
  ),
  !.
list_to_pred(vble(X),vble(X)):-!.
list_to_pred([X|L],Res):-
  list_to_pred2(L,R),
  Res =.. [X|R].

list_to_pred2([],[]):-!.
list_to_pred2([X|L],[Rx|Rl]):-
  list_to_pred(X,Rx),
  list_to_pred2(L,Rl).




for(I,I,J):-
	I =< J.
for(K,I,J):-
	I < J,
	I1 is I + 1,
	for(K,I1,J).


