%% Apply repairs to Unification Problems %%
%% Alan Bundy, 23.2.12 %%
%% Revised By Boris Mitrovic, 16.05.13; 11.06.16 for ontology repair %%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%      UNIFICATION  REPAIR       %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Substitute.
substitutes([],T,T):-!.
substitutes([X|_],_,_):-
    \+X = substitute(_,_),
    !,
    fail.
substitutes([X|L],T,U):-
    apply_substitute(X,T,T1),
    substitutes(L,T1,U).
apply_substitute(substitute(X1,X2),T,U):-
    apply_merge(merge(X1,X2),T,U).



repairall(_,[],[]):-!.
repairall(Rs,[X|L],[X1|L1]):-
    repairs(Rs,X,X1),
    repairall(Rs,L,L1).

%% repairs(Rs,UIn,UOut): apply repairs Rs to unification problem UIn to get repaired unification problem UOut.

% Base case: if no repairs do nothing. 
repairs([],U,U).

% Step case: apply each repair in turn.
repairs([H|T],UIn,UOut) :-
    repair(H,UIn,UMid), repairs(T,UMid,UOut).          % repair does one repair to the head, then recurse on the tail. 

%%  repair(R,UIn,UOut): apply one repair.

% Substitution.
repair(substitute(X1,X2),T1=T2,U1=U2):-
    apply_merge(merge(X1,X2),T1,U1),
    apply_merge(merge(X1,X2),T2,U2),
    !.

% Merge two terms.
repair(merge(X1,X2,left),T1=T2,U1=T2):-
    apply_merge(merge(X1,X2),T1,U1),
    !.
repair(merge(X1,X2,right),T1=T2,T1=U2):-
    apply_merge(merge(X1,X2),T2,U2),
    !.

% Apply a 'merge' operation to a list.
apply_merge(_,[],[]):-!.
apply_merge(merge(X1,X2),X1,X2):-!.
apply_merge(merge(X1,_),X,X):-
    \+is_list(X),
    X1 \= X,
    !.
apply_merge(merge(X1,X2),[X|L],[U|V]):-
    apply_merge(merge(X1,X2),X,U),
    apply_merge(merge(X1,X2),L,V).
    
% Permute arguments.
repair(permute(X,P,left),T1=T2,U1=T2):-
    apply_permute(permute(X,P),T1,U1),
    !.
repair(permute(X,P,right),T1=T2,T1=U2):-
    apply_permute(permute(X,P),T2,U2),
    !.

% Apply a 'permute' operation to a predicate.
apply_permute(_,T,T):-
    \+is_list(T),
    !.
apply_permute(permute(Y,P),[X|L],[X|L2]):-
    apply_permute2(permute(Y,P),L,L1),
    length(P,Len1),
    length(L1,Len2),
    (
        Y = X,
        Len1 = Len2,
        permute_arguments(L1,P,L2)
        ;
        Y \= X,
        L2 = L1
        ;
        Len1 \= Len2,
        L2 = L1
    ),
    !.
/*apply_permute(permute(Y,P),[X|L],[X|L1]):-
    Y \= X,
    apply_permute2(permute(Y,P),L,L1),
    !.*/

apply_permute2(_,[],[]):-!.
apply_permute2(A,[X|L],[X1|L1]):-
    apply_permute(A,X,X1),
    apply_permute2(A,L,L1).

permute_arguments(_,[],[]):-!.
permute_arguments(L,[Idx|P],[X|R]):-
    nth1(Idx,L,X),
    permute_arguments(L,P,R).

% Add a new argument (variable).
repair(addargv(X,Ar,N,left),T1=T2,U1=T2):-
    apply_addargv(addargv(X,Ar,N),T1,U1),
    !.
repair(addargv(X,Ar,N,right),T1=T2,T1=U2):-
    apply_addargv(addargv(X,Ar,N),T2,U2),
    !.

% Apply an 'addargv' operation to a predicate.
apply_addargv(_,T,T):-
    \+is_list(T),
    !.
apply_addargv(addargv(X,Ar,N),[X|L],[X|L2]):-
    length(L,Len),
    Ar = Len,
    apply_addargv2(addargv(X,Ar,N),L,L1),
    add_vble(L1,N,L2),
    !.
apply_addargv(addargv(Y,Ar,N),[X|L],[X|L1]):-
    (
        Y \= X
        ;
        length(L,Len),
        Ar \= Len
    ),
    apply_addargv2(addargv(Y,Ar,N),L,L1),
    !.

apply_addargv2(_,[],[]):-!.
apply_addargv2(A,[X|L],[X1|L1]):-
    apply_addargv(A,X,X1),
    apply_addargv2(A,L,L1).

% Add a variable to the Nth position.
:- dynamic new_vble/1.
:- retractall(new_vble(_)).
:- assert(new_vble(0)).
add_vble(L,N,R):-
    append(LL,LR,L),
    length(LL,N),
    new_vble(X),
    retract(new_vble(X)),
    X1 is X + 1,
    assert(new_vble(X1)),
    number_chars(X1,Chr),
    atom_chars(Atm,Chr),
    atom_concat('new',Atm,V),
    append(LL,[vble(V)|LR],R).



% Add a new argument (constant).
repair(addargc(X,Ar,N,C,left),T1=T2,U1=T2):-
    apply_addargc(addargc(X,Ar,N,C),T1,U1),
    !.
repair(addargc(X,Ar,N,C,right),T1=T2,T1=U2):-
    apply_addargc(addargc(X,Ar,N,C),T2,U2),
    !.

% Apply an 'addargc' operation to a predicate.
apply_addargc(_,T,T):-
    \+is_list(T),
    !.
apply_addargc(addargc(X,Ar,N,C),[X|L],[X|L2]):-
    length(L,Len),
    Ar = Len,
    apply_addargc2(addargc(X,Ar,N,C),L,L1),
    append(LL,LR,L1),
    length(LL,N),
    append(LL,[[C]|LR],L2),
    !.
apply_addargc(addargc(Y,Ar,N,C),[X|L],[X|L1]):-
    (
        Y \= X
        ;
        length(L,Len),
        Ar \= Len
    ),
    apply_addargc2(addargc(Y,Ar,N,C),L,L1),
    !.

apply_addargc2(_,[],[]):-!.
apply_addargc2(A,[X|L],[X1|L1]):-
    apply_addargc(A,X,X1),
    apply_addargc2(A,L,L1).



% Deleting an argument.
repair(delarg(X,Ar,N,left),T1=T2,U1=T2):-
    apply_delarg(delarg(X,Ar,N),T1,U1),
    !.
repair(delarg(X,Ar,N,right),T1=T2,T1=U2):-
    apply_delarg(delarg(X,Ar,N),T2,U2),
    !.

% Apply an 'delarg' operation to a predicate.
apply_delarg(_,T,T):-
    \+is_list(T),
    !.
apply_delarg(delarg(X,Ar,N),[X|L],[X|L2]):-
    length(L,Len),
    Ar = Len,
    append(LL,[_|LR],L),
    length(LL,N),
    append(LL,LR,L1),
    apply_delarg2(delarg(X,Ar,N),L1,L2),
    !.
apply_delarg(delarg(Y,Ar,N),[X|L],[X|L1]):-
    (
        Y \= X
        ;
        length(L,Len),
        Ar \= Len
    ),
    apply_delarg2(delarg(Y,Ar,N),L,L1),
    !.

apply_delarg2(_,[],[]):-!.
apply_delarg2(A,[X|L],[X1|L1]):-
    apply_delarg(A,X,X1),
    apply_delarg2(A,L,L1).

/*
% Stable version.
% Add new arguments (variables).
repair(addargs(X,Ar,N,left),T1=T2,U1=T2):-
    apply_addargs(addargs(X,Ar,N),T1,U1),
    !.
repair(addargs(X,Ar,N,right),T1=T2,T1=U2):-
    apply_addargs(addargs(X,Ar,N),T2,U2),
    !.

% Apply an 'addargs' operation to a predicate.
apply_addargs(_,T,T):-
    \+is_list(T),
    !.
apply_addargs(addargs(X,Ar,N),[X|L],[X|L2]):-
    length(L,Len),
    Ar = Len,
    apply_addargs2(addargs(X,Ar,N),L,L1),
    add_variables(L1,N,L2),
    !.
apply_addargs(addargs(Y,Ar,N),[X|L],[X|L1]):-
    (
        Y \= X
        ;
        length(L,Len),
        Ar \= Len
    ),
    apply_addargs2(addargs(Y,Ar,N),L,L1),
    !.

apply_addargs2(_,[],[]):-!.
apply_addargs2(A,[X|L],[X1|L1]):-
    apply_addargs(A,X,X1),
    apply_addargs2(A,L,L1).

:- dynamic new_vble/1.
:- retractall(new_vble(_)).
:- assert(new_vble(0)).
add_variables(L,0,L):-!.
add_variables(L,N,R):-
    N1 is N - 1,
    new_vble(X),
    retract(new_vble(X)),
    X1 is X + 1,
    assert(new_vble(X1)),
    append(L,[vble(new(X1))],L1),
    add_variables(L1,N1,R).
*/

% Add a new functor.
repair(addfunc(X,Ar,F,left),T1=T2,U1=T2):-
    apply_addfunc(addfunc(X,Ar,F),T1,U1),
    !.
repair(addfunc(X,Ar,F,right),T1=T2,T1=U2):-
    apply_addfunc(addfunc(X,Ar,F),T2,U2),
    !.

% Apply a 'addfunc' operation to a list.
apply_addfunc(addfunc(X,Ar,F),[X|L],[F,[X|L1]]):-
    length(L,Ar),
    apply_addfunc2(addfunc(X,Ar,F),L,L1),
    !.
apply_addfunc(addfunc(X,Ar,F),[Y|L],[Y|L1]):-
    (
        X \= Y
        ;
        X = Y,
        \+length(L,Ar)
    ),
    apply_addfunc2(addfunc(X,Ar,F),L,L1),
    !.
apply_addfunc(addfunc(_,_,_),vble(Y),vble(Y)):-!.
apply_addfunc2(_,[],[]):-!.
apply_addfunc2(addfunc(X,Ar,F),[P|L],[U|V]):-
    apply_addfunc(addfunc(X,Ar,F),P,U),
    apply_addfunc2(addfunc(X,Ar,F),L,V).
    

% Delete a functor.
repair(delfunc(X,Ar,P,left),T1=T2,U1=T2):-
    apply_delfunc(delfunc(X,Ar,P),T1,U1),
    !.
repair(delfunc(X,Ar,P,right),T1=T2,T1=U2):-
    apply_delfunc(delfunc(X,Ar,P),T2,U2),
    !.

% Apply a 'delfunc' operation to a list.
apply_delfunc(delfunc(X,Ar,P),[X|L],Y):-
    length(L,Ar),
    append(LL,[T|_],L),
    length(LL,P),
    apply_delfunc(delfunc(X,Ar,P),T,Y),
    !.
apply_delfunc(delfunc(X,Ar,P),[Y|L],[Y|L1]):-
    (
        X \= Y
        ;
        X = Y,
        \+length(L,Ar)
    ),
    apply_delfunc2(delfunc(X,Ar,P),L,L1),
    !.
apply_delfunc(delfunc(_,_,_),vble(Y),vble(Y)):-!.
apply_delfunc2(_,[],[]):-!.
apply_delfunc2(delfunc(X,Ar,P),[R|S],[U|V]):-
    apply_delfunc(delfunc(X,Ar,P),R,U),
    apply_delfunc2(delfunc(X,Ar,P),S,V).

% Make arities different
repair(diff_arities(FL,FR),[FL|ArgsL]=[FR|ArgsR],[FL|ArgsL1]=[FR|ArgsR]) :-
	append(ArgsL1,[_],ArgsL).	                       % Use append backwards to remove last LHS arg.

repair(diff_arities(FL,FR),[FL|ArgsL]=[FR|ArgsR],[FL|ArgsL]=[FR|ArgsR1]) :-
	append(ArgsR1,[_],ArgsR).	                       % Use append backwards to remove last RHS arg.

repair(diff_arities(FL,FR),[FL|ArgsL]=[FR|ArgsR],[FL|ArgsL1]=[FR|ArgsR]) :-
	append(ArgsL,[dummy],ArgsL1).	                   % Append extra arg onto original LHS

repair(diff_arities(FL,FR),[FL|ArgsL]=[FR|ArgsR],[FL|ArgsL]=[FR|ArgsR1]) :-
	append(ArgsR,[dummy],ArgsR1).	                   % Append extra arg onto original RHS

% rename F
repair(rename(F),[F|Args]=RHS,[F1|Args]=RHS) :-
    gensym(F,F1).                                    % Extend F string with dash to form F1

repair(rename(F),LHS=[F|Args],LHS=[F1|Args]) :- !,   % Same as previous clause but on LHS  
    gensym(F,F1).


% remove ith argument
repair(remove_ith(F,I),vble(X)=E,vble(X)=EI) :- !,
    position([F|Args],E,P),                          % Find position of [F|Args] in E
    I1 is I-1, length(Front,I1),                     % Use length backwards to find Front I-1 args
    append(Front,[_|Back],Args),                     % and append to find Back I+1 to N args
    append(Front,Back,ArgsI),                        % Append Front to Back thus snipping out Ith arg
    replace(P,E,[F|ArgsI],EI).                       % Replace old subterm with new at position P to get EI

% add X as additional argument to F
repair(insert_var(F,X),vble(X)=[F|Args],vble(X)=[F|ArgsX]) :- !,
    append(Args,[X],ArgsX).                          % Append X onto end of Args to get ArgsX

% Error if we cannot deal with repair. 
repair(R,U,_) :- !, print('** Unable to handle repair **'), print(R), print(' on '), print(U), nl, nl, fail.




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%     ONTOLOGY   REPAIR       %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% for ontology repair keep track of a number of repairs applied
% Base case: if no repairs do nothing. 
repairs([],0,U,U).

% Step case: apply each repair in turn.
repairs([H|T],NRepsOut,UIn,UOut) :-
    repair(H,NRepsCur,UIn,UMid), repairs(T,NRepsRec,UMid,UOut),
    NRepsOut is NRepsCur + NRepsRec.  

% Rename F
repair(rename(F),Nreps,[F|Args],[F1|Args1]) :- !,
    gensym(F,F1), countReps(rename(F),NrepsRest,Args,Args1),
    Nreps is NrepsRest + 1.

% Can't be applied to this term, try applying it to the rest
repair(rename(X),Nreps,[F|Args],[F|Args1]) :-
    X\=F, !, countReps(rename(X),Nreps,Args,Args1).

% Make arities different
% Heuristic - don't allow repairing inequality
repair(diff_arities((\=),(\=)),0,F,F) :- !.

repair(diff_arities(F,L),Nreps,[X|Args],[X|Args2]) :-     % do nothing if different
    length(Args,La),(F\=X;L\=La), !, countReps(diff_arities(F,L),Nreps,Args,Args2).

repair(diff_arities(F,L),Nreps,[F|Args],[F|Args2]) :- !,  % adding a dummy argument
    length(Args,L),countReps(diff_arities(F,L),NrepsRest,Args,Args1), append(Args1,[[dummy]],Args2), 
    Nreps is NrepsRest + 1.

% Insert variable X in F
repair(insert_var(F,X),Nreps,[F|Args],[F|Args2]) :- !,
    countReps(insert_var(F,X),NrepsRest,Args,Args1), append(Args1,[vble(X)],Args2), 
    Nreps is NrepsRest + 1.

% If not F, try to apply to rest
repair(insert_var(F,X),Nreps,[F2|Args],[F2|Args2]) :-
    F\=F2, !, countReps(insert_var(F,X),Nreps,Args,Args2).

% merge two functors
repair(merge(F1,F2,_),Nreps,[F1|Args],[F2|Args1]) :- !,
  countReps(merge(F1,F2,_),NrepsRest,Args,Args1),
    Nreps is NrepsRest + 1.

% do nothing if different
repair(merge(F1,F2,_),Nreps,[F|Args],[F|Args1]) :- !,
  countReps(merge(F1,F2,_),Nreps,Args,Args1).

% deal with different formats
% positive literals
repair(R,Nreps,+(UI),+(UO)) :- !,
  repair(R,Nreps,UI,UO).

% negative literals
repair(R,Nreps,-(UI),-(UO)) :- !,
  repair(R,Nreps,UI,UO).

% make into lists if not  
repair(R,Nreps,V,NV) :- !,
  \+(is_list(V)),
  repair(R,Nreps,[V],[NV]).  

% Error if we cannot deal with repair. 
repair(R,_,U,_) :- !, print('** Unable to handle ontology repair **'),
    print(R), print(' on '), print(U), nl, nl, fail.

% helper functions to keep track of repairs taken
countReps(_,0,[],[]).
countReps(Repair,Nreps,[H|Arg],[NewH|NewArg]) :-
  repair(Repair,NrepsCur,H,NewH),
  countReps(Repair,NrepsRec,Arg,NewArg),
  Nreps is NrepsCur + NrepsRec.
