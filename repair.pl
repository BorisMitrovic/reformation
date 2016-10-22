%% Apply repairs to Unification Problems %%
%% Alan Bundy, 23.2.12 %%
%% Revised By Boris Mitrovic, 16.05.13; 11.06.16 for ontology repair %%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%      UNIFICATION  REPAIR       %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% repairs(Rs,UIn,UOut): apply repairs Rs to unification problem UIn to get repaired unification problem UOut.

% Base case: if no repairs do nothing.
repairs([],U,U).

% Step case: apply each repair in turn.
repairs([H|T],UIn,UOut) :-
    repair(H,UIn,UMid), repairRepairs(H,T,TOut), repairs(TOut,UMid,UOut).          % repair does one repair to the head, then recurse on the tail.
repairs([merge(F1,F2)|T],UIn,UOut):-
    repairs([merge(F2,F1)|T],UIn,UOut),!.     % ******* Use F1 instead F2.

repairRepairs(_,[],[]).
repairRepairs(R, [H|T], [HOut|TOut]) :-
    repairRepair(R,H,HOut), repairRepairs(R,T,TOut).

repairRepair(merge(F,G),remove_n(F,N,L), remove_n(G,N,L)) :- !.   % TODO: Write out all possible interactions between repairs
repairRepair(merge(F,G),add_n(F,N,L), add_n(G,N,L)) :- !.   % *******: Write out all possible interactions between repairs
repairRepair(merge(F,G),remove_func(F,N,L), remove_func(G,N,L)) :- !.   % *******: Write out all possible interactions between repairs
repairRepair(_,U,U).

%%  repair(R,UIn,UOut): apply one repair.

% merge two functors from F1 to F2
repair(merge(F1,F2),[F1|Args]=RHS,[F2|Args]=RHS) :- !. % merge functors can happen in 4 ways.
repair(merge(F1,F2),LHS=[F1|Args],LHS=[F2|Args]).
repair(merge(F1,F2),[F2|Args]=RHS,[F1|Args]=RHS).
repair(merge(F1,F2),LHS=[F2|Args],LHS=[F1|Args]).



% remove (last) n arguments
repair(remove_n(F,N,left),LHS=[F|Args],LHS=[F|ArgsN]) :- !,
    length(Snip,N), append(ArgsN,Snip,Args).                 % use length and append backwards to find first N args of Args

repair(remove_n(F,N,right),[F|Args]=RHS,[F|ArgsN]=RHS) :- !,
    length(Snip,N), append(ArgsN,Snip,Args).                 % use length and append backwards to find first N args of Args

repair(remove_n(F,_,right), [G|_]=_,_) :- F\==G, !, fail.
repair(remove_n(F,_,left), _,[G|_]=_) :- F\==G, !, fail.

% add (last) n arguments
repair(add_n(F1,N,right),[F1|Args1]=[F2|Args2],[F1|Args1N]=[F2|Args2]) :- !,
       length(Add,N), append(_,Add,Args2),                             % Use length and append backwards to find, Add, the args to add
       append(Args1,Add,Args1N).                                       % Instantiate Add to extra args on the RHS

% add (last) n arguments
repair(add_n(F1,N,left),[F1|Args1]=[F2|Args2],[F1|Args1]=[F2|Args2N]) :- !,
       length(Add,N), append(_,Add,Args1),                             % Use length and append backwards to find, Add, the args to add
       append(Args2,Add,Args2N).                                       % Instantiate Add to extra args on the RHS

repair(add_n(F,_,_), [G|_]=_,_) :- F\==G, !, fail.

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
    \+protect([F]),                                      % F is not protected.
    gensym(F,F1).                                    % Extend F string with dash to form F1

repair(rename(F),LHS=[F|Args],LHS=[F1|Args]) :- !,   % Same as previous clause but on LHS
    \+protect([F]),                              % F is not protected.
    gensym(F,F1).


% remove ith argument
repair(remove_ith(F,I),vble(X)=E,vble(X)=EI) :- !,
    position([F|Args],E,P),                          % Find position of [F|Args] in E
    I1 is I-1, length(Front,I1),                     % Use length backwards to find Front I-1 args
    append(Front,[_|Back],Args),                     % and append to find Back I+1 to N args
    append(Front,Back,ArgsI),                        % Append Front to Back thus snipping out Ith arg
    replace(P,E,[F|ArgsI],EI).                       % Replace old subterm with new at position P to get EI

% ***remove ith argument of deeper function Tf2
repair(remove_ith(F,I),Df1=Df2,Df1=EI2) :- !,
    getfunction(F,Df2,[Tf2,Posiiton]),                % Find position of [F|Args] in Df2
    repair(remove_ith(F,I),vble(_)=Tf2,vble(_)=EI),   %% remove ith argument in Function Ff2 which is named F
    I1 is Posiiton-1, length(Front,I1),                     % Use length backwards to find Front I-1 args
    append(Front,[_|Back],Df2),                     % and append to find Back I+1 to N args
    append(Front,EI,ArgsI),                        % Append Front to EI(the changed function)
    append(ArgsI,Back,EI2).                       % Append EI(the changed function) to Back thus get the completed theory.

% ***remove function F，and replace it with a vble(c).
repair(remove_func(F),X=[F|_],X=vble(c)) :- !.

% ***remove function F，and replace it with a vble(c). When F is an element of E:
repair(remove_func(F),X=E,X=EI) :- !,
    getfunction(F,E,[Tf2,Posiiton]),!,                % Find position of [F|_] in E
      I1 is Posiiton-1, length(Front,I1),             % Use length backwards to find Front I-1 args
      append(Front,[Tf2|Back],E),                     % and append to find Back I+1 to N args
      append(Front,[vble(c)],Args1),                  % replace F with vble(c)
      append(Args1,Back,EI).                          % repaired theory EI


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
    \+protect([F]),                              % F is not protected.
    gensym(F,F1), countReps(rename(F),NrepsRest,Args,Args1),
    Nreps is NrepsRest + 1.

% Can't be applied to this term, try applying it to the rest
repair(rename(X),Nreps,[F|Args],[F|Args1]) :-
    \+protect([X]),                              % X is not protected.
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
repair(merge(F1,F2),Nreps,[F1|Args],[F2|Args1]) :- !,
  countReps(merge(F1,F2),NrepsRest,Args,Args1),
    Nreps is NrepsRest + 1.

% do nothing if different
repair(merge(F1,F2),Nreps,[F|Args],[F|Args1]) :- !,
  countReps(merge(F1,F2),Nreps,Args,Args1).

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
