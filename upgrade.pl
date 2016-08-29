% The "upgrade" algorithm for repairing incomplete theories.
% Chenghao Cai. 18th August, 2016.


% An implementation of upgrade.

upgrade(G,TIn,N,D,TOut,R):-
  upgrade1(G,TIn,[],R,TOut,_,N,D,s).

/*
  % Negate goals.
  % We don't use 'not' here, because it is a build-in clause.
  findall(Xt,(member(X,G),negate_goal(X,Xt)),Gt),
  upgrade1(Gt,TIn,Tr,Rs,TOut,Nr,D,s).
*/


upgrade1(G,TIn,SubsIn,Rs,TOut,SubsOut,Nr,D,Res):-
  resolve_unblocking(G,TIn,SubsIn,RsMid,TMid,SubsMid,Nr,D,ResMid),
  (
    % If resolution succeeds, then return the results.
    ResMid = s,
    Res = s,
    TOut = TMid,
    SubsOut = SubsMid,
    Rs = RsMid
    ;
    % If not succeeds, then upgrades.
    ResMid = f,
    cost_of_repair(RsMid,CsMid),
    NrMid is Nr - CsMid,
    upgrade1(G,TMid,SubsMid,RsMid2,TOut,SubsOut,NrMid,D,s),
    Res = s,
    append(RsMid,RsMid2,Rs)
  ).

resolve_unblocking([],T,_,[],T,[],_,_,s):-!.
resolve_unblocking(GIn,TIn,SubsIn,Rs,TOut,SubsOut,Nr,D,Res):-
  % The search depth should > 0.
  D > 0,
  % Apply substitutions to the goal.
  subst_goals(SubsIn,GIn,G),
  % Get a goal.
  append(G1,[X|G2],G),
  % Get an axiom.
  append(T1,[A|T2],TIn),
  % Search.
  append(A1,[Y|A2],A),
  (
    X = -U,
    Y = +V
    ;
    X = +U,
    Y = -V
  ),
  % Unify.
  reform2_limited([V=U],[],Sb1,success,fail,Rs1,Nr),
  cost_of_repair(Rs1,Cs1),
  Nr1 is Nr - Cs1,
  Nr1 >= 0,
  (
    Cs1 = 0,
    % If cost is 0, then update the goals, and go on.
    append(A1,A2,A3),
    append(G1,A3,G3),
    append(G3,G2,G4),
    subst_goals(Sb1,G4,GNewT),
    append(SubsIn,Sb1,SubsMid),
    %GNew = GNewT,
    update_goals(GNewT,GNew),

    % Continue search.
    D1 is D - 1,
    resolve_unblocking(GNew,TIn,SubsMid,Rs,TOut,SubsOut,Nr1,D1,Res)
    ;
    % If cost > 0, then upgrade the theory, and return.
    Cs1 > 0,
    (
      X = -U,
      Y = +V,
      % Repair.
      repairall(Rs1,[V=nothing],[V1=nothing]),
      % Upgrade the theory.
      append(A1,[+V1|A2],ANew),
      append(T1,[ANew|T2],TNew)
      ;
      X = +U,
      Y = -V,
      % Repair.
      repairall(Rs1,[V=nothing],[V1=nothing]),
      % Upgrade the theory.
      append(A1,[-V1|A2],ANew),
      append(T1,[ANew|T2],TNew),
      SubsOut = []
    ),
    Rs = Rs1,
    TOut = TNew,
    Res = f
  ).
  


negate_goal(-X,+X):-!.
negate_goal(+X,-X):-!.

diff_sym(-X,+Y):-!.
diff_sym(+X,-Y):-!.

subst_goals(_,[],[]):-!.
subst_goals(Sb,[-X|L],[-X1|L1]):-
  substitutes(Sb,X,X1),
  subst_goals(Sb,L,L1),
  !.
subst_goals(Sb,[+X|L],[+X1|L1]):-
  substitutes(Sb,X,X1),
  subst_goals(Sb,L,L1),
  !.

update_goals(G,G):-!.

/*

update_goals(G,GRes):-
  % Eliminate duplicate goals.
  (
    G = [],
    G1 = []
    ;
    setof(X,member(X,G),G1)
  ),
  update_goals_sub(G1,GRes),
  !.
update_goals_sub(G,GRes):-
  % Eliminate +X and -X pairs.
  append(G1,[-X|G2],G),
  append(G3,[+X|G4],G),
  append(G1,G2,G5),
  delete(G5,+X,GT),
  update_goals_sub(GT,GRes),
  !.
update_goals_sub(G,G):-!.
*/


/*

update_goals(G,GRes):-
  % Eliminate duplicate goals.
  (
    \+member(-X,G),
    G1 = []
    ;
    setof(-X,member(-X,G),G1)
  ),
info(4,[ppppppppppp,G1]),
info(4,[ppppppppppp,GRes]),
  %update_goals_sub(G1,GRes),
  GRes = G1,
info(4,[ppppppp,GRes]),%read(QQQ),
  !.
update_goals_sub(G,GRes):-
  % Eliminate +X and -X pairs.
  append(G1,[-X|G2],G),
  append(G3,[+X|G4],G),
  append(G1,G2,G5),
  delete(G5,+X,GT),
  update_goals_sub(GT,GRes),
  !.
update_goals_sub(G,G):-!.
*/

trans_to_list([],[]):-!.
trans_to_list([+G|L],[+G1|L1]):-
  pred_to_list(G,G1),
  trans_to_list(L,L1),
  !.
trans_to_list([-G|L],[-G1|L1]):-
  pred_to_list(G,G1),
  trans_to_list(L,L1),
  !.

trans_theory_to_list([],[]):-!.
trans_theory_to_list([X|L],[X1|L1]):-
  trans_to_list(X,X1),
  trans_theory_to_list(L,L1).


trans_to_pred([],[]):-!.
trans_to_pred([+G|L],[+G1|L1]):-
  list_to_pred(G,G1),
  trans_to_pred(L,L1),
  !.
trans_to_pred([-G|L],[-G1|L1]):-
  list_to_pred(G,G1),
  trans_to_pred(L,L1),
  !.

trans_theory_to_pred([],[]):-!.
trans_theory_to_pred([X|L],[X1|L1]):-
  trans_to_pred(X,X1),
  trans_theory_to_pred(L,L1).


