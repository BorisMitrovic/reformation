% The "align" algorithm for adjusting alignments of analogical blends.
% Chenghao Cai. 18th August, 2016.

align([],T,_,T,[]):-!.
align(S,[],_,S,[]):-!.
align(S,T,Nr,B,R):-
  Nr >= 0,
  findall(C,(member(Ax1,S),member(Ax2,T),reform_align_minimal([Ax1=Ax2],Rsn,Nr),cost_of_repair(Rsn,C)),CostList),
  (
    CostList = [],
    Nr1 = -1
    ;
    CostList \= [],
    min_list(CostList,Cmin),
    Nr1 is Nr - Cmin
  ),
  (
    Nr1 < 0,
    append(S,T,B),
    R = []
    ;
    Nr1 >= 0,
    member(X,S),member(Y,T),reform_align([X=Y],Rs,Cmin),
    delete_once(S,X,Stmp),
    repair_source_theory(Stmp,Rs,S1),
    delete_once(T,Y,T1),
    align(S1,T1,Nr1,B1,R1),
    B = [Y|B1],
    append(Rs,R1,R)
  ).


reform_align_minimal([Ax1=Ax2],Rsn,Nr):-
  for(I,0,Nr),
  reform_align([Ax1=Ax2],Rsn,I),
  !.


repair_source_theory([],_,[]):-!.
repair_source_theory([X|L],Rs,[X1|L1]):-
  repairall(Rs,[X=nothing],[X1=nothing]),
  repair_source_theory(L,Rs,L1).

delete_once([X|L],T,Res):-
  (
    X \= T,
    delete_once(L,T,L1),
    Res = [X|L1],
    !
    ;
    X = T,
    Res = L,
    !
  ).

reform_align(T,Rs,Nr):-
    filter_align(F),
    ccf_unblock_limited(T,Nr,F,[],Rss,_),
    findall(X,(member(X,Rss),\+X=substitute(_,_)),Rs),
    findall(X,(member(X,Rss),X=substitute(_,_)),_).

trans_all_to_list([],[]):-!.
trans_all_to_list([G|L],[G1|L1]):-
  pred_to_list(G,G1),
  trans_all_to_list(L,L1),
  !.

trans_all_to_pred([],[]):-!.
trans_all_to_pred([G|L],[G1|L1]):-
  list_to_pred(G,G1),
  trans_all_to_pred(L,L1),
  !.

 
matching(S,T,Nr,Res):-
  findall([C,'-----',Xp=Yp],(member(X,S),member(Y,T),reform2_limited([X=Y],[],SigmaOut,success,fail,Rs,Nr),cost_of_repair(Rs,C),list_to_pred(X,Xp),list_to_pred(Y,Yp)),Res).


