% The "redirect" algorithm for repairing faulty analogical blends of rewrite rules.
% Chenghao Cai. 18th August, 2016.

get_member(X,L):-
  member(Y,L),
  copy_term(Y,Y1),
  unify_with_occurs_check(X,Y1).

is_simplest(X,_):-
  var(X),
  !.
is_simplest(X,Rule):-
  \+is_list(X),
  \+get_member(simp(X,_),Rule),
  X =.. [_|L1],
  is_simplest(L1,Rule).
is_simplest([],_).
is_simplest([X|L],Rule):-
  is_simplest(X,Rule),
  is_simplest(L,Rule).


% Rewrite only once.

rewrite_base(X,X,_,[]):-
  var(X),
  !,
  fail.
rewrite_base(X,X,Rule,[]):-
  \+var(X),
  \+is_list(X),
  is_simplest(X,Rule),
  !,
  fail.

rewrite_base(X,Y,Rule,Path):-
  \+var(X),
  \+is_list(X),
  get_member(simp(S,Y),Rule),
  copy_term(simp(S,Y),Path),
  X = S.
rewrite_base(X,Y,Rule,Path):-
  \+var(X),
  \+atom(X),
  \+is_list(X),
  X =.. [P|L1],
  rewrite_base(L1,L2,Rule,Path),
  L1 \== L2,
  Y =.. [P|L2].
rewrite_base(L,Ls,Rule,Path):-
  \+var(L),
  L = [X|L1],
  (
    rewrite_base(X,Y,Rule,Path),
    Ls = [Y|L1]
    ;
    rewrite_base(L1,L2,Rule,Path),
    Ls = [X|L2]
  ).

simplify(_,_,_,Depth,_):-
  Depth < 0,
  !,
  fail.
simplify(X,Y,Rule,Depth,Path):-
  Depth > 0,
  rewrite_base(X,Mid,Rule,Ps),
  D1 is Depth - 1,
  simplify(Mid,Y,Rule,D1,Pl),
  Path = [Ps|Pl]
  ;
  \+rewrite_base(X,Mid,Rule,Ps),
  Y = X,
  Path = [].

info(_):-!.
info(X):-
  nl,print('INFO: '),print(X),nl.
printByLine([]).
printByLine([X|L]):-
  print(X),nl,
  printByLine(L).


rewrite_limited(_,_,_,Depth,_):-
  Depth < 0,
  !,
  fail.
rewrite_limited(X,Y,Rule,Depth,Path):-
  Depth > 0,
  rewrite_base(X,Mid,Rule,Ps),
  D1 is Depth - 1,
  rewrite_limited(Mid,Y,Rule,D1,Pl),
  Path = [Ps|Pl]
  ;
  Y = X,
  Path = [].


simplify_with_reformation(X,X,Rule,Rule,_):-
  var(X),
  !.
simplify_with_reformation(X,X,Rule,Rule,_,0):-
  \+var(X),
  \+is_list(X),
  is_simplest(X,Rule),!.

simplify_with_reformation(X,Y,RuleIn,RuleOut,NrMax,NrUsed):-
  \+var(X),
  \+is_list(X),
  get_member(simp(X1,Mid),RuleIn),
  (
    X = X1,
    simplify_with_reformation(Mid,Y,RuleIn,RuleOut,NrMax,NrUsed)
    ;
    X \= X1,
    remove_one_member(simp(X1,Mid),RuleIn,Rule1),
    copy_term(simp(X1,Mid),simp(Xs,Mids)),
    unify_with_reformation([X1=X],Nr,[X1=X],Rs),
    % Here, subsitution rules in Rs will NOT been applied to Xs.
    copy_term(X,Xt),
    repairall(Rs,[Xs=Xt],[Us=Ut]),
    add_one_member(simp(Us,Mids),Rule1,Rule2),
    Nrc = 1,
    Nr1 is Nr - Nrc,
    Nr1 >= 0,
    simplify_with_reformation(Mid,Y,Rule2,RuleOut,Nr1,Nr2),
    NrUsed is Nr2 + Nrc,
    NrUsed =< NrMax
  ).
simplify_with_reformation(X,Y,RuleIn,RuleOut,NrMax,NrUsed):-
  \+var(X),
  \+is_list(X),
  X =.. [P|L1],
  simplify_with_reformation(L1,L2,RuleIn,RuleOut,NrMax,NrUsed),
  L1 \== L2,
  Y =.. [P|L2].
simplify_with_reformation([],[],_,Rule,Rule,_,0).
simplify_with_reformation(L,[Y|L2],RuleIn,RuleOut,NrMax,NrUsed):-
  \+var(L),
  L = [X|L1],
  simplify_with_reformation(X,Y,RuleIn,Rule1,NrMax,Nr1),
  Nr2 is NrMax - Nr1,
  simplify_with_reformation(L1,L2,Rule1,RuleOut,Nr2,NrUsed),
  NrUsed =< NrMax.

remove_one_member(X,L,Res):-
  append(L1,[X|L2],L),
  append(L1,L2,Res).

add_one_member(X,L,[Y|L]):-
  copy_term(X,Y).

unify_with_reformation([X=Y],Nr,[X3=Y3],Rs):-
  pred_to_reform_format(X,X1,[],Vble1),
  pred_to_reform_format(Y,Y1,Vble1,Vble2),
  filter_rewrite(F),
  ccf_unblock_limited([X1=Y1],Nr,F,[],Rs,[X2=Y2]),
  reform_format_to_pred(X2,Vble2,X3),
  reform_format_to_pred(Y2,Vble2,Y3).

apply_repairs_to_pred(Rs,Pred,Res):-
  pred_to_reform_format(Pred,P1,[],Vble1),
  repairs(Rs,P1=P1,P2=_),
  reform_format_to_pred(P2,Vble1,Res).

:- dynamic pred_vble/1.
:- retractall(pred_vble(_)).
:- assert(pred_vble(0)).
pred_to_reform_format(X,V,Vble,Vble):-
  var(X),
  member(var_to_vble(X1,V),Vble),
  X == X1,
  !.
pred_to_reform_format(X,vble(N1),VbleIn,[NewVble|VbleIn]):-
  var(X),
  pred_vble(N),
  retractall(pred_vble(N)),
  N1 is N + 1,
  assert(pred_vble(N1)),
  NewVble = var_to_vble(X,vble(N1)),
  !.
pred_to_reform_format(X,[X],Vble,Vble):-
  (
    atom(X)
    ;
    number(X)
  ),
  !.
pred_to_reform_format(P,[X|Res],VbleIn,VbleOut):-
  P =.. [X|L],
  pred_to_reform_format2(L,Res,VbleIn,VbleOut).
pred_to_reform_format2([],[],Vble,Vble):-!.
pred_to_reform_format2([X|L],[Rx|Rl],VbleIn,VbleOut):-
  pred_to_reform_format(X,Rx,VbleIn,VbleMid),
  pred_to_reform_format2(L,Rl,VbleMid,VbleOut).

reform_format_to_pred([X],_,X):-!.
reform_format_to_pred(vble(V),Vble,X):-
  member(var_to_vble(X,vble(V)),Vble),
  !.
reform_format_to_pred(vble(_),_,X):-!.
reform_format_to_pred([X|L],Vble,P):-
  reform_format_to_pred2(L,Vble,L1),
  P =.. [X|L1].
reform_format_to_pred2([],_,[]):-!.
reform_format_to_pred2([X|L],Vble,[X1|L1]):-
  reform_format_to_pred(X,Vble,X1),
  reform_format_to_pred2(L,Vble,L1).

:- dynamic pred_lab/1.
:- retractall(pred_lab(_)).
:- assert(pred_lab(0)).
label_pred(X,X):-
  var(X),
  !.
label_pred(X,X1):-
  (
    atom(X)
    ;
    number(X)
  ),
  pred_lab(N),
  retractall(pred_lab(_)),
  N1 is N + 1,
  assert(pred_lab(N1)),
  number_chars(N1,Chr),
  atom_chars(Atm,Chr),
  atom_concat('id',Atm,P1),
  atom_concat(X,P1,X1),
  !.
label_pred(Pred,Res):-
  Pred =.. L,
  label_pred2(L,L1),
  Res =.. L1.
label_pred2([],[]):-!.
label_pred2([X|L],[X1|L1]):-
  label_pred(X,X1),
  label_pred2(L,L1).

not_locally_confluent(Rule,[X,Y1,Y2],Depth):-
  get_member(simp(X,_),Rule),
  simplify(X,Y1,Rule,Depth,Path1),
  simplify(X,Y2,Rule,Depth,Path2),
  Y1 \= Y2.

reverse_simp_rule([],[]):-!.
reverse_simp_rule([simp(X1,Y1)|L1],[simp(X2,Y2)|L2]):-
  copy_term(simp(X1,Y1),simp(Y2,X2)),
  reverse_simp_rule(L1,L2),
  !.

rewrite_trace(X,X,[],0):-!.
rewrite_trace(X,Y,_,Depth):-
  Depth < 0,
  !.
rewrite_trace(X,Y,[R|Path],Depth):-
  rewrite_limited(X,Mid,[R],1,[R]),
  D1 is Depth - 1,
  rewrite_trace(Mid,Y,Path,D1).  

simp_rule_reform(_,_,_,Nr,_,[]):-
  Nr =< 0,
  !,
  fail.
simp_rule_reform(Rule,FwdDepth,BkwdDepth,_,Rule,[]):-
  \+not_locally_confluent(Rule,_,FwdDepth),
  !.
simp_rule_reform(Rule,FwdDepth,BkwdDepth,Nr,RuleOut,Rs):-
  Nr > 0,
  get_member(simp(X,_),Rule),
  copy_term(X,Xt),
  reverse_simp_rule(Rule,RuleRev),
  simplify(X,Y1,Rule,FwdDepth,Path1),
  simplify(X,Y2,Rule,FwdDepth,Path2),
  Y1 \= Y2,
  copy_term(Y1,Yt),
  setof((U,Path),rewrite_limited(Y1,U,RuleRev,BkwdDepth,Path),TgtSet),
  reform_locally(Xt,Yt,Path2,TgtSet,Nr,Rule,RuleMid,Rs1),
  length(Rs1,L1),
  Nr1 is Nr - L1,
  Nr1 >= 0,
  (
    \+need_repairs(RuleMid,FwdDepth),
    RuleOut = RuleMid,
    Rs = Rs1
    ;
    need_repairs(RuleMid,FwdDepth),
    simp_rule_reform(RuleMid,FwdDepth,BkwdDepth,Nr1,RuleOut,Rs2),
    append(Rs1,Rs2,Rs)
  ).

need_repairs(Rule,Depth):-
  copy_term(Rule,Rule1),
  not_locally_confluent(Rule1,_,Depth),
  !.

reform_locally(X,Y,Path,TgtSet,Nr,Rule,RuleOut,Rs):-
  Nr > 0,
  copy_term(X,Xt),
  copy_term(Y,Yt),
  length(Path,Len),
  for(I,1,Len),
  first_n_elements(I,Path,Path1),
  rewrite_trace(X,T,Path1,I),
  \+member((T,_),TgtSet),
  (
    append(Path2,[simp(P1,P2)],Path1),
    copy_term(T,Tt),
    setof(U,Pathv^member((U,Pathv),TgtSet),TgtSet1),
    get_member(V,TgtSet1),
    unify_with_reformation([Tt=V],Nr,_,RsSs),
    findall(RR,(member(RR,RsSs),RR \= substitute(_,_)),Rs),
    apply_repairs_to_pred(Rs,P2,P4),
    remove_one_member(simp(P1,P2),Rule,Rule1),
    add_one_member(simp(P1,P4),Rule1,Rule2)
    ;
    fail, % Do not use this.
    get_member((V,Pathv),TgtSet),
    append(Path2,[simp(P1,P2)],Pathv),
    label_pred(P2,P3),
    append(Path2,[simp(P1,P3)],Path4),
    length(Path4,L4),
    rewrite_trace(Yt,Vt,Path4,L4),
    unify_with_reformation([Vt=T],Nr,_,Rs),
    apply_repairs_to_pred(Rs,P3,P4),
    remove_one_member(simp(P2,P1),Rule,Rule1),
    add_one_member(simp(P4,P1),Rule1,Rule2)
  ),
  \+illegal_rules(Rule2),
  eliminate_duplicate_rules(Rule2,RuleOut).

illegal_rules(Rule):-
  member(R,Rule),
  unify_with_occurs_check(simp(X,X),R),
  !.

eliminate_duplicate_rules(RuleIn,RuleOut):-
  setof(X,member(X,RuleIn),RuleOut),
  !.

first_n_elements(0,_,[]):-!.
first_n_elements(N,[X|L],[X|L1]):-
  N > 0,
  N1 is N - 1,
  first_n_elements(N1,L,L1).

simp_rule_revise(Rule,FwdDepth,BkwdDepth,MaxNr,Res,Rs):-
  for(Nr,1,MaxNr),
  simp_rule_reform(Rule,FwdDepth,BkwdDepth,Nr,Res,Rs),
  length(Rs,Nr).


redirect(RuleIn,DF,DB,N,RuleOut,R):-
  simp_rule_reform(RuleIn,DF,DB,N,RuleOut,R).
