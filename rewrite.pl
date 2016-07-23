info(_):-!.
info(X):-
  nl,print('INFO: '),print(X),nl.
printByLine([]).
printByLine([X|L]):-
  print(X),nl,
  printByLine(L).


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
  %\+member_with_occurs_check(simp(X,_),Rule).
  %\+member(simp(X,_),Rule).
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


/*

simplify(_,_,_,Depth,_):-
  Depth < 0,
  !,
  fail.
simplify(X,X,_,_,[]):-
  var(X),
  !.
simplify(X,X,Rule,_,[]):-
  \+var(X),
  \+is_list(X),
  is_simplest(X,Rule),!.
  %\+member_with_occurs_check(simp(X,_),Rule).
  %\+member(simp(X,_),Rule).
simplify(X,Y,Rule,Depth,[P1|Path]):-
  Depth > 0,
  D1 is Depth - 1,
  \+var(X),
  \+is_list(X),
  get_member(simp(X1,Mid),Rule),
  copy_term(simp(X1,Mid),P1),
  X = X1,
  %member(simp(X1,Mid),Rule),
  %unify_with_occurs_check(X,X1),
  simplify(Mid,Y,Rule,D1,Path).
simplify(X,Y,Rule,Depth,Path):-
  \+var(X),
  \+is_list(X),
  X =.. [P|L1],
  simplify(L1,L2,Rule,Depth,Path),
  L1 \== L2,
  Y =.. [P|L2].
simplify([],[],_,_,[]).
simplify(L,[Y|L2],Rule,Depth,Path):-
  \+var(L),
  L = [X|L1],
  simplify(X,Y,Rule,Depth,P1),
  simplify(L1,L2,Rule,Depth,P2),
  append(P1,P2,Path).

*/

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

/*
rewrite_limited(_,_,_,Depth,_):-
  Depth < 0,
  !,
  fail.
rewrite_limited(X,X,_,_,[]):-
  var(X),
  !.
rewrite_limited(X,X,Rule,_,[]):-
  \+var(X),
  \+is_list(X),
  is_simplest(X,Rule),!.
rewrite_limited(X,X,_,Depth,[]):-
  Depth >= 0,
  \+var(X),
  \+is_list(X).
rewrite_limited(X,Y,Rule,Depth,[P1|Path]):-
  Depth > 0,
  D1 is Depth - 1,
  \+var(X),
  \+is_list(X),
  get_member(simp(X1,Mid),Rule),
  copy_term(simp(X1,Mid),P1),
  X = X1,
  %member(simp(X1,Mid),Rule),
  %unify_with_occurs_check(X,X1),
  rewrite_limited(Mid,Y,Rule,D1,Path).
rewrite_limited(X,Y,Rule,Depth,Path):-
  \+var(X),
  \+is_list(X),
  X =.. [P|L1],
  rewrite_limited(L1,L2,Rule,Depth,Path),
  L1 \== L2,
  Y =.. [P|L2].
rewrite_limited([],[],_,_,[]).
rewrite_limited(L,[Y|L2],Rule,Depth,Path):-
  \+var(L),
  L = [X|L1],
  rewrite_limited(X,Y,Rule,Depth,P1),
  rewrite_limited(L1,L2,Rule,Depth,P2),
  append(P1,P2,Path).


*/

% Simplify with reformation.
% simplify_with_reformation(Term,SimplifiedTerm,Rules,RepairedRules,MaximumCostOfRepairs,)

/*
simp_rule_reform(X,Tgt,RuleIn,RuleOut,NrMax,NrUsed):-
  \+var(X),
  \+is_list(X),
  get_member(simp(X1,Mid),RuleIn),
  (
    X = X1,
    (
      simp_rule_reform(Mid,Tgt,RuleIn,RuleOut,NrMax,NrUsed)
      ;
      simplify(Mid,Y1,RuleIn),
      Y1 \= Tgt,
      % Here
      reform(this_ruleRHS_eg_Mid,Mid1,Rs),
      repair(Rs,this_ruleRHS),
      update(RuleIn,Rs,RuleOut),
      % Here
      
    )
    ;
    X \= X1,
    


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
    simplify(Mid,Y,Rule2,RuleOut,Nr1,Nr2),
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
*/
% ----------------------------------------------------

simplify_with_reformation(X,X,Rule,Rule,_):-
  var(X),
  !.
simplify_with_reformation(X,X,Rule,Rule,_,0):-
  \+var(X),
  \+is_list(X),
  is_simplest(X,Rule),!.
  %\+member_with_occurs_check(simp(X,_),Rule).
  %\+member(simp(X,_),Rule).

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
  info(4,['unf_pair_is:']),
  info(4,X1),
  info(4,Y1),
  filter_rewrite(F),
  ccf_unblock_limited([X1=Y1],Nr,F,[],Rs,[X2=Y2]),
  info(4,['rs is: ',Rs]),
  reform_format_to_pred(X2,Vble2,X3),
  reform_format_to_pred(Y2,Vble2,Y3).

apply_repairs_to_pred(Rs,Pred,Res):-
  info(4,['apply repairs --- ',Pred,Rs]),
  pred_to_reform_format(Pred,P1,[],Vble1),
  info(4,['list format is: ',P1,Vble1]),
  info(4,['P2 now is: ',P2]),
  repairs(Rs,P1=P1,P2=_),
  info(4,['repaired list is: ',P2]),
  reform_format_to_pred(P2,Vble1,Res),
  info(4,['repaired pred is: ',Res]).

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
  atom_concat('id',N1,P1),
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
  %printByLine([x=X,y1=Y1,y2=Y2,p1=Path1,p2=Path2]),nl,
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
  % NumRepRule > 0,
  Nr > 0,
  get_member(simp(X,_),Rule),
  copy_term(X,Xt),
  reverse_simp_rule(Rule,RuleRev),
  simplify(X,Y1,Rule,FwdDepth,Path1),
  simplify(X,Y2,Rule,FwdDepth,Path2),
  Y1 \= Y2,
  copy_term(Y1,Yt),
  info(4,[not_common_tgt,Y1,Y2]),
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
  info(3,[notLC,RuleMid]),
    % N1 is NumRepRule - 1,
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
  info(3,['path is: ',Path]),
  first_n_elements(I,Path,Path1),
  rewrite_trace(X,T,Path1,I),
  info(4,['s -> t1 is: ',X,T]),
  \+member((T,_),TgtSet),

  info(3,['path1 is: ',I,Path1]),
  (
    append(Path2,[simp(P1,P2)],Path1),
    copy_term(T,Tt),
  info(3,['TgtSet is: ',TgtSet]),
  info(3,['fterm is: ',Tt]),
    setof(U,Pathv^member((U,Pathv),TgtSet),TgtSet1),
  info(4,['TgtSet1 is: ',TgtSet1]),
    get_member(V,TgtSet1),
  info(4,["Unifying ", Tt=V]),
    unify_with_reformation([Tt=V],Nr,_,Rs),
  info(4,["For ", Tt=V, 'Repair is: ',Rs,' to ',P2]),
    %\+illegal_repairs(Rs),
    apply_repairs_to_pred(Rs,P2,P4),
  info(4,['Repaird RHS is: ',P4]),
    remove_one_member(simp(P1,P2),Rule,Rule1),
    add_one_member(simp(P1,P4),Rule1,Rule2)
    ;
    fail, % Do not use this.
    get_member((V,Pathv),TgtSet),
    append(Path2,[simp(P1,P2)],Pathv),
    label_pred(P2,P3),
  info(3,[P2, ' renamed to: ',P3]),
    append(Path2,[simp(P1,P3)],Path4),
  info(3,['path4 is: ',Path4]),
    length(Path4,L4),
    rewrite_trace(Yt,Vt,Path4,L4),
  info(4,['TgtSet is: ',TgtSet]),
  info(3,['vterm is: ',Vt]),
    unify_with_reformation([Vt=T],Nr,_,Rs),
  info(4,["For ", Vt=T, 'Repair is: ',Rs,' to ',P3]),
    %\+illegal_repairs(Rs),
    apply_repairs_to_pred(Rs,P3,P4),
  info(4,['Repaird LHS is: ',P4]),
    remove_one_member(simp(P2,P1),Rule,Rule1),
    add_one_member(simp(P4,P1),Rule1,Rule2)
  ),

  legal_rules(Rule2),
  eliminate_duplicate_rules(Rule2,RuleOut),
  info(3,['Repaired Rules are: ',RuleOut]).

legal_rules(Rule):-
  \+member(simp(X,X),Rule).

eliminate_duplicate_rules(RuleIn,RuleOut):-
  setof(X,member(X,RuleIn),RuleOut),
  !.

first_n_elements(0,_,[]):-!.
first_n_elements(N,[X|L],[X|L1]):-
  N > 0,
  N1 is N - 1,
  first_n_elements(N1,L,L1).

% dif --- differentiation.
% ind_int --- indefinite integral.
% def_int --- definite integral.
% min --- minus.
% plu --- plus.
% mul --- multiply.

ont_arith(Ont):- Ont = [
  simp(plu(d0,d90),d90),
  simp(plu(d90,d0),d90),
  simp(plu(d90,d90),d180)

].

ont_sin(Ont):- Ont = [
  simp(sin(d0:d),0),
  simp(sin(d90:d),1),
  simp(sin(d180:d),0),
  simp(sin(d270:d),-1),
  simp(sin(plu(X:d,Y:d)),plu(mul(sin(X:d),cos(Y:d)),mul(cos(X:d),sin(Y:d)))),
  simp(sin(min(X:d,Y:d)),min(mul(sin(X:d),cos(Y:d)),mul(cos(X:d),sin(Y:d)))) 

].

simp_rule_revise(Rule,FwdDepth,BkwdDepth,MaxNr,Res,Rs):-
  for(Nr,1,MaxNr),
  simp_rule_reform(Rule,FwdDepth,BkwdDepth,Nr,Res,Rs),
  length(Rs,Nr).



ont_sin_test(L):- L = [
  sin(d0),
  dif(sin(X),X),
  dif(sin(d90),X)
].

ont_not_conf(L):- L = [
  simp(a,b),
  simp(a,c)
].


ont_not_conf_2(L):- L = [
  simp(a,b),
  simp(a,c),
  simp(a,d)
].

% Repair RHS
ont_not_conf_3_1(L):- L = [
  simp(a,e),
  simp(a,f),
  simp(e,x),
  simp(f,y)
].

% Repair LHS or RHS
ont_not_conf_3_2(L):- L = [
  simp(a,e),
  simp(a,f),
  simp(e,x),
  simp(g,x)
].



ont_not_conf_4(L):- L = [
  simp(dcos(X),sin(X)), % want sin(X) be sin(plu(X,d180))
  simp(sin(d90),n1),
  simp(dcos(d90),neg(n1)),
  simp(sin(plu(X,d180)),neg(sin(X))),
  simp(neg(sin(d90)),neg(n1))
].

ont_not_conf_5(L):- L = [
  simp(start,a(b,c(d,e))),
  simp(start,a(b(c,d),e)),
  simp(c(d,e),e),
  simp(b(c,e),b) %simp(b(c,d),b)
].


% Can work, but it requires significantly long time.

ont_ele_force_5(L):- L = [
  % Fe(q1,q2,r1,r2) => k*q1*q2*(r2-r1)/norm(r2-r1)^3
  simp(fe(Q1,Q2,vec(X1,Y1,Z1),vec(X2,Y2,Z2)),divi(mult(mult(mult(k,Q1),Q2),minu(vec(X2,Y2,Z2),vec(X1,Y1,Z1))),powe(norm(minu(vec(X2,Y2,Z2),vec(X1,Y1,Z1))),n3))),

  % Constant k => 9*10^9
  simp(k,n9e9),

  % Data fe => 9*10^9
  simp(fe(n1,n1,vec(n1,n0,n0),vec(n0,n0,n0)),vec(n9e9,n0,n0)),

  % -1*(v1-v2) => v2-v1
  % simp(neg(minu(V1,V2)),minu(V2,V1)),

  % Arithmetic
  /*simp(divi(mult(mult(mult(n9e9,n1),n1),minu(vec(n0,n0,n0),vec(n1,n0,n0))),powe(norm(minu(vec(n0,n0,n0),vec(n1,n0,n0))),n3)),neg(vec(n9e9,n0,n0))),
  simp(divi(mult(mult(mult(n9e9,n1),n1),minu(vec(n1,n0,n0),vec(n0,n0,n0))),powe(norm(minu(vec(n1,n0,n0),vec(n0,n0,n0))),n3)),vec(n9e9,n0,n0))*/

  % c*(x,y,z) => (c*x,c*y,c*z)
  simp(mult(C,vec(X,Y,Z)),vec(mult(C,X),mult(C,Y),mult(C,Z))),

  % (xa,ya,za)-(xb,yb,zb) => (xa-xb,ya-yb,za-zb)
  simp(minu(vec(Xa,Ya,Za),vec(Xb,Yb,Zb)),vec(minu(Xa,Xb),minu(Ya,Yb),minu(Za,Zb))),

  % x-0 => x
  simp(minu(X,d0),X),

  % x*1 => x , 1*x => x
  simp(mult(X,d1),X),
  simp(mult(d1,X),X),

  % x/1 => x
  simp(divi(X,d1),X),

  % ||(1,0,0)|| => 1
  simp(norm(vec(d1,d0,d0)),d1),

  % 1^X => 1
  simp(powe(d1,X),d1)

].


% Easy version.

ont_ele_force_5_easy(L):- L = [
  % Fe(q1,q2,r1,r2) => k*q1*q2*(r2-r1)/norm(r2-r1)^3
  simp(fe(Q1,Q2,vec(X1,Y1,Z1),vec(X2,Y2,Z2)),divi(mult(mult(mult(k,Q1),Q2),minu(vec(X2,Y2,Z2),vec(X1,Y1,Z1))),powe(norm(minu(vec(X2,Y2,Z2),vec(X1,Y1,Z1))),n3))),

  % Constant k => 9*10^9
  simp(k,n9e9),

  % Data fe => 9*10^9
  simp(fe(n1,n1,vec(n1,n0,n0),vec(n0,n0,n0)),vec(n9e9,n0,n0)),

  % -1*(v1-v2) => v2-v1
  % simp(neg(minu(V1,V2)),minu(V2,V1)),

  % Arithmetic
  simp(divi(mult(mult(mult(n9e9,n1),n1),minu(vec(n0,n0,n0),vec(n1,n0,n0))),powe(norm(minu(vec(n0,n0,n0),vec(n1,n0,n0))),n3)),neg(vec(n9e9,n0,n0))),
  simp(divi(mult(mult(mult(n9e9,n1),n1),minu(vec(n1,n0,n0),vec(n0,n0,n0))),powe(norm(minu(vec(n1,n0,n0),vec(n0,n0,n0))),n3)),vec(n9e9,n0,n0))

/*

  % c*(x,y,z) => (c*x,c*y,c*z)
  simp(mult(C,vec(X,Y,Z)),vec(mult(C,X),mult(C,Y),mult(C,Z))),

  % (xa,ya,za)-(xb,yb,zb) => (xa-xb,ya-yb,za-zb)
  simp(minu(vec(Xa,Ya,Za),vec(Xb,Yb,Zb)),vec(minu(Xa,Xb),minu(Ya,Yb),minu(Za,Zb))),

  % x-0 => x
  simp(minu(X,d0),X),

  % x*1 => x , 1*x => x
  simp(mult(X,d1),X),
  simp(mult(d1,X),X),

  % x/1 => x
  simp(divi(X,d1),X),

  % ||(1,0,0)|| => 1
  simp(norm(vec(d1,d0,d0)),d1),

  % 1^X => 1
  simp(powe(d1,X),d1)

*/

].

% Direct Current and Alternating Current.

ont_dc_vs_ac(L):- L = [

  % u = Usin(wt).
  simp(u(time(T),volt(U),angv(W)),mult(volt(U),sin(mult(angv(W),time(T))))),

  % i = u/C, faulty.
  simp(i(time(T),volt(U),angv(W)),divi(u(time(T),volt(U),angv(W)),cons(c))),
  % Wanted rule is:
  %simp(i(time(T),volt(U),angv(W)),mult(deri(u(time(T),volt(U),angv(W)),time(T)),cons(c1))),

  % When t = 0s, U = 5V, w = 0, i = 0A.
  % simp(i(n0,n5,n0),n0),

  % When t = 1s, U = 5V, w = w1 = pi/2, i = 0A.
  simp(i(time(n1),volt(n5),angv(w1)),curr(n0)),

  % When t = 1s, U = 5V, w = w2 = pi, i = -1A.
  simp(i(time(n1),volt(n5),angv(w2)),curr(neg(n1))),

  % d(Usin(wt)) / dt => wUcos(wt).
  simp(deri(mult(volt(U),sin(mult(angv(W),time(T))))/*,time(T)*/),mult(mult(cos(mult(angv(W),time(T))),angv(W)),volt(U))),

  % cos(w1) => 0
  %simp(type1(cos(mult(angv(w1),time(n1)))),curr(n0)),

  % cos(w2) => -1
  %simp(type1(cos(mult(angv(w2),time(n1)))),curr(neg(n1))),

  simp(mult(mult(mult(cos(mult(angv(w1),time(n1))),angv(w1)),volt(n5)),cons(c1)),curr(n0)),

  % c1*w2*5*cos(w2t) => cos(w2t), where c1 = -1 / 5 / pi.
  simp(mult(mult(mult(cos(mult(angv(w2),time(n1))),angv(w2)),volt(n5)),cons(c1)),curr(neg(n1)))

].




% Positive number and negative number.
/*

x + y = y + x
-x + -y = -y + -x

*/

% Real part and imaginary part.
/*

x + y = y + x
xi + yi = yi + xi

x * y = y * x
xi * yi = yi * xi

s(0) + s(0) => s(s(0))
i * s(0) + i * s(0) => i * s(i * s(0))

1 * 1 => 1
1i * 1i => 1i



*/

% Diss1.
% The first example of the dissertation.
% Run by ont_diss_1(Rule),simp_rule_reform(Rule,4,4,2,Res,Rs).
ont_diss_1(Rule):- Rule = [
  simp(plus(squ(cos(X)),squ(sin(X))),n1),
  simp(der(cos(x),X),sin(X)),
  simp(der(cos(x),divi(pi,n2)),neg(n1)),
  simp(sin(divi(pi,n2)),n1),
  simp(cos(divi(pi,n2)),n0),
  simp(plus(squ(n0),squ(n1)),n1)
].

% Diss2.
% The example of List and BTree in the dissertation.
% Run by ont_diss_2(Rule),simp_rule_reform(Rule,3,3,5,Res,Rs),member(merge(_,plus),Rs).

ont_diss_2(Rule):- Rule = [
  %simp(nat(size(btree(node(lab(V),btree(L),btree(R))))),nat(succ(nat(plus(nat(size(btree(L))),nat(size(btree(R)))))))),
  %simp(nat(size(btree(L))),nat(n1))
  
  %simp(size(node(V,L,R)),succ(plus(size(L),size(R)))),
  simp(size(node(V,L,R)),succ(size(L))),
  simp(size(node(b,leaf(c),leaf(d))),n3),
  simp(size(leaf(V)),n1),
  %simp(size(leaf(V)),n0),
  simp(succ(plus(n1,n1)),n3)
].



% ont_sin(Rule),ont_sin_test(L),member(X,L),simplify(X,Y,Rule).
