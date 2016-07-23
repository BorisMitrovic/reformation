% The example 9.3 on pp.34-35 of the paper.

% USAGE: In SWI-Prolog, run:
% notrace,[diagnose,repair,util,reform,revise,utilRevise,info,story,rewrite,filter,example_unblocking].
% and run:
% example_9_3.

example_9_3:-

  % The upper limit of the cost of repair.
  Nr = 10,

  % Filter. See filter.pl.
  filter1(F),

  % Y is a goal. Ax is an axiom.
  % Variables should be written as vble(..).
  Y = parent2(camilla,william,step),
  Ax = implies(stepmum(vble(p),vble(c)),parent(vble(p),vble(c))),

  % Unblock Y and the RHS of Ax. Reps are suggested repairs
  Ax = implies(_,X),
  pred_to_list(X,P),
  pred_to_list(Y,Q),
  ccf_unblock_limited([P=Q],Nr,F,[],Rs,Res),
  findall(R,(member(R,Rs),\+R=(substitute(_,_))),Reps),

  % Apply the repairs to Ax. Ax1 is the resulting axiom.
  pred_to_list(Ax,U),
  repairall(Reps,[U=[nothing]],[U1=[nothing]]),
  list_to_pred(U1,Ax1),

  % Check if Y and the RHS of Ax1 can be unified.
  Ax1 = implies(_,X1),
  pred_to_list(X1,P1),
  ccf_unblock_limited([P1=Q],Nr,F,[],Rs1,Res1),
  findall(R,(member(R,Rs1),\+R=(substitute(_,_))),[]),

  % Output the result.
  nl,printByLine(['Repairs are:'|Reps]),
  nl,printByLine(['The repaired axiom is:'|[Ax1]]),nl.

