% Examples for the "redirect" algorithm.
% Chenghao Cai. 18th August, 2016.

% USAGE: In SWI-Prolog, run:
% notrace,[diagnose,repair,util,reform,revise,utilRevise,extralib,redirect,example_redirect].
% Then run different examples by using the command above each example. For instance: ont_diss_1(Rule),redirect(Rule,4,4,2,Res,Rs).


% The sin and cos example of the dissertation.
% Run by: ont_diss_1(Rule),redirect(Rule,4,4,2,Res,Rs).
ont_diss_1(Rule):- Rule = [
  simp(plus(squ(cos(X)),squ(sin(X))),n1),
  simp(der(cos(x),X),sin(X)),
  simp(der(cos(x),divi(pi,n2)),neg(n1)),
  simp(sin(divi(pi,n2)),n1),
  simp(cos(divi(pi,n2)),n0),
  simp(plus(squ(n0),squ(n1)),n1)
].

% Second order case.
% Run by: ont_diss_1_2nd(Rule),redirect(Rule,4,4,3,Res,Rs).
ont_diss_1_2nd(Rule):- Rule = [
  simp(l2(l2(der, cos), X), l2(sin, X)),
  simp(l2(l2(der, cos),l2(divi, pi, n2)), l2(neg, n1)),
  simp(l2(sin, l2(divi, pi, n2)), n1)
].

% The example of List and BTree in the dissertation.
% Run by: ont_diss_2(Rule),redirect(Rule,7,2,2,Res,Rs),member(addfunc(_,_,plus,_),Rs).

ont_diss_2(Rule):- Rule = [
  simp(size(empty),n0),
  simp(size(node(V,L,R)),succ(size(L))),
  simp(size(node(a,empty,node(a,empty,empty))),succ(succ(n0))),
  simp(plus(X,n0),X),
  simp(plus(X,succ(Y)),succ(plus(X,Y)))
].

% Diss 3.
% Gravity and EleForce.

% Run by: ont_ele_force_5(Rule),redirect(Rule,4,4,2,Res,Rs).

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
  simp(divi(mult(mult(mult(n9e9,n1),n1),minu(vec(n0,n0,n0),vec(n1,n0,n0))),powe(norm(minu(vec(n0,n0,n0),vec(n1,n0,n0))),n3)),neg(vec(n9e9,n0,n0))),
  simp(divi(mult(mult(mult(n9e9,n1),n1),minu(vec(n1,n0,n0),vec(n0,n0,n0))),powe(norm(minu(vec(n1,n0,n0),vec(n0,n0,n0))),n3)),vec(n9e9,n0,n0))
].


% Run by: ont_ele_force_5_2(Rule),redirect(Rule,4,4,4,Res,Rs),member(merge(n667,n899,left),Rs).

ont_ele_force_5_2(L):- L = [

  % Fe(q1,q2,r1,r2) => k*q1*q2*(r2-r1)/norm(r2-r1)^3
  simp(fe(Q1,Q2,vec(X1,Y1,Z1),vec(X2,Y2,Z2)),divi(mult(mult(mult(k,Q1),Q2),minu(vec(X2,Y2,Z2),vec(X1,Y1,Z1))),powe(norm(minu(vec(X2,Y2,Z2),vec(X1,Y1,Z1))),n3))),

  % Constant k => 9*10^9
  simp(k,mult(n667,powe(n10,neg(n11)))),
  % simp(k,n9000000000),
  % Data fe => 9*10^9
  simp(fe(n0p00000004,n0p00000004,vec(n0p1,n0,n0),vec(n0,n0,n0)),vec(n0p0144,n0,n0)),
  simp(divi(mult(mult(mult(mult(n899,powe(n10,n9)),n0p00000004),n0p00000004),minu(vec(n0,n0,n0),vec(n0p1,n0,n0))),powe(norm(minu(vec(n0,n0,n0),vec(n0p1,n0,n0))),n3)),neg(divi(mult(mult(mult(mult(n899,powe(n10,n9)),n0p00000004),n0p00000004),minu(vec(n0p1,n0,n0),vec(n0,n0,n0))),powe(norm(minu(vec(n0p1,n0,n0),vec(n0,n0,n0))),n3)))),
  simp(divi(mult(mult(mult(mult(n899,powe(n10,n9)),n0p00000004),n0p00000004),minu(vec(n0p1,n0,n0),vec(n0,n0,n0))),powe(norm(minu(vec(n0p1,n0,n0),vec(n0,n0,n0))),n3)),vec(n0p0144,n0,n0))

].




% Failed example.

% Direct Current and Alternating Current.

% Run by:
% ont_dc_vs_ac(Rule),redirect(Rule,7,7,5,Res,Rs),member(simp(i(time(T),volt(U),angv(W)),mult(deri(u(time(T),volt(U),angv(W))),cons(c1))),Res).

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


ont_dc_vs_ac_typed(L):- L = [

  % u = Usin(wt).
  simp(volt(u(time(T),volt(U),angv(W))),num(mult(volt(U),num(sin(num(mult(angv(W),time(T)))))))),

  % i = u/C, faulty.
  simp(curr(i(time(T),volt(U),angv(W))),num(divi(volt(u(time(T),volt(U),angv(W))),num(c)))),
  % Wanted rule is:
  %simp(i(time(T),volt(U),angv(W)),mult(deri(u(time(T),volt(U),angv(W)),time(T)),cons(c1))),

  % When t = 0s, U = 5V, w = 0, i = 0A.
  % simp(i(n0,n5,n0),n0),

  % When t = 1s, U = 5V, w = w1 = pi/2, i = 0A.
  simp(curr(i(time(n1),volt(n5),angv(w1))),curr(num(n0))),

  % When t = 1s, U = 5V, w = w2 = pi, i = -1A.
  simp(curr(i(time(n1),volt(n5),angv(w2))),curr(num(neg(num(n1))))),

  % d(Usin(wt)) / dt => wUcos(wt).
  simp(num(deri(num(mult(volt(U),num(sin(num(mult(angv(W),time(T)))))))/*,time(T)*/)),num(mult(num(mult(num(cos(num(mult(angv(W),time(T))))),angv(W))),volt(U)))),

  % cos(w1) => 0
  %simp(type1(cos(mult(angv(w1),time(n1)))),curr(n0)),

  % cos(w2) => -1
  %simp(type1(cos(mult(angv(w2),time(n1)))),curr(neg(n1))),

  simp(num(mult(num(mult(num(mult(num(cos(num(mult(angv(w1),time(n1))))),angv(w1))),volt(n5))),num(c1))),curr(num(n0))),

  % c1*w2*5*cos(w2t) => cos(w2t), where c1 = -1 / 5 / pi.
  simp(num(mult(num(mult(num(mult(num(cos(num(mult(angv(w2),time(n1))))),angv(w2))),volt(n5))),num(c1))),curr(num(neg(num(n1)))))

].


