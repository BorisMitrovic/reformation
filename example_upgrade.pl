% Examples for the "upgrade" algorithm.
% Chenghao Cai. 18th August, 2016.

% USAGE: In SWI-Prolog, run:
% notrace,[diagnose,repair,util,reform,revise,utilRevise,extralib,upgrade,example_upgrade].
% example_upgrade(Res).

example_upgrade(Res):-

  % The upper limit of the cost of repair.
  Nr = Nr3, % Nr1|Nr2|Nr3|Nr4|Nr5|Nr6

  % The depth of resolution.
  D = D3, % D1|D2|D3|D4|D5|D6

  T = T3, % T1|T2|T3|T4|T5|T6

  G = G3, % G1|G2|G3|G4|G5|G6

  % T is a theory. G is a goal (or some goals).
  % They should be in conjunctive normal form.
  % +p means p is true. -p means p is false.
  % p /\ q ==> r can be written as [-p,-q,+r].
  % Variables should be written as vble(..).
  % The goal should be negated. i.e. A goal g is written as -g.

  Nr1 = 4, D1 = 5,

  % List and BTree.

  T1 = [

    % Axioms.
    [-size(empty),+n0],
    [-size(node(vble(h),vble(l),vble(r))),+succ(size(vble(l)))],

    % Premise.
    [+size(node(a,node(a,empty,empty),node(a,empty,empty)))],

    [-plus(n0,vble(x)),+vble(x)],
    [-plus(succ(vble(x)),vble(y)),+succ(plus(vble(x),vble(y)))]

  ],

  G1 = [
    -succ(succ(succ(n0)))
  ],

  % List and BTree again. 

  Nr2 = 2, D2 = 5,

  T2 = [

    % Axioms.
    [-size(empty),+n0],
    [-size(node(vble(h),vble(l),vble(r))),+succ(size(vble(l)))],

    % Premise.
    [+size(node(a,node(a,empty,empty),node(a,empty,empty)))],

    [-plus(n0,vble(x)),+vble(x)],
    [-plus(succ(vble(x)),vble(y)),+succ(plus(vble(x),vble(y)))],

    % Extra.
    [-succ(plus(size(node(a,empty,empty)),size(node(a,empty,empty)))),+succ(plus(succ(n0),succ(n0)))],
    [-succ(plus(succ(n0),succ(n0))),+succ(succ(succ(n0)))]

  ],

  G2 = [
    -succ(succ(succ(n0)))
  ],


  % Addition and subtraction example.

  Nr3 = 1, D3 = 3,

  T3 = [

    % Axioms.
    %[-plus(vble(x),n0),vble(x)],
    %[-plus(vble(x),succ(vble(y))),+succ(plus(vble(x),vble(y)))],
    %[-pred(minus(vble(x),n0)),+pred(vble(x))],
    %[-minus(vble(x),pred(vble(y))),+pred(minus(vble(x),vble(y)))],
    
    [-l2(vble(p), l2(minus, vble(x), n0)), +l2(vble(p), vble(x))],
    [-l2(minus, vble(x1), n0), +vble(x1)],
    [-l2(minus, vble(x), l2(pred, vble(y))), +l2(pred, l2(minus, vble(x),vble(y)))],

    % Premise.
    [+l2(minus, n0, l2(pred, n0))]
  ],

  G3 = [
    -l2(succ, n0)
  ],


  % SelfLove example. This example is from [Bundy, A. and Mitrovic, B. (2016). Reformation: A domain-independent algorithm for theory repair. Technical report, the University of Edinburgh.]

  Nr4 = 2, D4 = 2,

  T4 = [
    [+loves(vble(y),love_of(vble(y)))]
     %[+loves(vble(x))]
  ],

  G4 = [
    -loves(vble(x),vble(x))
    %-loves(love_of(vble(x)))
  ],

  % A test example.

  Nr5 = 3, D5 = 5,

  T5 = [
    % a is true.
    [+a],
    % b is true.
    [+b],
    % a ==> p.
    [-a,+p],
    % b ==> q.
    [-b,+q],
    % c ==> r.
    [-c,+r],
    % p /\ q /\ r ==> s.
    [-p,-q,-r,+s]
  ],

  G5 = [
    % The goal is s.
    -s
  ],


  % Making (3 + 2) + 1 ==> 6.

  Nr6 = 3, D6 = 5,

  T6 = [
    % The original expression is (3 + 2) + 1.
    [+plus(plus(three,two),one)],
    % forall a,b,c. (a + b) + c ==> a + (b + c).
    [-plus(plus(vble(a),vble(b)),vble(c)),+plus(vble(a),plus(vble(b),vble(c)))],
    % forall a,b,c. a + (b + c) ==> a + (c + b).
    [-plus(vble(a),plus(vble(b),vble(c))),+plus(vble(a),plus(vble(c),vble(b)))],
    % forall a. a + (2 + 1) ==> a + 4.
    % It is faulty. 4 should be changed to 3.
    [-plus(vble(a),plus(two,one)),+plus(vble(a),four)],
    % 3 + 3 ==> 6.
    [-plus(three,three),+six]
  ],

  % The original expression is (3 + 2) + 1.
  % The goal is 6.
  G6 = [
    -six
  ],

  % Transform the theory and the goal(s) to a list format.
  trans_to_list(G,GIn),
  trans_theory_to_list(T,TIn),

  % Upgrade.
  upgrade(GIn,TIn,Nr,D,TOut,Rs),

  % Print the results.
  trans_theory_to_pred(TOut,Tp),
  nl,printByLine(['The original theory is:'|T]),
  nl,printByLine(['The goal is:'|G]),
  nl,printByLine(['Repairs are:'|Rs]),
  nl,printByLine(['The repaired theory is:'|Tp]),nl,

  Res = Tp.


