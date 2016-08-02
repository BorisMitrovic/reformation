% The example 9.3 on pp.34-35 of the paper.

% USAGE: In SWI-Prolog, run:
% notrace,[diagnose,repair,util,reform,revise,utilRevise,extralib,upgrade,example_upgrade].
% and run:
% example_upgrade(Res).

example_upgrade(Res):-

  % The upper limit of the cost of repair.
  Nr = 3,

  % The depth of resolution.
  D = 5,

  % T is a theory. G is a goal (or some goals).
  % They should be in conjunctive normal form.
  % +p means p is true. -p means p is false.
  % p /\ q ==> r can be written as [-p,-q,+r].
  % Variables should be written as vble(..).

  % The example 9.3 on pp.34-35 of the paper.

  T = [
    [+stepmum(camilla,william)],
    [-stepmum(vble(p),vble(c)),+parent(vble(p),vble(c))]
  ],

  G = [
    +parent2(camilla,william,step)
  ],

  /*
  % A test example.

  T = [
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

  G = [
    % The goal is s.
    +s
  ],
  */

  /*
  % Making (3 + 2) + 1 ==> 6.

  T = [
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
  G = [
    +six
  ],
  */

  % Transform the theory and the goal(s) to a list format.
  trans_to_list(G,GIn),
  trans_theory_to_list(T,TIn),

  % Upgrade.
  upgrade(GIn,TIn,Tr,Rs,TOut,Nr,D),

  % Print the results.
  trans_theory_to_pred(TOut,Tp),
  nl,printByLine(['The original theory is:'|T]),
  nl,printByLine(['The goal is:'|G]),
  nl,printByLine(['Repairs are:'|Rs]),
  nl,printByLine(['The repaired theory is:'|Tp]),nl,

  Res = Tp.


