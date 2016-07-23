% Development Set

% smaill_nat.dol vs smaill_list.dol

nat1_vs_list1(X, Y):-

% Start of the source theory.

  % forall x,y:Nat. plus(s(x),y) = s(plus(x,y))
  X = equal(app(s(vble(xs5)),vble(ys5)),s(app(vble(xs5),vble(ys5)))),

  % forall x,y:L;h:El. app(cons(h,x),y) = cons(h,app(x,y))
  Y = equal(app(cons(vble(ht1),vble(xt1)),vble(yt1)),cons(vble(ht1),app(vble(xt1),vble(yt1)))).


% Nat-4 vs List-3. No type.
% S1 vs Tnew1
% S2 vs Tnew2
% S3 vs T1
% S4 vs Tnew3
% Snew1 vs T2
% Snew2 vs T3

nat4_vs_list3(Source, Target):-

% Start of the source theory.
Source = source_theory(

  % forall x:Nat. sum(s(x)) = plus(s(x),sum(x))
  equal(rev(s(vble(xs1))),app(s(vble(xs1)),rev(vble(xs1)))),

  % forall x,y:Nat. qsum(s(x),y) = qsum(x,plus(s(x),y))
  equal(qrev(s(vble(xs2)),vble(ys2)),qrev(vble(xs2),app(s(vble(xs2)),vble(ys2)))),

  % forall x,y:Nat. plus(s(x),y) = s(plus(x,y))
  equal(app(s(vble(xs5)),vble(ys5)),s(app(vble(xs5),vble(ys5)))),

  % forall x,y:Nat. plus(sum(x),y) = qsum(x,y)
  equal(app(rev(vble(xs7)),vble(ys7)),qrev(vble(xs7),vble(ys7))),

  % New Axioms
  vble(newAx1),
  vble(newAx2)

),
% End of the source theory.

% Start of the target theory.
Target = target_theory(

  % forall x,y:L;h:El. app(cons(h,x),y) = cons(h,app(x,y))
  equal(app(cons(vble(ht1),vble(xt1)),vble(yt1)),cons(vble(ht1),app(vble(xt1),vble(yt1)))),

  % forall x:L;h:El. rev(cons(h,x)) = app(rev(x),cons(h,nil))
  equal(rev(cons(vble(ht3),vble(xt3))),app(rev(vble(xt3)),cons(vble(ht3),nil))),

  % forall x,y:L;h:El. qrev(cons(h,x),y) = qrev(x,cons(h,y))
  equal(qrev(cons(vble(ht5),vble(xt5)),vble(yt5)),qrev(vble(xt5),cons(vble(ht5),vble(yt5)))),

  % New Axioms
  vble(newAx3),
  vble(newAx4),
  vble(newAx5)
 
).
% End of the target theory.

/*

% Full version.

smaill_full(Source, Target):-

% Start of the source theory.
Source = source_theory(

  % Axs0 |-> Axt2 : sum(0) = 0
  equal(sum(0),0),

  % Axs1 //-> Axt3 : forall x:Nat. sum(s(x)) = plus(s(x),sum(x))
  equal(sum(s(xs1)),plus(s(xs1),sum(xs1))),

  % Axs2 |-> Axt5 : forall x,y:Nat. qsum(s(x),y) = qsum(x,plus(s(x),y))
  equal(qsum(s(xs2),ys2),qsum(xs2,plus(s(xs2),ys2))),

  % Axs3 |-> Axt4 : forall x:Nat. qsum(0,x) = x
  equal(qsum(0,xs3),xs3),

  % Axs4 |-> Axt0 : forall x:Nat. plus(0,x) = x
  equal(plus(0,xs4),xs4),

  % Axs5 |-> Axt1 : forall x,y:Nat. plus(s(x),y) = s(plus(x,y))
  equal(plus(s(xs5),ys5),s(plus(xs5,ys5))),

  % Axs6 |-> Axt6: forall x: Nat. sum(x) = qsum(x,0)
  equal(sum(xs6),qsum(xs6,0)),

  % Axs7: forall x,y:Nat. plus(sum(x),y) = qsum(x,y)
  equal(plus(sum(xs7),ys7),qsum(xs7,ys7)),

  % New Axioms
  vble(newAx1)

),
% End of the source theory.

% Start of the target theory.
Target = target_theory(

  % Axt0: forall x: L. app(nil,x) = x
  equal(app(nil,xt0),xt0),

  % Axt1: forall x,y:L;h:El. app(cons(h,x),y) = cons(h,app(x,y))
  equal(app(cons(ht1,xt1),yt1),cons(ht1,app(xt1,yt1))),

  % Axt2: rev(nil) = nil
  equal(rev(nil),nil),

  % Axt3: forall x:L;h:El. rev(cons(h,x)) = app(rev(x),cons(h,nil))
  equal(rev(cons(ht3,xt3)),app(rev(xt3),cons(ht3,nil))),

  % Axt4: forall x:L. qrev(nil,x) = x
  equal(qrev(nil,xt4),xt4),

  % Axt5: forall x,y:L;h:El. qrev(cons(h,x),y) = qrev(x,cons(h,y))
  equal(qrev(cons(ht5,xt5),yt5),qrev(xt5,cons(ht5,yt5))),

  % Axt6: forall x:L. rev(x) = qrev(x,nil);
  equal(rev(xt6),qrev(xt6,nil))
  
).
% End of the target theory.

*/


