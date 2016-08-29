% Examples for the "align" algorithm.
% Chenghao Cai. 18th August, 2016.

% USAGE: In SWI-Prolog, run:
% notrace,[diagnose,repair,util,reform,revise,utilRevise,extralib,align,example_align].
% example_align(Rs,B).

example_align(Rs,B):-

  % Select an example.
  Nr = Nr2, % Nr1|Nr2|Nr3|Nr4|Nr5
  S = S2, % S1|S2|S3|S4|S5
  T = T2, % T1|T2|T3|T4|T5



  % List vs BTree Example.

  Nr1 = 6,

  S1 = [

    % Types
    list(nil),
    list(cons(el(vble(v1)),list(vble(v2)))),
    nat(length(list(vble(v3)))),

    nat(n0),
    nat(succ(nat(vble(v4)))),
    nat(plus(nat(vble(v4a)),nat(vble(v4b)))),

    % Axioms
    simp(length(nil),n0),
    simp(length(cons(vble(h),vble(ll))),succ(length(vble(ll)))),

    simp(plus(n0,vble(x)),vble(x)),
    simp(plus(succ(vble(x)),y),succ(plus(vble(x),vble(y))))

  ],

  % BTree 1 - strong.
  Nr1s = 6,
  T1s = [
    % Types
    val(a),
    btree(leaf(val(vble(v5)))),
    btree(node(val(vble(v6)),btree(vble(v7)),btree(vble(v8)))),
    nat(size(btree(vble(v9)))),
    nat(succ(nat(vble(v10)))),
    nat(plus(nat(vble(v11)),nat(vble(v12)))),
    
    % Axioms
    simp(size(leaf(a)),succ(n0)),
    simp(plus(succ(n0),succ(n0)),succ(succ(succ(n0))))
  ],

  % BTree 1.
  T1 = [
    % Types
    % val(a),
    btree(empty),
    btree(node(val(vble(v6)),btree(vble(v7)),btree(vble(v8)))),
    nat(size(btree(vble(v9)))),

    nat(n0),
    nat(succ(nat(vble(v10)))),
    nat(plus(nat(vble(v11)),nat(vble(v12)))),
    
    % Axioms
    %simp(size(empty),n0),
    simp(size(node(a,empty,node(a,empty,empty))),succ(succ(n0))),
    %simp(succ(plus(n0,succ(n0))),succ(succ(n0)))

    simp(plus(n0,vble(x)),vble(x)),
    simp(plus(succ(vble(x)),y),succ(plus(vble(x),vble(y))))

  ],


  % Foodchain Example.

  Nr2 = 3,

  S2 = [
    eat(eagle,mouse),
    eat(eagle,snake),
    eat(snake,mouse),
    eat(cat,mouse),
    eat(cat,dove)
  ],

  T2 = [
    is_eaten_by(mouse,cat,alice),
    is_eaten_by(dove,cat,bob),
    is_eaten_by(mouse,owl,bob)
  ],



  % Nat + List.

  Nr3 = 2,

  S3 = [
    % forall x:Nat. sum(s(x)) = plus(s(x),sum(x))
    equal(rev(s(vble(xs1))),app(s(vble(xs1)),rev(vble(xs1)))),

    % forall x,y:Nat. qsum(s(x),y) = qsum(x,plus(s(x),y))
    equal(qrev(s(vble(xs2)),vble(ys2)),qrev(vble(xs2),app(s(vble(xs2)),vble(ys2)))),

    % forall x,y:Nat. plus(s(x),y) = s(plus(x,y))
    equal(app(s(vble(xs5)),vble(ys5)),s(app(vble(xs5),vble(ys5)))),

    % forall x,y:Nat. plus(sum(x),y) = qsum(x,y)
    equal(app(rev(vble(xs7)),vble(ys7)),qrev(vble(xs7),vble(ys7)))

  ],

  T3 = [
    % forall x,y:L;h:El. app(cons(h,x),y) = cons(h,app(x,y))
   equal(app(cons(vble(ht1),vble(xt1)),vble(yt1)),cons(vble(ht1),app(vble(xt1),vble(yt1)))),

    % forall x:L;h:El. rev(cons(h,x)) = app(rev(x),cons(h,nil))
    equal(rev(cons(vble(ht3),vble(xt3))),app(rev(vble(xt3)),cons(vble(ht3),nil))),

    % forall x,y:L;h:El. qrev(cons(h,x),y) = qrev(x,cons(h,y))
    equal(qrev(cons(vble(ht5),vble(xt5)),vble(yt5)),qrev(vble(xt5),cons(vble(ht5),vble(yt5))))
  ],



  % C vs Pascal --- Blast.

  % lb --- left bracket
  % rb --- right bracket
  % ps --- percent sign
  % ad --- address sign
  % sc --- semicolon
  % dq --- double quotation mark
  % cm --- comma
  % newl --- \n
  % cl --- colon

  Nr4 = 9,

  S4 = [
    %pattern_c1(scanf,lb,ad,x,rb), % -5
    %pattern_c1(scanf,lb,ad,y,rb), % -5
    %pattern_c1(scanf,lb,dq,ps,d,dq,cm,ad,x,rb),
    %pattern_c1(scanf,lb,dq,ps,d,dq,cm,ad,y,rb)
    %pattern_c2(printf,lb,dq,ps,d,newl,dq,cm,z,rb),
    %pattern_c3(z,equal,x,minus,y)
    pascal_1(read_p,lb,x,rb),
    pascal_1(read_p,lb,y,rb),
    pascal_2(s,cn,equal,x,plus,y),
    pascal_3(writeln,lb,s,rb),

    pascal_2(s,cn,equal,x,minus,y),
    pascal_3(writeln,lb,s,rb),
    pascal_2(s,cn,equal,x,mult,y),
    pascal_3(writeln,lb,s,rb),
    pascal_2(s,cn,equal,x,divi,y),
    pascal_3(writeln,lb,s,rb)

  ],

  T4 = [
    python_1(x,equal,input,lb,rb),
    python_1(y,equal,input,lb,rb),
    python_2(s,equal,x,plus,y),
    python_3(print_p,lb,s,rb)
  ],



  % Pascal vs Python.
  Nr5 = 12,

  S5 = [
    read_p(x,c),
    read_p(y,c),
    %writeln(plus(x,y)),
    print_p(mult(x,y)),
    %cnequal(s,n0),
    for_to_do(i,to(x,y),do(equal(s,plus(s,i)))),
    %writeln(s),
    equal(t,n1),
    for_to_do(i,to(x,y),do(equal(t,mult(t,i)))),
    print_p(t)
  ],

  T5 = [
    equal(x,input),
    equal(y,input),
    %print_p(plus(x,y)),
    %equal(s,n0),
    for_in(i,xrange(x,plus(y,n1)),exec(equal(s,plus(s,i))))
    %print_p(s)
  ],

  trans_all_to_list(S,SList),
  trans_all_to_list(T,TList),
  align(SList,TList,Nr,BList,Rs),
  trans_all_to_pred(BList,B),

  nl,printByLine(['Repairs are:'|Rs]),
  nl,printByLine(['The repaired blend is:'|B]),nl.
    
