%cch Remove duplicated repairs.
removeDuplicatedRepairs([],[]):-!.
removeDuplicatedRepairs([X|L],R1):-
    member(X,L),
    removeDuplicatedRepairs(L,R1),!.
removeDuplicatedRepairs([X|L],[X|R1]):-
    removeDuplicatedRepairs(L,R1),!.

%cch
prtinf(X):-
  print("HERE: "),
  print(X),nl.
printByLine([]).
printByLine([X|L]):-
  print(X),nl,
  printByLine(L).


test1(X):-
  X = 
[

  [
    ps_equal:ss_Sym,
    [
      ps_plus:ss_Nat,
      [cs_0:ss_Nat],
      vble(vs_x:ss_Nat)
    ],
    vble(vs_x:ss_Nat)
  ]
  = 
  [
    pt_equal:st_Sym,
    [
      pt_app:st_List,
      [ct_nil:st_List],
      vble(vt_x:st_List)
    ],
    vble(vt_x:st_List)
  ]

].


test2(X):-
  X = 
[

  [
    ps_equal:ss_Sym,
    [
      ps_plus:ss_Nat,
      [cs_1:ss_Nat],
      vble(vs_x:ss_Nat)
    ],
    [
      ps_succ:ss_Nat,
      vble(vs_x:ss_Nat)
    ]
  ]
  =
  [
    pt_equal:st_Sym,
    [
      pt_app:st_List,
      [
        pt_cons:st_List,
        vble(vt_e:st_El),
        [ct_nil:st_List]
      ],
      vble(vt_x:st_List)
    ],
    [
      pt_cons:st_List,
      vble(vt_e:st_El),
      vble(vt_x:st_List)
    ]
  ]

].


test1_novble(X):-
  X = 
[

  [
    ps_equal:ss_Sym,
    [
      ps_plus:ss_Nat,
      [cs_0:ss_Nat],
      [vs_x:ss_Nat]
    ],
    vble(vs_x:ss_Nat)
  ]
  = 
  [
    pt_equal:st_Sym,
    [
      pt_app:st_List,
      [ct_nil:st_List],
      [vt_x:st_List]
    ],
    vble(vt_x:st_List)
  ]

].




story1(X):-
  X = 
[

  [
    ps_equal,
    [
      ps_plus,
      [cs_0],
      vble(vs_x)
    ],
    vble(vs_x)
  ]
  = 
  [
    pt_equal,
    [
      pt_app,
      [ct_nil],
      vble(vt_x)
    ],
    vble(vt_x)
  ]

  ,

  [
    ps_equal,
    [
      ps_plus,
      [cs_1],
      vble(vs_x)
    ],
    [
      ps_succ,
      vble(vs_x)
    ]
  ]
  =
  [
    pt_equal,
    [
      pt_app,
      [
        pt_cons,
        vble(vt_e),
        [ct_nil]
      ],
      vble(vt_x)
    ],
    [
      pt_cons,
      vble(vt_e),
      vble(vt_x)
    ]
  ]

].

story1_sorted(X):-
  X = 
[

  [
    ps_equal:ss_Sym,
    [
      ps_plus:ss_Nat,
      [cs_0:ss_Nat],
      vble(vs_x:ss_Nat)
    ],
    vble(vs_x:ss_Nat)
  ]
  = 
  [
    pt_equal:st_Sym,
    [
      pt_app:st_List,
      [ct_nil:st_List],
      vble(vt_x:st_List)
    ],
    vble(vt_x:st_List)
  ]

  ,

  [
    ps_equal:ss_Sym,
    [
      ps_plus:ss_Nat,
      [cs_1:ss_Nat],
      vble(vs_x:ss_Nat)
    ],
    [
      ps_succ:ss_Nat,
      vble(vs_x:ss_Nat)
    ]
  ]
  =
  [
    pt_equal:st_Sym,
    [
      pt_app:st_List,
      [
        pt_cons:st_List,
        vble(vt_e:st_El),
        [ct_nil:st_List]
      ],
      vble(vt_x:st_List)
    ],
    [
      pt_cons:st_List,
      vble(vt_e:st_El),
      vble(vt_x:st_List)
    ]
  ]

].


story2(X):-
  X = 
[
  [
    ps_equal,
    [
      ps_plus,
      [cs_1],
      vble(vs_x)
    ],
    [
      ps_succ,
      vble(vs_x)
    ]
  ]
  =
  [
    pt_equal,
    [
      pt_app,
      [
        pt_cons,
        vble(vt_e),
        [ct_nil]
      ],
      vble(vt_x)
    ],
    [
      pt_cons,
      vble(vt_e),
      vble(vt_x)
    ]
  ]

].

story3(X):-
  X = 
[

  [
    s_equal,
    [
      s_plus,
      [s_0],
      vble(s_x)
    ],
    vble(s_x)
  ]
  = 
  [
    t_equal,
    [
      t_app,
      [t_nil],
      vble(t_x)
    ],
    vble(t_x)
  ]

  ,

  [
    s_equal,
    [
      s_plus,
      [
        s_succ,
        vble(s_x)
      ],
      vble(s_y)
    ],
    [
      s_succ,
      [
        s_plus,
        vble(s_x),
        vble(s_y)
      ]
    ]
  ]
  =
  [
    t_equal,
    [
      t_app,
      [
        t_cons,
        vble(t_h),
        vble(t_x)
      ],
      vble(t_y)
    ],
    [
      t_cons,
      vble(t_h),
      [
        t_app,
        vble(t_x),
        vble(t_y)
      ]
    ]
  ]

].

story4(X,S):-
  S = 
[
  (bot -> s_Nat),
  (s_Nat -> top),
  (bot -> t_L),
  (t_L -> top),
  (bot -> s_El),
  (s_El -> top)
],
  X = 
[

  [
    s_equal,
    [
      s_plus,
      [s_0]:sort(s_Nat),
      vble(s_X1):sort(s_Nat)
    ]:sort(s_Nat),
    vble(s_X1):sort(s_Nat)
  ]:sort(top)
  = 
  [
    t_equal,
    [
      t_app,
      [t_nil]:sort(t_L),
      vble(t_X4):sort(t_L)
    ]:sort(t_L),
    vble(t_X4):sort(t_L)
  ]:sort(top)

  ,

  [
    s_equal,
    [
      s_plus,
      [
        s_succ,
        vble(s_X2):sort(s_Nat)
      ]:sort(s_Nat),
      vble(s_X3):sort(s_Nat)
    ]:sort(s_Nat),
    [
      s_succ,
      [
        s_plus,
        vble(s_X2):sort(s_Nat),
        vble(s_X3):sort(s_Nat)
      ]:sort(s_Nat)
    ]:sort(s_Nat)
  ]:sort(top)
  =
  [
    t_equal,
    [
      t_app,
      [
        t_cons,
        vble(t_X1):sort(t_El),
        vble(t_X2):sort(t_L)
      ]:sort(t_L),
      vble(t_X3):sort(t_L)
    ]:sort(t_L),
    [
      t_cons,
      vble(t_X1):sort(t_El),
      [
        t_app,
        vble(t_X2):sort(t_L),
        vble(t_X3):sort(t_L)
      ]:sort(t_L)
    ]:sort(t_L)
  ]:sort(top)

].



story5_sorted(X):-
  X = 
[

  [
    equal:sym,
    [
      plus:nat,
      [0:nat],
      vble(x:nat)
    ],
    vble(x:nat)
  ]
  = 
  [
    equal:sym,
    [
      app:list,
      [nil:list],
      vble(u:list)
    ],
    vble(u:list)
  ]

  ,

  [
    equal:sym,
    [
      plus:nat,
      [
        succ:nat,
        vble(x:nat)
      ],
      vble(y:nat)
    ],
    [
      succ:nat,
      [
        plus:nat,
        vble(x:nat),
        vble(y:nat)
      ]
    ]
  ]
  =
  [
    equal:sym,
    [
      app:list,
      [
        cons:list,
        vble(h:elem),
        vble(u:list)
      ],
      vble(v:list)
    ],
    [
      cons:list,
      vble(h:elem),
      [
        app:list,
        vble(u:list),
        vble(v:list)
      ]
    ]
  ]

].



story5(X):-
  X = 
[

  [
    equal,
    [
      plus,
      [0],
      vble(x)
    ],
    vble(x)
  ]
  = 
  [
    equal,
    [
      app,
      [nil],
      vble(u)
    ],
    vble(u)
  ]

  ,

  [
    equal,
    [
      plus,
      [
        succ,
        vble(x)
      ],
      vble(y)
    ],
    [
      succ,
      [
        plus,
        vble(x),
        vble(y)
      ]
    ]
  ]
  =
  [
    equal,
    [
      app,
      [
        cons,
        vble(h),
        vble(u)
      ],
      vble(v)
    ],
    [
      cons,
      vble(h),
      [
        app,
        vble(u),
        vble(v)
      ]
    ]
  ]

].


% Axioms aligned exactly.
theory_pair_5(X):-
  X = [
% Start of the source theory.
[
  source:thy,
  % Axiom S1.
  [
    equal:sym,
    [
      plus:nat,
      [0:nat],
      vble(x:nat)
    ],
    vble(x:nat)
  ],

  % Axiom S2.
  [
    equal:sym,
    [
      plus:nat,
      [
        succ:nat,
        vble(x:nat)
      ],
      vble(y:nat)
    ],
    [
      succ:nat,
      [
        plus:nat,
        vble(x:nat),
        vble(y:nat)
      ]
    ]
  ]
]  
% End of the source theory.

=

% Start of the target theory.
[
  target:thy,
  % Axiom T1. 
  [
    equal:sym,
    [
      app:list,
      [nil:list],
      vble(u:list)
    ],
    vble(u:list)
  ],

  % Axiom T2.
  [
    equal:sym,
    [
      app:list,
      [
        cons:list,
        vble(h:elem),
        vble(u:list)
      ],
      vble(v:list)
    ],
    [
      cons:list,
      vble(h:elem),
      [
        app:list,
        vble(u:list),
        vble(v:list)
      ]
    ]
  ]
]
% End of the target theory.
    ].


% Axioms not aligned.
% S1 = T2, S2 = T1.
theory_pair_6(X):-
  X = [
% Start of the source theory.
[
  source:thy,
  % Axiom S1.
  [
    equal:sym,
    [
      plus:nat,
      [0:nat],
      vble(x:nat)
    ],
    vble(x:nat)
  ],

  % Axiom S2.
  [
    equal:sym,
    [
      plus:nat,
      [
        succ:nat,
        vble(x:nat)
      ],
      vble(y:nat)
    ],
    [
      succ:nat,
      [
        plus:nat,
        vble(x:nat),
        vble(y:nat)
      ]
    ]
  ]
]  
% End of the source theory.

=

% Start of the target theory.
[
  target:thy,

  % Axiom T2.
  [
    equal:sym,
    [
      app:list,
      [
        cons:list,
        vble(h:elem),
        vble(u:list)
      ],
      vble(v:list)
    ],
    [
      cons:list,
      vble(h:elem),
      [
        app:list,
        vble(u:list),
        vble(v:list)
      ]
    ]
  ],

  % Axiom T1. 
  [
    equal:sym,
    [
      app:list,
      [nil:list],
      vble(u:list)
    ],
    vble(u:list)
  ]
]
% End of the target theory.
    ].





% Axioms not aligned. The numbers of axioms are different.
% S1 = T2, S2 = T1. S3 = New_Axiom.
theory_pair_7(X):-
  X = [
% Start of the source theory.
[
  source:thy,
  % Axiom S1.
  [
    equal:sym,
    [
      plus:nat,
      [0:nat],
      vble(x:nat)
    ],
    vble(x:nat)
  ],

  % Axiom S2.
  [
    equal:sym,
    [
      plus:nat,
      [
        succ:nat,
        vble(x:nat)
      ],
      vble(y:nat)
    ],
    [
      succ:nat,
      [
        plus:nat,
        vble(x:nat),
        vble(y:nat)
      ]
    ]
  ],

  % Axiom S3.
  [
    equal:sym,
    [
      plus:nat,
      vble(x:nat),
      vble(y:nat)
    ],
    [
      plus:nat,
      vble(y:nat),
      vble(x:nat)
    ]
  ]
]  
% End of the source theory.

=

% Start of the target theory.
[
  target:thy,

  % Axiom T2.
  [
    equal:sym,
    [
      app:list,
      [
        cons:list,
        vble(h:elem),
        vble(u:list)
      ],
      vble(v:list)
    ],
    [
      cons:list,
      vble(h:elem),
      [
        app:list,
        vble(u:list),
        vble(v:list)
      ]
    ]
  ],

  % Axiom T1. 
  [
    equal:sym,
    [
      app:list,
      [nil:list],
      vble(u:list)
    ],
    vble(u:list)
  ]
]
% End of the target theory.
    ].


pred_to_list(X,[X]):-
  (
    atom(X)
    ;
    number(X)
  ),
  !.
pred_to_list(vble(X),vble(X)):-!.
pred_to_list(P,[X|Res]):-
  P =.. [X|L],
  pred_to_list2(L,Res).

pred_to_list2([],[]):-!.
pred_to_list2([X|L],[Rx|Rl]):-
  pred_to_list(X,Rx),
  pred_to_list2(L,Rl).

list_to_pred([X],X):-
  (
    atom(X)
    ;
    number(X)
  ),
  !.
list_to_pred(vble(X),vble(X)):-!.
list_to_pred([X|L],Res):-
  list_to_pred2(L,R),
  Res =.. [X|R].

list_to_pred2([],[]):-!.
list_to_pred2([X|L],[Rx|Rl]):-
  list_to_pred(X,Rx),
  list_to_pred2(L,Rl).



for(I,I,J):-
	I =< J.
for(K,I,J):-
	I < J,
	I1 is I + 1,
	for(K,I1,J).

% "smaill_nat.dol" and "smaill_list.dol"
% Notype
theory_smaill(Source, Target):-

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
/*
  % Axs6 |-> Axt6: forall x: Nat. sum(x) = qsum(x,0)
  equal(sum(xs6),qsum(xs6,0)),

  % Axs7: forall x,y:Nat. plus(sum(x),y) = qsum(x,y)
  equal(plus(sum(xs7),ys7),qsum(xs7,ys7)),
*/
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
  equal(rev(cons(ht3,xt3)),app(rev(xt3),cons(ht3,nil))) /*,

  % Axt4: forall x:L. qrev(nil,x) = x
  equal(qrev(nil,xt4),xt4),

  % Axt5: forall x,y:L;h:El. qrev(cons(h,x),y) = qrev(x,cons(h,y))
  equal(qrev(cons(ht5,xt5),yt5),qrev(xt5,cons(ht5,yt5))),

  % Axt6: forall x:L. rev(x) = qrev(x,nil);
  equal(rev(xt6),qrev(xt6,nil)) */
  
).
% End of the target theory.





% For adding functors.
theory_addfunc(Source, Target):-

% Start of the source theory.
Source = sc(

  % a(b(c(d(e(f))))),
  app(cons(ht1,xt1))
  % a1(b1(c1(d1(e1(f1)))))

),
% End of the source theory.

% Start of the target theory.
Target = tg(

  % app(nil,xt0),
  g(h(i(j(k(l)))))
  % app(rev(xt3))
 
).
% End of the target theory.

