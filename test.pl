%% Tests for Non-Standard Unification Procedure %%
%% Alan Bundy, 30.1.12 %%


testall(R) :- minimal(R).
testall(R) :- verbal(R).
testall(R) :- unblockall(R).
testall(R) :- blockall(R).



blockall(R) :- nl, nl,  go1(R), nl, nl.
blockall(R) :- nl, nl,  go2(R), nl, nl.
blockall(R) :- nl, nl,  mechanic(R), nl, nl.
blockall(R) :- nl, nl,  driver(R), nl, nl.
blockall(R) :- nl, nl,  eq(R), nl, nl.
% blockall(R) :- nl, nl,  wms(R), nl, nl.
% because of operator precedence (for example ':' and '=') sorts can't be specified (convert fails) for functions of type '=', '+', '-', '/', '*'.

unblockall(R) :- nl, nl,  go3(R), nl, nl.
unblockall(R) :- nl, nl,  go4(R), nl, nl.
unblockall(R) :- nl, nl,  go5(R), nl, nl.
unblockall(R) :- nl, nl,  go6(R), nl, nl.
unblockall(R) :- nl, nl,  parent(R), nl, nl.
unblockall(R) :- nl, nl,  pay(R), nl, nl.
unblockall(R) :- nl, nl,  love(R), nl, nl.
unblockall(R) :- nl, nl,  love2(R), nl, nl.
% unblockall(R) :- nl, nl,  cauchy(R), nl, nl.      % uses function symbols ('=','+',...)

verbal(R):- nl, nl, football(R), nl, nl.
verbal(R):- nl, nl, deceased(R), nl, nl.
verbal(R):- nl, nl, possession(R), nl, nl.
verbal(R):- nl, nl, parent2(R), nl, nl.
verbal(R):- nl, nl, milk(R), nl, nl.
verbal(R):- nl, nl, complicated(R), nl, nl.
verbal(R):- nl, nl, bees(R), nl, nl.
verbal(R):- nl, nl, dumbo(R), nl, nl.
verbal(R):- nl, nl, adoptive(R), nl, nl.

minimal(R):- nl,nl, minimal1(R), nl,nl.
minimal(R):- nl,nl, minimal2(R), nl,nl.
minimal(R):- nl,nl, minimal3(R), nl,nl.
minimal(R):- nl,nl, minimal4(R), nl,nl.
minimal(R):- nl,nl, minimal5(R), nl,nl.
minimal(R):- nl,nl, minimal6(R), nl,nl.



% minimal repair Examples
minimal1(Rs):-
    print('* Illustrate failed unification of f(x:t,x:t, x:t):s,f(a:t,b:t,b:t):s'), nl,
    reform(f(x:t,x:t, x:t):s,f(a:t,b:t,b:t):s,_,fail,FS,_),
    print('Result is '), print(FS), nl,
   nl,
    print('* Unblock unification of f(x:t,x:t, x:t):s,f(a:t,b:t,b:t):s'), nl, !,
    reform(f(x:t,x:t, x:t):s,f(a:t,b:t,b:t):s,Sigma,success,_,Rs),
    print('   With substitution: '), print(Sigma).

minimal2(Rs):-
    print('* Illustrate failed unification of f(x:t,x:t, x:t,x:t,x:t,x:t):s,f(a:t,b:t,b:t,c:t,a:t,a:t):s'), nl,
    reform(f(x:t,x:t, x:t,x:t,x:t,x:t):s,f(a:t,b:t,b:t,c:t,a:t,a:t):s,_,fail,FS,_),
    print('Result is '), print(FS), nl,
   nl,
    print('* Unblock unification of f(x:t,x:t, x:t,x:t,x:t,x:t):s,f(a:t,b:t,b:t,c:t,a:t,a:t):s'), nl, !,
    reform(f(x:t,x:t, x:t,x:t,x:t,x:t):s,f(a:t,b:t,b:t,c:t,a:t,a:t):s,Sigma,success,_,Rs),
    print('   With substitution: '), print(Sigma).

minimal3(Rs):-
    print('* Illustrate failed unification of f(x:t,y:s,x:t,x:t,d:s):s,f(a:t,c:s,b:t,b:t,y:s):s'), nl,
    reform(f(x:t,y:s,x:t,x:t,d:s):s,f(a:t,c:s,b:t,b:t,y:s):s,_,fail,FS,_),
    print('Result is '), print(FS), nl,
   nl,
    print('* Unblock unification of f(x:t,y:s,x:t,x:t,d:s):s,f(a:t,c:s,b:t,b:t,y:s):s'), nl, !,
    reform(f(x:t,y:s,x:t,x:t,d:s):s,f(a:t,c:s,b:t,b:t,y:s):s,Sigma,success,_,Rs),
    print('   With substitution: '), print(Sigma).

% minimal blocking
minimal4(Rs):-
    print('* Illustrate successful unification of f(x:t,a:t,x:t):s,f(y:t,y:t,z:t):s'), nl,
    reform(f(x:t,a:t,x:t):s,f(y:t,y:t,z:t):s,Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
   nl,
    print('* Block unification of f(x:t,a:t,x:t):s=f(y:t,y:t,z:t):s'), nl, !,
    reform(f(x:t,a:t,x:t):s,f(y:t,y:t,z:t):s,_,fail,_,Rs),
   nl.

minimal5(Rs):- 
    print('* Illustrate successful unification of f(x:s,x:s,a:s):s=f(y:s,a:s,y:s):s'), nl,
    reform(f(x:s,x:s,a:s):s,f(y:s,a:s,y:s):s,Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
    nl,
    print('* Block unification of f(x:s,x:s,a:s):s=f(y:s,a:s,y:s):s'), nl, !,
    reform(f(x:s,x:s,a:s):s,f(y:s,a:s,y:s):s,_,fail,_,Rs).   

minimal6(Rs):- 
    print('* Illustrate successful unification of f(x:s,x:s,x:s):s=f(a:s,a:s,a:s):s'), nl,
    reform(f(x:s,x:s,x:s):s,f(a:s,a:s,a:s):s,Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
    nl,
    print('* Block unification of f(x:s,x:s,x:s):s=f(a:s,a:s,a:s):s'), nl, !,
    reform(f(x:s,x:s,x:s):s,f(a:s,a:s,a:s):s,_,fail,_,Rs).   


% Conceptual Examples
football(Rs) :- 
    print('* Illustrate successful unification of handle(buffon:footballer):pred=handle(x:footballer):pred'), nl,
    reform(handle(buffon:footballer):pred,handle(x:footballer):pred,Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
    nl,
    print('* Block unification of handle(buffon:footballer):pred=handle(x:footballer):pred'), nl,
    reform(handle(buffon:footballer):pred,handle(x:footballer):pred,_,fail,_,Rs).

bees(Rs) :- 
    print('* Illustrate successful unification of flies(bee_queen:bee):pred=flies(x:bee):pred'), nl,
    reform(flies(bee_queen:bee):pred,flies(x:bee):pred,Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
    nl,
    print('* Block unification of flies(bee_queen:bee):pred=flies(x:bee):pred'), nl,
    reform(flies(bee_queen:bee):pred,flies(x:bee):pred,_,fail,_,Rs).

dumbo(Rs) :- 
    print('* Illustrate successful unification of flies(dumbo:elephant):s=flies(x:elephant):s'), nl,
    reform(flies(dumbo:elephant):s, flies(x:elephant):s,Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
    nl,
    print('* Block unification of flies(dumbo:elephant):s=flies(x:elephant):s'), nl,
    reform(flies(dumbo:elephant):s, flies(x:elephant):s,_,fail,_,Rs).

adoptive(Rs) :- 
    print('* Illustrate successful unification of given_birth(x:mother):s=given_birth(marry:mother):s'),
    nl,
    reform(given_birth(x:mother):s, given_birth(marry:mother):s,Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
    nl,
    print('* Block unification of given_birth(x:mother):s=given_birth(marry:mother):s'), nl,
    reform(given_birth(x:mother):s, given_birth(marry:mother):s,_,fail,_,Rs).

deceased(Rs) :- 
    print('* Illustrate successful unification of have_heartbeat(x:person):s=have_heartbeat(einstein:person):s'),
    nl,
    reform(have_heartbeat(x:person):s, have_heartbeat(einstein:person):s,Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
    nl,
    print('* Block unification of have_heartbeat(x:person):s=have_heartbeat(einstein:person):s'), nl,
    reform(have_heartbeat(x:person):s, have_heartbeat(einstein:person):s,_,fail,_,Rs).

possession(Rs) :- 
    print('* Illustrate successful unification of materialist(john:dualist):philosophy=materialist(x:dualist):philosophy'),
    nl,
    reform(materialist(john:dualist):philosophy, materialist(x:dualist):philosophy,Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
    nl,
    print('* Block unification of materialist(john:dualist):philosophy=materialist(x:dualist):philosophy'), nl,
    reform(materialist(john:dualist):philosophy, materialist(x:dualist):philosophy,_,fail,_,Rs).

parent2(Rs):-
    print('* Illustrate failed unification of love(john:father,x:child):pred=love(y:mother,z:child):pred'), nl,
    reform(love(john:father,x:child):pred,love(y:mother,z:child):pred,_,fail,FS,_),
    print('Result is '), print(FS), nl,
   nl,
    print('* Unblock unification of love(john:father,x:child):pred=love(y:mother,z:child):pred'), nl, !,
    reform(love(john:father,x:child):pred,love(y:mother,z:child):pred,_,success,_,Rs).

milk(Rs):-
    print('* Illustrate failed unification of origin(x:milk,y:animal):s=origin(coconut:milk,coconut_palm:fruit):s'), nl,
    reform(origin(x:milk, y:animal):s, origin(coconut:milk, coconut_tree:fruit):s,_,fail,FS,_),
    print('Result is '), print(FS), nl,
   nl,
    print('* Unblock unification of origin(x:milk,y:animal):s=origin(coconut:milk,coconut_tree:fruit):s'), nl, !,
    reform(origin(x:milk, y:animal):s, origin(coconut:milk, coconut_palm:fruit):s,_,success,_,Rs).

complicated(Rs):-
    print('* Illustrate failed unification of source(x:milk, y:animal, france:country):s, origin(coconut:pure_milk, coconut_tree:vegetable, bordeaux:town):t'), nl,
    reform(source(x:milk, y:animal, france:country):s, origin(coconut:pure_milk, coconut_tree:vegetable, bordeaux:town):t,_,fail,FS,_),
    print('Result is '), print(FS), nl,
   nl,
    print('* Unblock unification of source(x:milk, y:animal, france:country):s, origin(coconut:pure_milk, coconut_tree:vegetable, bordeaux:town):t'), nl, !,
    reform(source(x:milk, y:animal, france:country):s, origin(coconut:pure_milk, coconut_tree:vegetable, bordeaux:town):t,_,success,_,Rs).

% <add> convex example, by using more unifications


go1(Rs):- 
    print('* Illustrate successful unification of x:s=f(c:t):s'), nl,
    reform(x:s,f(c:t):s,Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
    nl,
    print('* Block unification of x:s=f(c:t):s'), nl, !,
    reform(x:s,f(c:t):s,_,fail,_,Rs).   

go2(Rs):-
    print('* Illustrate successful unification of f(x:c):s,f(c:c):s'), nl,
    reform(f(x:c):s,f(c:c):s,Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
    nl,
    print('* Block unification of f(x:c):s=f(c:c):s'), nl, !,
    reform(f(x:c):s,f(c:c):s,_,fail,_,Rs).

go3(Rs):-
    print('* Illustrate failed unification of x:s=f(x:s):t'), nl,
    reform(x:s,f(x:s):t,_,fail,FS,_),
    print('Result is '), print(FS), nl,
   nl,
    print('* Unblock unification of x:s=f(x:s):t'), nl, !,
    reform(x:s,f(x:s):t,_,success,_,Rs).

go4(Rs):-
    print('* Illustrate failed unification of f(x:v):t=f(a:a,c:v):s'), nl,
    reform(f(x:v):t,f(a:a,c:v):s,_,fail,FS,_),
    print('Result is '), print(FS), nl,
    nl,
    print('* Unblock unification of f(x:v):t=f(a:a,c:v):s'), nl, !,
    reform(f(x:v):t,f(a:a,c:v):s,_,success,_,Rs).

go5(Rs):-
    print('* Illustrate failed unification of f(x:c):s=g(a:c):s'), nl,
    reform(f(x:c):s,g(a:c):s,_,fail,FS,_),
    print('Result is '), print(FS), nl,
    nl,
    print('* Unblock unification of f(x:c):s=g(a:c):s'), nl, !,
    reform(f(x:c):s,g(a:c):s,_,success,_,Rs).



go6(Rs):-
    print('* Illustrate failed unification of f(x)=g(y,z)'), nl,
    reform(f(x),g(y,z),_,fail,FS,_),
    print('Result is '), print(FS), nl,
    nl,
    print('* Unblock unification of f(x)=g(y,z)'), nl, !,
    reform(f(x),g(y,z),_,success,_,Rs).



%% Examples from BBN 1750

mechanic(Rs) :- 
    print('* Illustrate successful unification of mechanic(f:t):p=mechanic(f:t):p'), nl,
    reform(mechanic(f:t):p,mechanic(f:t):p,Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
    nl,
    print('* Block unification of mechanic(f:t):p=mechanic(f:t):p'), nl,
    reform(mechanic(f:t):p,mechanic(f:t):p,_,fail,_,Rs).

mechanicName(Rs) :- 
    print('* Illustrate successful unification of mechanic(felipe:person):profession=mechanic(felipe:person):profession'), nl,
    reform(mechanic(felipe:person):profession,mechanic(felipe:person):profession,Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
    nl,
    print('* Block unification of mechanic(felipe:person):profession=mechanic(felipe:person):profession'), nl,
    reform(mechanic(felipe:person):profession,mechanic(felipe:person):profession,_,fail,_,Rs).


driver(Rs) :- 
    print('* Illustrate successful unification of driver(f:t):p=driver(x:t):p'), nl,
    reform(driver(f:t):p,driver(x:t):p,Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
    nl,
    print('* Block unification of driver(f:t):p=driver(x:t):p'), nl, !,
    reform(driver(f:t):p,driver(x:t):p,_,fail,_,Rs).


eq(Rs) :- 
    print('* Illustrate successful unification of eq(x:v,x:v):p=eq(y:v,c:v):p'), nl,
    reform(eq(x:v,x:v):p,eq(y:v,c:v):p,Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
    nl,
    print('* Block unification of eq(x:v,x:v):p=eq(y:v,c:v):p'), nl, !,
    reform(eq(x:v,x:v):p,eq(y:v,c:v):p,_,fail,_,Rs).


%% Examples from BBN 1759

parent(Rs) :- 
    print('* Illustrate failed unification of parent(a:s,c:s):p=parnet(x:s,y:s):p'), nl,
    reform(parent(a:s,c:s):p,parnet(x:s,y:s):p,_,fail,FS,_),
    print('Result is '), print(FS), nl,
    nl,
    print('* Unblock unification of parent(a:s,c:s):p=parnet(x:s,y:s):p'), nl, !,
    reform(parent(a:s,c:s):p,parnet(x:s,y:s):p,_,success,_,Rs).

pay(Rs) :-
    print('* Illustrate failed unification of pay(a:item,price(c:money):p):o=pay(x:item,price(y:card):p,b:type):p'), nl,
    reform(pay(a:item,price(c:money):p):o,pay(x:item,price(y:card):p,b:type):p,_,fail,FS,_),
    print('Result is '), print(FS), nl,
    nl,
    print('* Unblock unification of pay(a:item,price(c:money):p):o=pay(x:item,price(y:card):p,b:type):p'), nl, !,
    reform(pay(a:item,price(c:money):p):o,pay(x:item,price(y:card):p,b:type):p,_,success,_,Rs).

love(Rs) :-
    print('* Illustrate failed unification of love(x:p,x:p):s=love(y:p,love_of(y:p):p):s'), nl,
    reform(love(x:p,x:p):s,love(y:p,love_of(y:p):p):s,_,fail,FS,_),
    print('Result is '), print(FS), nl,
    nl,
    print('* Unblock unification of love(x:p,x:p):s=love(y:p,love_of(y:p):p):s'), nl, !,
    reform(love(x:p,x:p):s,love(y:p,love_of(y:p):p):s,_,success,_,Rs).


love2(Rs) :-
    print('* Illustrate failed unification of love(x:p,x:p):s=love2(y:p,love_of(y:p):p):s'), nl,
    reform(love(x:p,x:p):s,love2(y:p,love_of(y:p):p):s,_,fail,FS,_),
    print('Result is '), print(FS), nl,
    nl,
    print('* Unblock unification of love(x:p,x:p):s=love2(y:p,love_of(y:p):p):s'), nl, !,
    reform(love(x:p,x:p):s,love2(y:p,love_of(y:p):p):s,_,success,_,Rs).


cauchy(Rs) :-
    print('* Illustrate failed unification of geq(y,y) and geq(n,m(e/3,x+b(delta(e/3,x,n))))'), nl,
    reform(geq(y,y), geq(n,m(e/3,x+b(delta(e/3,x,n)))),_,fail,FS,_),
    print('Result is '), print(FS), nl,
    nl,
    print('* Unblock unification of geq(y,y) and geq(n,m(e/3,x+b(delta(e/3,x,n))))'), nl, !,
    reform(geq(y,y), geq(n,m(e/3,x+b(delta(e/3,x,n)))),_,success,_,Rs).



wms(Rs) :-
    print('* Block unification of f(c:s):s=a:s:s and f(c:s):s=z:s:s'), nl, !,
    reform(f(c:s):s=a:s, f(c:s):s=z:s,_,fail,_,Rs).



test_disjoin(Z) :- disjoin(a,b,X), disjoin(c,d,Y), disjoin(X,Y,Z).


test_disjoin2(Z) :- a=Z; b=Z; c=Z; d=Z.


r(X) :- p(X).

r(X) :- q(X).

r(X) :- o(X).

p(a).
p(b).
p(c).


q(d).
q(e).
q(f).

o(g).
o(h).
o(i).
