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
    print('* Illustrate failed unification of f(x,x, x),f(a,b,b)'), nl,
    reform(f(x,x, x),f(a,b,b),_,fail,FS,_),
    print('Result is '), print(FS), nl,
   nl,
    print('* Unblock unification of f(x,x, x),f(a,b,b)'), nl, !,
    reform(f(x,x, x),f(a,b,b),Sigma,success,_,Rs),
    print('   With substitution: '), print(Sigma).

minimal2(Rs):-
    print('* Illustrate failed unification of f(x,x, x,x,x,x),f(a,b,b,c,a,a)'), nl,
    reform(f(x,x, x,x,x,x),f(a,b,b,c,a,a),_,fail,FS,_),
    print('Result is '), print(FS), nl,
   nl,
    print('* Unblock unification of f(x,x, x,x,x,x),f(a,b,b,c,a,a)'), nl, !,
    reform(f(x,x, x,x,x,x),f(a,b,b,c,a,a),Sigma,success,_,Rs),
    print('   With substitution: '), print(Sigma).

minimal3(Rs):-
    print('* Illustrate failed unification of f(x,y,x,x,d),f(a,c,b,b,y)'), nl,
    reform(f(x,y,x,x,d),f(a,c,b,b,y),_,fail,FS,_),
    print('Result is '), print(FS), nl,
   nl,
    print('* Unblock unification of f(x,y,x,x,d),f(a,c,b,b,y)'), nl, !,
    reform(f(x,y,x,x,d),f(a,c,b,b,y),Sigma,success,_,Rs),
    print('   With substitution: '), print(Sigma).

% minimal blocking
minimal4(Rs):-
    print('* Illustrate successful unification of f(x,a,x),f(y,y,z)'), nl,
    reform(f(x,a,x),f(y,y,z),Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
   nl,
    print('* Block unification of f(x,a,x)=f(y,y,z)'), nl, !,
    reform(f(x,a,x),f(y,y,z),_,fail,_,Rs),
   nl.

minimal5(Rs):- 
    print('* Illustrate successful unification of f(x,x,a)=f(y,a,y)'), nl,
    reform(f(x,x,a),f(y,a,y),Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
    nl,
    print('* Block unification of f(x,x,a)=f(y,a,y)'), nl, !,
    reform(f(x,x,a),f(y,a,y),_,fail,_,Rs).   

minimal6(Rs):- 
    print('* Illustrate successful unification of f(x,x,x)=f(a,a,a)'), nl,
    reform(f(x,x,x),f(a,a,a),Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
    nl,
    print('* Block unification of f(x,x,x)=f(a,a,a)'), nl, !,
    reform(f(x,x,x),f(a,a,a),_,fail,_,Rs).   


% <add> convex example, by using more unifications


go1(Rs):- 
    print('* Illustrate successful unification of x=f(c)'), nl,
    reform(x,f(c),Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
    nl,
    print('* Block unification of x=f(c)'), nl, !,
    reform(x,f(c),_,fail,_,Rs).   

go2(Rs):-
    print('* Illustrate successful unification of f(x:c),f(c:c)'), nl,
    reform(f(x:c),f(c:c),Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
    nl,
    print('* Block unification of f(x:c)=f(c:c)'), nl, !,
    reform(f(x:c),f(c:c),_,fail,_,Rs).

go3(Rs):-
    print('* Illustrate failed unification of x=f(x)'), nl,
    reform(x,f(x),_,fail,FS,_),
    print('Result is '), print(FS), nl,
   nl,
    print('* Unblock unification of x=f(x)'), nl, !,
    reform(x,f(x),_,success,_,Rs).

go4(Rs):-
    print('* Illustrate failed unification of f(x)=f(a,c)'), nl,
    reform(f(x),f(a,c),_,fail,FS,_),
    print('Result is '), print(FS), nl,
    nl,
    print('* Unblock unification of f(x)=f(a,c)'), nl, !,
    reform(f(x),f(a,c),_,success,_,Rs).

go5(Rs):-
    print('* Illustrate failed unification of f(x:c)=g(a:c)'), nl,
    reform(f(x:c),g(a:c),_,fail,FS,_),
    print('Result is '), print(FS), nl,
    nl,
    print('* Unblock unification of f(x:c)=g(a:c)'), nl, !,
    reform(f(x:c),g(a:c),_,success,_,Rs).



go6(Rs):-
    print('* Illustrate failed unification of f(x)=g(y,z)'), nl,
    reform(f(x),g(y,z),_,fail,FS,_),
    print('Result is '), print(FS), nl,
    nl,
    print('* Unblock unification of f(x)=g(y,z)'), nl, !,
    reform(f(x),g(y,z),_,success,_,Rs).



%% Examples from BBN 1750

mechanic(Rs) :- 
    print('* Illustrate successful unification of mechanic(f)=mechanic(f)'), nl,
    reform(mechanic(f),mechanic(f),Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
    nl,
    print('* Block unification of mechanic(f)=mechanic(f)'), nl,
    reform(mechanic(f),mechanic(f),_,fail,_,Rs).

mechanicName(Rs) :- 
    print('* Illustrate successful unification of mechanic(felipe)=mechanic(felipe)'), nl,
    reform(mechanic(felipe),mechanic(felipe),Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
    nl,
    print('* Block unification of mechanic(felipe)=mechanic(felipe)'), nl,
    reform(mechanic(felipe),mechanic(felipe),_,fail,_,Rs).


driver(Rs) :- 
    print('* Illustrate successful unification of driver(f)=driver(x)'), nl,
    reform(driver(f),driver(x),Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
    nl,
    print('* Block unification of driver(f)=driver(x)'), nl, !,
    reform(driver(f),driver(x),_,fail,_,Rs).


eq(Rs) :- 
    print('* Illustrate successful unification of eq(x,x)=eq(y,c)'), nl,
    reform(eq(x,x),eq(y,c),Sigma,success,FS,_),
    print('Result is '), print(FS), print(' with substitution '), print(Sigma), nl,
    nl,
    print('* Block unification of eq(x,x)=eq(y,c)'), nl, !,
    reform(eq(x,x),eq(y,c),_,fail,_,Rs).


%% Examples from BBN 1759

parent(Rs) :- 
    print('* Illustrate failed unification of parent(a,c)=parnet(x,y)'), nl,
    reform(parent(a,c),parnet(x,y),_,fail,FS,_),
    print('Result is '), print(FS), nl,
    nl,
    print('* Unblock unification of parent(a,c)=parnet(x,y)'), nl, !,
    reform(parent(a,c),parnet(x,y),_,success,_,Rs).

pay(Rs) :-
    print('* Illustrate failed unification of pay(a:item,price(c:money)):o=pay(x:item,price(y:card),b)'), nl,
    reform(pay(a:item,price(c:money)):o,pay(x:item,price(y:card),b),_,fail,FS,_),
    print('Result is '), print(FS), nl,
    nl,
    print('* Unblock unification of pay(a:item,price(c:money)):o=pay(x:item,price(y:card),b)'), nl, !,
    reform(pay(a:item,price(c:money)):o,pay(x:item,price(y:card),b),_,success,_,Rs).

love(Rs) :-
    print('* Illustrate failed unification of love(x,x)=love(y,love_of(y))'), nl,
    reform(love(x,x),love(y,love_of(y)),_,fail,FS,_),
    print('Result is '), print(FS), nl,
    nl,
    print('* Unblock unification of love(x,x)=love(y,love_of(y))'), nl, !,
    reform(love(x,x),love(y,love_of(y)),_,success,_,Rs).


love2(Rs) :-
    print('* Illustrate failed unification of love(x,x)=love2(y,love_of(y))'), nl,
    reform(love(x,x),love2(y,love_of(y)),_,fail,FS,_),
    print('Result is '), print(FS), nl,
    nl,
    print('* Unblock unification of love(x,x)=love2(y,love_of(y))'), nl, !,
    reform(love(x,x),love2(y,love_of(y)),_,success,_,Rs).


cauchy(Rs) :-
    print('* Illustrate failed unification of geq(y,y) and geq(n,m(e/3,x+b(delta(e/3,x,n))))'), nl,
    reform(geq(y,y), geq(n,m(e/3,x+b(delta(e/3,x,n)))),_,fail,FS,_),
    print('Result is '), print(FS), nl,
    nl,
    print('* Unblock unification of geq(y,y) and geq(n,m(e/3,x+b(delta(e/3,x,n))))'), nl, !,
    reform(geq(y,y), geq(n,m(e/3,x+b(delta(e/3,x,n)))),_,success,_,Rs).



wms(Rs) :-
    print('* Block unification of f(c)=a and f(c)=z'), nl, !,
    reform(f(c)=a, f(c)=z,_,fail,_,Rs).



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
