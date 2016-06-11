% Sweets ontology
% everything a child likes is a chocolate; everything a child likes is an icecream; nothing is both an icecream and a chocolate.

fact([-child(xx), -likes(xx,xc), +chocolate(xc)]).
fact([-child(x), -likes(x,xi), +icecream(xi)]).
fact([+likes(john,icy)]).
fact([+child(john)]).
fact([+icecream(icy)]).
fact([+child(jane)]).
fact([+chocolate(chocodream)]).
fact([+likes(jane,chocodream)]).
fact([-chocolate(yc), -icecream(yc)]).

%   [diagnose,repair,util,reform,revise,utilRevise,sweets]. revise.
