/*
Run the following to test this ontology:
[diagnose,repair,util,reform,revise,utilRevise,stepmother,upgrade,unblock].


fact([+stepmum(camilla,william)]).
fact([-stepmum($x,$z),+parent($x,$z)]).
fact([-parent2(camilla,william,step)]).


fact([+parent2($x,$y,cstep)]).
fact([-parent(camilla,bill)]).

*/

fact([+parent2($x,$y,cstep)]).
fact([-parent(camilla,bill)]).


fact1([parent2(x,y,cstep)]).
fact1([parent(camilla,bill)]).
