% Self love theory
% adapted from "every man loves a woman" ambiguity


fact1([loves(x,x)]).
fact1([loves(y,love_of(y))]).
/*
Run the following to test this theory:
notrace,[diagnose,repair,util,reform,revise,utilRevise,selflove,unblock,upgrade],upgrade.
*/
fact([+loves($x,$x)]).
fact([-loves($y,love_of($y))]).
