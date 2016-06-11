% multiple repairs ontology

fact([+bird(dodo)]).
fact([-bird(x), +fly(x)]).
fact([+extinct(dodo)]).
fact([-extinct(y), +immobile(y)]).
fact([-immobile(z), -fly(z)]).

fact([+imaginary(dragon)]).
fact([-talk_of(x1,x2), +alive(x1)]).
fact([-talk_of(y1,y2), +alive(y2)]).
fact([+talk_of(michael,dragon)]).
fact([-imaginary(w),-alive(w)]).

%   [diagnose,repair,util,reform,revise,utilRevise,animal]. revise.