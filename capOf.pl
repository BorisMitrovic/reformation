% Capital of ontology

fact([+cap_of(london,britain)]).
fact([+cap_of(edinburgh,britain)]).
fact([+cap_of(berlin,germany)]).
fact([+cap_of(canberra,australia)]).
fact([-cap_of($x,$y), -cap_of($z,$y), +($x == $z)]).
/*
% Run the following to test this ontology:
notrace,[diagnose,repair,util,reform,revise,utilRevise,capOf], revise.

*/
protect([]).
