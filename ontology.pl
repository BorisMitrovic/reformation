% ontology is a collection of facts. Converted to CNF form.

fact([-eats(xa, xa)]).
fact([+eats(xm, grass)]).

fact([+mad(madcow)]).
fact([-mad(xx), -eats(xh,grass), +eats(xx,xh)]).

% Run the following to test this ontology:
%   notrace,[diagnose,repair,util,reform,revise,utilRevise,ontology]. revise.