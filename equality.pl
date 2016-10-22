% Faulty equality axiom
% From exists z, forall y, z=/=y


fact([-equal($y,$c)]).   % Faulty axiom
fact([+equal($x,$x)]).   % Reflexivity

% function(equal).
protect([equal]).

% Run the following to test this ontology:
%   notrace,[diagnose,repair,util,reform,revise,utilRevise,equality], revise.
/*
fact([-(==(y,c))]).   % Faulty axiom
fact([+(==(x,x))]).   % Reflexivity
*/
