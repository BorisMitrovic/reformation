% Faulty equality axiom
% From exists z, forall y, z=/=y

fact([-equal(y,c)]).   % Faulty axiom
fact([+equal(x,x)]).   % Reflexivity


% Run the following to test this ontology:
%   notrace,[diagnose,repair,util,reform,revise,utilRevise,equality], revise.
