% Motherhood theory
% There are now many kinds of motherhood, which can potentially be confused.

fact([+mum(diana,bill)]).              % Birth mother
fact([+mum(camilla,bill)]).            % Step mother
fact([-equal(diana,camilla)]).            % Different people
fact([-mum($x,$z),-mum($y,$z),+equal($x,$y)]).  % Mother are unique

% Run the following to test this ontology:
%   notrace,[diagnose,repair,util,reform,revise,utilRevise,motherhood], revise.

 protect([diana]).
 protect([bill]).
 protect([camilla]).

 function(equal).
