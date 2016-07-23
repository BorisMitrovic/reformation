% Filters can prohibit some repairs when unblocking unification.
% To enable/prohibit a repair, you could comment/uncomment it, as some examples below.

% The filter of example_9_3.
filter1(F):-
  F = 
  [
    % Prohibit merging.
    % merge(_,_,left) ,
    merge(_,_,right) ,

    % Prohibit adding new arguments (constants).
    % addargc(_,_,_,_,left) ,
    % addargc(_,_,_,_,right) ,

    % Prohibit adding new arguments (variables).
    % addargv(_,_,_,left) ,
    % addargv(_,_,_,right) ,

    % Prohibit deleting arguments.
    % delarg(_,_,_,left) ,
    % delarg(_,_,_,right) ,

    % Prohibit adding new functors.
    addfunc(_,_,_,left) ,
    addfunc(_,_,_,right) ,

    % Prohibit deleting functors.
    delfunc(_,_,_,left) ,
    delfunc(_,_,_,right) ,
    
    % Prohibit permuting arguments.
    permute(_,_,left) ,
    permute(_,_,right) ,

    tail_of_filter
  ].

% A filter for repairing rewriting rules.
filter_rewrite(F):-
  F = 
  [
    % Prohibit merging.
    % merge(_,_,left) ,
    merge(_,_,right) ,

    % Prohibit adding new arguments (constants).
    % addargc(_,_,_,_,left) ,
    addargc(_,_,_,_,right) ,

    % Prohibit adding new arguments (variables).
    % addargv(_,_,_,left) ,
    addargv(_,_,_,right) ,

    % Prohibit deleting arguments.
    delarg(_,_,_,left) ,
    delarg(_,_,_,right) ,

    % Prohibit adding new functors.
    % addfunc(_,_,_,left) ,
    addfunc(_,_,_,right) ,

    % Prohibit deleting functors.
    delfunc(_,_,_,left) ,
    delfunc(_,_,_,right) ,
    
    % Prohibit permuting arguments.
    % permute(_,_,left) ,
    permute(_,_,right) ,

    tail_of_filter
  ].


% The default filter.
filter_default(F):-
  F = 
  [
    % Prohibit merging.
    % merge(_,_,left) ,
    merge(_,_,right) ,

    % Prohibit adding new arguments (constants).
    % addargc(_,_,_,_,left) ,
    addargc(_,_,_,_,right) ,

    % Prohibit adding new arguments (variables).
    % addargv(_,_,_,left) ,
    addargv(_,_,_,right) ,

    % Prohibit deleting arguments.
    delarg(_,_,_,left) ,
    delarg(_,_,_,right) ,

    % Prohibit adding new functors.
    addfunc(_,_,_,left) ,
    addfunc(_,_,_,right) ,

    % Prohibit deleting functors.
    delfunc(_,_,_,left) ,
    delfunc(_,_,_,right) ,
    
    % Prohibit permuting arguments.
    permute(_,_,left) ,
    permute(_,_,right) ,

    tail_of_filter
  ].
