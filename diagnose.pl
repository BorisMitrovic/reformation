%% Diagnose Unification Problems and Suggest Repairs %%
%% Alan Bundy, 30.1.12 %%
%% Revised By Boris Mitrovic, 16.05.13; 11.06.16 for ontology repair %%

%% diagnose(W,FS,Eq,Rs): if result from Eq unwanted W\=FS then suggest repairs
%% Rs to signature

% Do nothing if result is as wanted. Do not back up
diagnose(FS,FS,_,[]) :- !.

% Suggest repair if success wanted but failure produced.

% Case CCf repairs: merge functors and make same arity
diagnose(success,fail,[F1|Args1]=[F2|Args2],Rs) :- !,
    merge_funcs(F1,F2,Rs1),                 % Merge functors if they are different
    same_arity([F1|Args1],[F2|Args2],Rs2),  % Equate arities if they are different
    append(Rs1,Rs2,Rs).                     % Conjoin these repairs



% Case VCf repairs: remove occurrences of X
diagnose(success,fail,vble(X)=[F|Args],Rs) :-
    position(vble(X),[F|Args],Posn),     % Find position that X occurs at
    remove_occ(Posn,[F|Args],Rs).        % Suggest repair Rs that removes an argument that X occurs in

% Case *** repairs: remove F if there is no other functions
diagnose(success,fail,vble(_)=[F|Args],Rs) :- !,
   \+ bagof(FuncName,
         (getfunction(FuncName,[F|Args],[_,_]),
         FuncName \== F ),
         _),
   Rs=[remove_func(F)].        % Suggest repair Rs that removes an argument that X occurs in

% Suggest repair if failure wanted but success produced.

% Case CCs repairs: split functors or differentiate arities
diagnose(fail,success,[F1|Args1]=[F2|Args2],Rs) :- !,
    (split_funcs(F1,F2,Rs);                  % Split functors
    diff_arity([F1|Args1],[F2|Args2],Rs)).   % Or differentiate arities

% Case VCs repairs: insert X to induce occurs check failure
diagnose(fail,success,vble(X)=[F|_],Rs) :-
    Rs = [insert_var(F,X)].


%% merge_funcs(F1,F2): Merge two function names
% Do nothing if already the same.
merge_funcs(F,F,[]) :- !.                       % No repair if functors are the same
merge_funcs(F1,F2,[]) :-
  function(F1); function(F2),!.                       % No repair if functors are the functions
% Rename first to second if different
merge_funcs(F1,F2,[merge(F1,F2)]) :-
    F1\==F2.                               % Return repair if functors are different



%% Make two arities the same
% First find the two arities
same_arity([F1|Args1],[F2|Args2],Rs) :-
    length(Args1,L1), length(Args2,L2),           % Find arities of Fis
    same_arity2(F1,L1,F2,L2,Rs).                  % Return repair to make them the same

% Do nothing if arities the same.  Do not back up
same_arity2(_,L,_,L,[]) :- !.

% Find out which is longer and rearrange to put small first.
same_arity2(F1,L1,F2,L2,Rs) :-
    L1<L2, !, same_arity3(F1,L1,F2,L2,left,Rs).  % if smallest on left do nothing

same_arity2(F1,L1,F2,L2,Rs) :-
    L2<L1, !, same_arity3(F2,L2,F1,L1,right,Rs). % if smallest on right then switch


% Return just one of the possible repairs kind for repair.pl do further process.
/*
  same_arity3: Return just one of the possible repairs type
    F1: the function with shorter arities
    L1: the lengh of shorter arities.
    F2: the function with longer arities
    L2: the lengh of longer arities.
    Side: The position of the first input function of same_arity().
    Rs: the repair kind ([remove_n(F2,N,Side)] or [add_n(F1,N,Other)])
*/
same_arity3(F1,L1,F2,L2,Side,Rs) :-
    N is L2-L1,                                            % N is number of args to remove/add
    switch(Side,Other),                                    % Calculate the other side
    disjoin([remove_n(F2,N,Side)],[add_n(F1,N,Other)],Rs). % Either remove N from bigger or add N to smaller

% Suggest repair Rs that removes a function named F
remove_func(F,[F|_],[remove_func(F)]).

remove_func(F,[_|Args],Rs) :-  				  % Recurse on deeper arguments
    getfunction(F,Args,[Tf2,Posiiton]),       % Find position of [F|Args] in Args
    []\==Tf2,                      			  % Arg is the Ith argument
    I1 is Posiiton-1, length(Front,I1),       % Front will be Posiiton I-1 args
    append(Front,[_|Rest],Args),     		  % Rest is remain arguments in Args
    remove_func(F,Rest,Rs).         		  % Recurse on Arg


%% remove_occ(Posn,Exp,Rs): remove an occurence of variable X that occurs at Posn from Exp to give repairs Rs
remove_occ([I|_],[F|_],[remove_ith(F,I)]).  % Remove the Ith argument of F

remove_occ([I|Rest],[_|Args],Rs) :-   % Recurse on deeper arguments
    I1 is I-1, length(Front,I1),      % Front will be first I-1 args
    append(Front,[Arg|_],Args),       % Arg is the Ith argument
    remove_occ(Rest,Arg,Rs).          % Recurse on Arg

%% split_funcs(F1,F2): split functions if they are the same

% Do nothing if they are already different or they are functions and do not back up
split_funcs(F1,F2,[]) :- F1\==F2; function(F1); function(F2), !.

% Rename one if they are the same.
split_funcs(F,F,[rename(F)]).           % Return rename one functor

%% Make two arities different

% First find the two arities
diff_arity([F1|Args1],[F2|Args2],Rs) :-
    length(Args1,L1), length(Args2,L2),           % Discover two arities
    diff_arity2([F1|Args1],L1,[F2|Args2],L2,Rs).  % Return differentiating them

% Do nothing if arities are already different and do not back up
diff_arity2([_|_],L1,[_|_],L2,[]) :- L1\==L2, !.

% Change an arity if they are the same
diff_arity2([F|_],L,[F|_],L,[diff_arities(F,L)]) :- !. % Generic repair
