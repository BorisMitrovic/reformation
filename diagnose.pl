%% Diagnose Unification Problems and Suggest Repairs %%
%% Alan Bundy, 30.1.12 %%
%% Revised By Boris Mitrovic, 16.05.13; 11.06.16 for ontology repair %%

%% diagnose(W,FS,Eq,Rs): if result from Eq unwanted W\=FS then suggest repairs
%% Rs to signature

% Do nothing if result is as wanted. Do not back up
diagnose(FS,FS,_,[]) :- !.

% Suggest repair if success wanted but failure produced. 

% Case CCf repairs: merge functors and make same arity
diagnose(success,_,T,T,[]):-!.
diagnose(success,fail,X1,X2,Rs):-
    X1 \= vble(_),
    X2 \= vble(_),
    \+is_list(X1),
    \+is_list(X2),
    !,
    (
        Rs = [merge(X1,X2,left)]
        ;
        Rs = [merge(X2,X1,right)]
    ).

/*diagnose(success,fail,[X1],[X2],[merge(X1,X2)]):-
    X1 \= vble(_),
    X2 \= vble(_),
    \+is_list(X1),
    \+is_list(X2),
    !.*/
diagnose(success,fail,vble(X1),X2,[substitute(vble(X1),X2)]):-
    \+contains_term(vble(X1),X2),
    !.
diagnose(success,fail,X1,vble(X2),[substitute(vble(X2),X1)]):-
    \+contains_term(vble(X2),X1),
    !.
/*
% Occurs-in.
% not complete.
diagnose(success,fail,vble(X1),X2,Rs):-
    contains_term(vble(X1),X2),
    vble(X1) \= X2,
    add_func(vble(X1),left,Rs),
    !.
diagnose(success,fail,X1,vble(X2),Rs):-
    contains_term(vble(X2),X1),
    vble(X2) \= X1,
    add_func(vble(X2),right,Rs),
    !.
*/   

diagnose(success,fail,[X1|L1],[X2|L2],Rs):-
    list_depth([X1|L1],Dep1),
    list_depth([X2|L2],Dep2),
    (
        Dep1 < Dep2,
        (
            add_func(X1,L1,left,Rs)
            ;
            del_func(X2,L2,right,Rs)
        )
        ;
        Dep1 > Dep2,
        (
            add_func(X2,L2,right,Rs)
            ;
            del_func(X1,L1,left,Rs)
        )
    ).

diagnose(success,fail,[X1|L1],[X2|L2],Rs):-
    length(L1,Len1),
    length(L2,Len2),
    Len1 \= Len2,
    !,
    unify_arity([X1|L1],[X2|L2],Rs).

diagnose(success,fail,[X1|L1],[X2|L2],Rs):-
    length(L1,Len),
    length(L2,Len),
    !,
    (
        Len > 0,
        (
            X1 \= X2,
            Rs1 = []
            ;
            permute(X1,L1,Rs1,left)
            ;
            permute(X2,L2,Rs1,right)
        ),
        diagnose(success,fail,X1,X2,Rs2),
        append(Rs1,Rs2,Rs)
        ;
        Len = 0,
        X1 \= X2,
        diagnose(success,fail,X1,X2,Rs)
        ;
        X1 = X2,
        diagnose_arguments(success,fail,L1,L2,Rs)
    ).

diagnose_arguments(success,fail,[X1|L1],[X2|L2],Rs):-
    length(L1,Len),
    length(L2,Len),
    !,
    (
        X1 \= X2,
        diagnose(success,fail,X1,X2,Rs)
        ;
        X1 = X2,
        diagnose_arguments(success,fail,L1,L2,Rs)
    ).


%permute(_,_,_,_):-!,fail.
permute(X,Args,[permute(X,P,Dir)],Dir):-
    length(Args,Len),
    numlist(1,Len,L),
    permutation(P,L),
    P \= L.

list_depth([],0):-!.
list_depth(X,fst):-
    atom(X),
    !.    
list_depth(vble(_),1):-!.
list_depth([X|L],D):-
    list_depth(X,D1),
    list_depth(L,D2),
    (
        D1 = fst,
        D is D2 + 1
        ;
        D1 \= fst,
        D1 > D2,
        D = D1
        ;
        D1 \= fst,
        D1 =< D2,
        D = D2
    ).


:- dynamic new_func/1.
:- retractall(new_func(_)).
:- assert(new_func(0)).
add_func(X,Arg,Dir,[addfunc(X,L,F1,Dir)]):-
    length(Arg,L),
    new_func(N),
    retractall(new_func(_)),
    N1 is N + 1,
    assert(new_func(N1)),
    atom_concat('newfunc',N1,F1),
    !.

del_func(X,Arg,Dir,Rs):-
    length(Arg,L),
    L1 is L - 1,
    for(I,0,L1),
    Rs = [delfunc(X,L,I,Dir)].

:- dynamic new_argc/1.
:- retractall(new_argc(_)).
:- assert(new_argc(0)).
get_new_argc(C):-
    new_argc(N),
    retractall(new_argc(_)),
    N1 is N + 1,
    assert(new_argc(N1)),
    atom_concat('newargc',N1,C),
    !.

/*
% Stable version.
unify_arity([X1|L1],[X2|L2],Rs):-
    length(L1,Len1),
    length(L2,Len2),
    (
        Len1 > Len2,
        N is Len1 - Len2,
        (
            Rs = [addargs(X2,Len2,N,right)]
            %;
            %Rs = [delargs(X1,N,left)]
        )
        ;
        Len1 < Len2,
        N is Len2 - Len1,
        (
            Rs = [addargs(X1,Len1,N,left)]
            %;
            %Rs = [delargs(X2,N,right)]
        )
    ).

*/

unify_arity([X1|L1],[X2|L2],Rs):-
    length(L1,Len1),
    length(L2,Len2),
    (
        Len1 > Len2,
        (
            for(N,0,Len2),
            get_new_argc(C),
            Rs = [addargc(X2,Len2,N,C,right)]
            ;
            for(N,0,Len2),
            Rs = [addargv(X2,Len2,N,right)]
            ;
            N1 is Len1 - 1,
            for(N,0,N1),
            Rs = [delarg(X1,Len1,N,left)]
        )
        ;
        Len1 < Len2,
        (
            for(N,0,Len1),
            get_new_argc(C),
            Rs = [addargc(X1,Len1,N,C,left)]
            ;
            for(N,0,Len1),
            Rs = [addargv(X1,Len1,N,left)]
            ;
            N1 is Len2 - 1,
            for(N,0,N1),
            Rs = [delarg(X2,Len2,N,right)]
        )
    ).

% Case VCf repairs: remove occurrences of X
diagnose(success,fail,vble(X)=[F|Args],Rs) :- !, 
    position(vble(X),[F|Args],Posn),     % Find position that X occurs at
    remove_occ(Posn,[F|Args],Rs).        % Suggest repair Rs that removes an argument that X occurs in

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


% Return just one of the possible repairs
same_arity3(F1,L1,F2,L2,Side,Rs) :-
    N is L2-L1,                                            % N is number of args to remove/add
    switch(Side,Other),                                    % Calculate the other side
    disjoin([remove_n(F2,N,Side)],[add_n(F1,N,Other)],Rs). % Either remove N from bigger or add N to smaller

%% remove_occ(Posn,Exp,Rs): remove an occurence of variable X that occurs at Posn from Exp to give repairs Rs
remove_occ([I|_],[F|_],[remove_ith(F,I)]).  % Remove the Ith argument of F

remove_occ([I|Rest],[_|Args],Rs) :-   % Recurse on deeper arguments
    I1 is I-1, length(Front,I1),      % Front will be first I-1 args
    append(Front,[Arg|_],Args),       % Arg is the Ith argument
    remove_occ(Rest,Arg,Rs).          % Recurse on Arg

%% split_funcs(F1,F2): split functions if they are the same

% Do nothing if they are already different and do not back up
split_funcs(F1,F2,[]) :- F1\==F2, !.

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
