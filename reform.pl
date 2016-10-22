%% Reformation Procedure %%
%% Alan Bundy, 16.2.12 %%
%% Revised By Boris Mitrovic, 16.05.13; 11.06.16 %%

%% Representation: variables are vble(X); compound terms are [Func|Args], where
%% Args can be empty list if Func is constant.

%% Unification problems and substitutions are both lists of equations E1=E2. For
%%  substitutions E1 is always vble(X) for some X.


%% reform(E1,E2,Sigma,W,FS,Rs): unify E1 and E2 with substitution Sigma,
%% result FS (fail/success) and what was wanted. Return repairs Rs.

reform(E1,E2,Sigma,W,FS,Rs) :-              % accept singleton even if not in list format
    \+(is_list(E1)), !,
    reform([E1],E2,Sigma,W,FS,Rs).

reform(E1,E2,Sigma,W,FS,Rs) :- 
    \+(is_list(E2)), !,
    reform(E1,[E2],Sigma,W,FS,Rs).

reform(E1S,E2S,Sigma,W,FS,Rs) :-            % Internal format assumes E1 and E2 are lists
    maplist(convert,E1S,NE1S),              % Convert inputs to internal format
    maplist(convert,E2S,NE2S),
    pairwise(NE1S,NE2S,NE),                 % Unify each pair of items in a list
    reform2(NE,[],Sigma,W,FS,Rs).           % Call reformation on internal form


% reform3 converts to internal representation

reform3(F1,F2,SigmaIn,SigmaOut,W,FS,Rs) :-
    pairwise(F1,F2,Ne),
    reform2(Ne,SigmaIn,SigmaOut,W,FS,Rs).

% Pretty print current state (Handy for debugging)
% reform2(EL,SigmaIn,_,_,_,_,_) :-
%    verbose(on),
%    print('* Problem: '), pprint(EL), nl,
%    print('* Substitution: '), pprint(SigmaIn), nl, nl, fail.


%% reform2(EL,SigmaIn,SigmaOut,W,FS,Rs): Unify expression list EL with input
%% substitution SigmaIn and output SigmaOut, result FS (fail/success) and
%% repairs Rs. Success is asserted

% Base case (wanted failure)
reform2([],SigmaIn,SigmaIn,fail,success,_) :-    % Fail if failure wanted, but base case is successful
    (refsuccess; assert(refsuccess)),            % Mark successful unification (assert only one fact)
    !, fail.                                     % Failure wanted, but unification succeeds, so fail 

% Base case (wanted success)
reform2([],SigmaIn,SigmaIn,success,success,[]) :-   % When no more problems, succeed with empty substitution
    (refsuccess; assert(refsuccess)),               % Assert only one fact
    !.                                  

% Case CC_s: success on two compound expressions. F1=F2 and length Arg1 and
% length Arg2 the same.

reform2([[F1|Args1]=[F2|Args2]|Old],SigmaIn,SigmaOut,W,FS,Rs) :- 
    F1==F2, length(Args1,L), length(Args2,L),       % If functors and arities agree
    pairwise(Args1,Args2,New),                      % Pair up corresponding subterms
    append(New,Old,Rest),                           % Add them to the Old problems
    (reform2(Rest,SigmaIn,SigmaOut,W,FS,Rs);        % Repair either from recursive part
    refsuccess(FS2),                                % Gets the asserted FS value from the end of recursion
    diagnose(W,FS2,[F1|Args1]=[F2|Args2],Rs),       % Or repair from diagnosing current unification
    \+(Rs=[])).                                     % Only if diagnosing finds a repair


% Case CC_f: failure on two compound expressions. F1/=F2, or length Arg1 and
% length Arg2 different.

reform2([[F1|Args1]=[F2|Args2]|_],_,_,_,fail,_) :-              
    (F1\==F2 ; length(Args1,L1), length(Args2,L2), L1\==L2),   % if functors or arities disagree
    retractall(refsuccess), fail.                              % mark failure for recursion

reform2([[F1|Args1]=[F2|Args2]|_],_,_,fail,fail,_) :-          % If failure wanted then fail
    (F1\==F2 ; length(Args1,L1), length(Args2,L2), L1\==L2).   % if functors or arities disagree

% Failure unwanted -> repair
reform2([[F1|Args1]=[F2|Args2]|Rest],SigmaIn,SigmaOut,success,fail,Rs) :- % If failure unwanted
    (F1\==F2 ; length(Args1,L1), length(Args2,L2), L1\==L2), !,           % but functors or arities disagree
    diagnose(success,fail,[F1|Args1]=[F2|Args2],Rs1),                     % Diagonose a repair
    repairs(Rs1,[F1|Args1]=[F2|Args2],U),                                 % Apply it
    reform2([U|Rest],SigmaIn,SigmaOut,success,_,Rs2),                     % Continue reformation with repaired problem
    append(Rs1,Rs2,Rs).                                                   % Conjoin first repair with any more found. 

% Case VC: a variable vs a compound expression. 

% Switch expressions if in wrong order
reform2([[F|Args]=vble(X)|Rest],SigmaIn,SigmaOut,W,FS,Rs) :- !,   
    reform2([vble(X)=[F|Args]|Rest],SigmaIn,SigmaOut,W,FS,Rs).     % Reorient problem to put variable first

% Case VC_f: variable occurs in term E then fail
reform2([vble(X)=[F|Args]|_],_,_,fail,fail,_) :-             % If failure wanted then fail
     occurs(vble(X),[F|Args]), !.                            % if var occurs in expression

% Failure unwanted -> repair
reform2([vble(X)=[F|Args]|Rest],SigmaIn,SigmaOut,success,fail,Rs) :-   % If failure unwanted
    occurs(vble(X),[F|Args]), retractall(refsuccess), !,               % but var occurs in expression differ
    diagnose(success,fail,vble(X)=[F|Args],Rs1),                       % Diagnose a repair
    repairs(Rs1,vble(X)=[F|Args],U),                                   % Apply it
    reform2([U|Rest],SigmaIn,SigmaOut,success,_,Rs2),                  % Continue reformation with repaired problem
    append(Rs1,Rs2,Rs).                                                % Conjoin first repair with any more found. 

% Case VC_s: variable does not occur in terms 
reform2([vble(X)=[F|Args]|Rest],SigmaIn,SigmaOut,W,FS,Rs) :- 
    \+ occurs(vble(X),[F|Args]),                              % If var does not occur in expression
    (W=success,                                               % If unblocking, then permute to ensure minimal repair 
    containsDifferent(vble(X),[F|Args],Rest),                 % Check if more than one occurance of the same variable with different instantiation
    reform2(Rest,SigmaIn,SigmaMid,W,FS1,Rs1),                 % First reform rest
    subst(SigmaMid,[vble(X)=[F|Args]], NewCurr),              % Apply substitutions obtained
    reform2(NewCurr, SigmaMid, SigmaOut, W, FS2, Rs2),        % Followed by reforming the current
    and(FS1,FS2,FS),                                          
    append(Rs1,Rs2,Rs),                                       % Append repairs, since unblocking
    \+(Rs=[]);                                                % If no repairs found, don't duplicate
    subst(vble(X)/[F|Args],Rest,NewRest),                     % Substitute expression for var in problems
    subst(vble(X)/[F|Args],SigmaIn,SigmaMid1),                % Substitute expression for var in substitution
    compose(vble(X)/[F|Args],SigmaMid1,SigmaMid2),            % Compose new substitution with old one
    (reform2(NewRest,SigmaMid2,SigmaOut,W,FS,Rs);             % Either recursive repair with new problem and substitution
    refsuccess(FS2),                                          % Gets the FS value from the end of recursion
    diagnose(W,FS2,vble(X)=[F|Args],Rs),                      % Or repair from diagnosing current unification
    \+(Rs=[]))).                                              % Only if diagnosing finds a repair


% Case VV: a variable vs a variable

% Case VV=: variables are already the same
reform2([vble(X)=vble(X)|Rest],SigmaIn,SigmaOut,W,FS,Rs) :-   % If two vars and same then
    reform2(Rest,SigmaIn,SigmaOut,W,FS,Rs).                   % ignore them and carry on with the rest

% Case VV/=: variables are different
reform2([vble(X)=vble(Y)|Rest],SigmaIn,SigmaOut,W,FS,Rs) :-   
    X\==Y,                                                    % If two vars and different then
    Subst1 = vble(X)/vble(Y),                                 % some subst needed
    compose(Subst1,SigmaIn,SigmaMid),                         % Compose new substitution with old one
    subst(SigmaMid,Rest,NewRest),                             % substitute one for the other in the problems
    (reform2(NewRest,SigmaMid,SigmaOut,W,FS,Rs);              % Recurse with new problem
    refsuccess(FS2),                                          % Get success from recursion
    diagnose(W,FS2,vble(X)=vble(Y),Rs),                       % Repair from diagnosing current unification
    \+(Rs=[])).                                               % Only if diagnosing finds a repair
