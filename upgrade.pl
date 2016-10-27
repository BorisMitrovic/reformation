/*
upgrade by Xue Li
*/

/*
Read ontology from a collection of fact assertions. (Expected format of the ontology.)
Ontology is the tree of the whole set of Cluases, with format Cluase;
GoalsTree is the tree of the goals/subgoals, with format of (negated_proposition, parent_axiom).
*/
initOntoGoal(Ontology, GoalsTree):-
	findall(Cluase,
					(fact(Cl), convertClause(Cl,Cluase)),
					Ontology), % convert all facts to internal representation
	% Find goal which is the negated axiom and then add it into goal tree as the top goal.
	findall((Goal,Clause),																	% Format of Goal: (negatedproposition, whole axiom, position)
					(	member(Clause,Ontology),										% get every axiom/literal
						member(Goal,Clause), 														% get every proposition in the axiom
						isGoal(Goal)),															% all the proposition is goal(negated)
					GoalsTree),
		vnl,vprint('GoalsTree is:'),vprintAll(GoalsTree).

finiteCost(Cost):- Cost=<10000, !.
upgrade:- retractall(found), upgrade(0).
/*
Nf,Nt is used for sort in quicksort->q_sort->pivoting.
FullRepairs is  list of all possible completed theories with corresponding Repairs;
So every element of FullRepairs is a set of repairs for the GoalsTree.
Repairs is the list of all repairs for every subgoal.
*/
upgrade(N):-
	initOntoGoal(InitialOnt,GoalsTree),									% Initialise ontology
	setof(	((Nf,Nt),(Repairs,UpgradedOut,N)),					% Find a set of all the repairs needed
					(
						derivation(InitialOnt,DerivedOnt,[],PairCl,0,ActualCost,GoalsTree,GoalsTreeR),		% Apply forward inference
						finiteCost(ActualCost),
						repair_uncompleted(DerivedOnt,[],UpgradedOut,PairCl,[],Repairs,GoalsTreeR,[]),	% Get repairs:Repairs
						costRepairs(Repairs,RepairCost), 							% find cost
						% finiteCost(RepairCost), assert(found),								% if minimal cost, then success
						RepairCost =< N, assert(found),								% if minimal cost, then success
						length(UpgradedOut,Nt),Nf=0),
					FullRepairs),										% get all needed repairs;
	vnl, vprint('FullRepairs '),
	quicksort(FullRepairs,RepairsSorted),
	% eliminateDuplicates(RepairsSorted,SetOfRepairs),		% sort and remove duplicate repairs
	% output each repair
	findall(Clause,fact(Clause),Clauses),
	nl, print('The original theory  : '), nl, printAll(Clauses),
	printOut(RepairsSorted).

upgrade(N) :- \+(found), N1 is N+1, upgrade(N1).				% No repairs found with minimal N1 repairs -> try N1+1
upgrade(_) :- retract(found),fail.							% Keep track if a repair is found

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/*
Input:
	InitialOnt: original set of clauses.
	GoalsInT((goal1,clause1), (goal2,clause2)...):	Input	GoalsTree whose nodes are the subgoal or maingoal propositions and clauses of these goals.
	PairInT [(P1,P1new),(P2,P2new)...] : Original propositions and their subsituted ones during resolution last time.
Output:
	PairOutT [(P1,P1new),(P2,P2new)...] : The PairOutT is a tree of pairs which are constituted by original propositions and their newest substituted ones.
	DerivedOnt	: Rest Clauses after resolution.
	GoalsOutT: The tree of (goals, clause)
% new inference, add to ontology, or new inconsistency, add to Proofs of contradiction
Recursion info: when resolution failed, go back to member(Clause2,AfterOnt), if it failed again, then go back to
member(Clause1,InitialOnt). If it sitll faied, then go to next definition of derivation.
*/
derivation(InitialOnt, DerivedOnt, PairInT, PairOutT, OldCost, ActualCost, GoalsInT, GoalsOutT):-
	finiteCost(OldCost),														% if cost within budget
	member(Clause1, InitialOnt),										% binary inference on every pair
	afterClause(Clause1, InitialOnt, AfterOnt),			% make sure every pair visited only once
	member(Clause2, AfterOnt),													% If there is rest clause for recursion, then continue.
	length(Clause1, L1), enum(L1, LS1), member(I1, LS1),
	length(Clause2, L2), enum(L2, LS2), member(I2, LS2),		% every member is an proposition like	[+[cap_of, [london], [britain]]]

	% If there is a goal (negated proposition), continue to resolve. Otherwise, pick next pair from	member((C2,P2),AfterOnt)
	resolution(Clause1, I1, Clause2, I2, NewC, PairInT, NewPair, GoalsInT, GoalsTree),			% resolve two ontology clauses by every pair of propositions
	NewCost = OldCost + 1,
	subtract(InitialOnt, [Clause1], Derive_ont1),							% delete resolved proposition and add new one
	subtract(Derive_ont1, [Clause2], Derive_ont2),
	% restart derive with new set of ontology
	derivation([NewC|Derive_ont2], DerivedOnt, NewPair, PairOutT, NewCost, ActualCost, GoalsTree, GoalsOutT).	% recall with added new clause (restart from line 56)

/*
	Only when the recursion goes to the end(recurse into the last member of axiom and [])
	or when the ActualCost is beyond the limit.
	or there are only one proposition in the whole set of aixoms.
	there is no more inference possible
	then ResOnt is the rest clauses of derivation; GoalsTree is the final result of goals
	PairOntNew is the final rest ontology for reforming.
*/
derivation(DerivedOnt, DerivedOnt, PairOntNew, PairOntNew, CurrentCost, CurrentCost, GoalsTree, GoalsTree) :- !,
	(	finiteCost(CurrentCost),
		vnl,vprint('End of Recursion ********************')
	;
		vnl,vprint('Upgrade Ontology failed,CurrentCost: '), vprint(CurrentCost)
	).

/*
 	1.Resolve a pair of propositions:I1th term of C1 and I2th term of C2 using reformation algorithm
  2.return new pair of propositions after substitution
	3.delete subgoals which has been resolved from search tree.


*	Only if there are both - & + propositions in theory, upgrade algorithm can be applied.
	There may be some sub goals left in the RestOnt Tree because of lacking + propositions.
	It is ok, since the algorithm will failed at the step of repair_uncompleted, as it should be.
	So we do not add goals when it is a pair of - & -. In summary, we only add goals in resolved clauses.
	Unpaired goals will be paired in recursion later or left in RestOnt for repair_uncompleted step.
*/
resolution(C1, I1, C2, I2, NewC, PairCin, NewPairT, GoalsIn, GoalsOut):-
	nth1(I1, C1, T1),							% for each pair of terms (T1 is the I1th element in list C1)
	nth1(I2, C2, T2),
	oppositeSigns(T1, T2, R1, R2),				% if opposite literals
  findgoal((T1, C1), (T2, C2), (Goal, Cgoal)),
	% if successful resolution
	reform3([R1], [R2], _, SubstOut, success, success, []),
	resultingClause(C1, I1, C2, I2, RestPs),	% RestPs is the rest propositions after resolution
	subst(SubstOut, RestPs, NewC),				% derive new clause, which is consitituted by substituted propositions

	% Resolved goal is subgoal from previous substitutions or original goals. Delete it from trees respectively.
	( member((_, Goal), PairCin),
		subtract(PairCin, (_, Goal), PairC2), 	% Delete resolved goal in Propositions Tree.
		GoalsSet = GoalsIn
	;
	  subtract(GoalsIn, [(Goal, Cgoal)], GoalsSet), % Delete resolved Goal form GoalsTree.
		PairC2 = PairCin
	),
	findGoals(NewC, C1, C2, GoalsNew),		% Add new goals
	append(GoalsSet, GoalsNew, GoalsOut),
	pairPro(PairC2, RestPs, NewC, NewPairT).		%  Add new substituted propositons and original ones (The pair is used in repair_uncompleted)




/*
  repair uncompleted literals
Input:
	OldOnt: 		The list of all rest clauses which are not resolved (Including goals).
	UpgradedIn:	The list of repaired clauses.
	PairProT:		The tree of original clauses and substituted clauses, such as [(O1,S1),(O2,S2)....].
	RsIn:				The list of repairs which have been found.
	GoalsIn:		The Goals tree with rest goals to be repaired.
Output:
	UpgradedOut: It is repaired during repair_uncompleted based on Goals.
	RsOut:			 New set of	Repairs.
	GoalsOut:		 New Goals tree which has removed resolved goal.
*/
repair_uncompleted(OldOnt, UpgradedIn, UpgradedOut, PairProT, RsIn, RsOut, GoalsIn, GoalsOut):-
	costRepairs(RsIn, M),
	finiteCost(M),								% if cost within budget
	member((G1, ClauseGoal), GoalsIn),  % repair goal G in format like -[parent,[camilla],[bill]]
	member(Clause1, OldOnt),										% binary inference on every pair
	length(Clause1, L1), enum(L1, LS1), member(I1, LS1),
	nth1(I1, Clause1, T1),		% T1 is the I1th proposition in C1.

	oppositeSigns(T1, G1, T2, G2),		% get a pair of propositions
	pairwise([T2], [G2], UnificationPair),
	reform2(UnificationPair, [], _, success, _, Repair),

	% If there was substitution, Use substituted proposition T1 to find repair, then reform its original proposition.
	(	member((OriginalP, T1), PairProT),						% Get Original clause according to substituted one (Clause1)
		( OriginalP = (-OP1) ; OriginalP = (+OP1) ),
			pairwise([OP1], [G2], UnificationPair2),
			[UIn] = UnificationPair2
	;
		\+member((_, T1), PairProT),  % If T1 is not the result of a substitution.
		[UIn] = UnificationPair
	),
	repairs(Repair, UIn, RepairedOnt),

	CompletedOnt = [RepairedOnt|UpgradedIn],

	RsMid = [Repair | RsIn],
	% Update rest ontology by deleting the pair of repaired propositions
	subtract(OldOnt, [Clause1], NewOnt1),							% delete axiom which repaired proposition belongs to
	subtract(NewOnt1, [ClauseGoal], NewOnt2),							% delete axiom which repaired goal belongs to
	subtract(Clause1, [T1], NewC1),							% get rest propositions by deleting repaired proposition
	subtract(ClauseGoal, [G1], NewCG),							% get rest propositions by deleting repaired goal
	append(NewOnt2, NewC1, RestOnt1),							% add rest proposition of the axiom which resolved proposition belongs to
	append(RestOnt1, NewCG, RestOnt),							% add rest proposition of the axiom which resolved proposition belongs to
	subtract(GoalsIn, [(G1,ClauseGoal)], GoalsTree),							% delete resolved proposition

	repair_uncompleted(RestOnt, CompletedOnt, UpgradedOut, PairProT, RsMid, RsOut, GoalsTree, GoalsOut). % continue repair rest goals.


% When both RestOntology and Goalstree are empty, the goals are fully proved. Return UpgradedOut & Repairs.
repair_uncompleted([], UpgradedOut, UpgradedOut, _, Repairs, Repairs, [], []):- !,
	vnl,vprint('Completed Ontology').

% When Goalstree is empty, there is still rest clauses,then empty clause is failed prooved.
repair_uncompleted(RestOntology, UpgradedOut, UpgradedOut, _, Repairs, Repairs, [], []):- !,
	\+ RestOntology = [],
	vnl, vprint('############## RestOntology=  '), vprint(RestOntology),
	vnl, vprint('Upgraded failed').

/*
	Negated proposition is the goal;
	If input is a negeted proposition, then return true.
	Otherwise, return false.
*/
isGoal(-_):- !.		% negated proposition is the goal.
findgoal((T1, C1), (T2, C2), Goal):-
	(T1=(-_), Goal = (T1, C1) ; Goal = (T2, C2)).


addGoal(Newgoal, OldGoalTrees, OldGoalTrees):-
	 member(Newgoal, OldGoalTrees).

addGoal([], OldGoalTrees, OldGoalTrees):- !.

addGoal(Newgoal, OldGoalTrees, NewGoalTrees):-
	[(T1,_)] = Newgoal,
	isGoal(T1),
	\+ member(Newgoal, OldGoalTrees),
	append(Newgoal, OldGoalTrees, NewGoalTrees).

printOut([H|T]):-
	nl, print('------------------ Repairs as below ------------------'),
	printUpgrOnto(H), printOut(T).
printOut([]):- !.

/*
UpgrOnto is a list whose element is in format of ((Nf,Nt),(Repairs,UpgradedOutology,N))
Repairs is a set of all repairs for Goalstree.
*/
printUpgrOnto(UpgrOnto):-
	UpgrOnto = ((_, Nt), (Repairs, UpgradedOut, N)),
	findall(C, member(C, UpgradedOut), Cs),								% Get every upgraded axiom from the whole set of completed theory.
	convertForm(Cs, OntologyR),
	length(Cs, Nr), Ni is Nt-Nr,

	nl, print('Minimal cost of repairs: '), print(N),		% display minimal cost
	print('  Number of inferences: '), print(Ni),			% display heuristic
	nl, print('Repairs: '),
	nl, printAll(Repairs),
	nl, print('The Upgraded Ontology: '), nl, printAll(OntologyR).

/*
Note:
	* OldPairTree & NewPairTree are the pairs based on [(proposition_original , proposition_substituted),...].
	* OldClause & NewClause are based on propositions, such as [+(), +(), -(), .....].
	* Use 'P' to represent for proposition, 'Ps' for propositions.
Input:
	Argument1: OldPairTree is ((P1original,P1new),(P2original,P2new)...)
	Argument2: OldPro [P1,P2,...]  P* is the old P which is left after resolution.
						 * OldPro is either the original Ps or which have been substituted before.
						 * We only store the original ones and update substituted Ps withh new substituted Ps.
	Argument3: NewPros	[P1new,P2new,...] P*new is the newest substituted P* after resolution.
Output:
	Argument4: NewPairTree is ((P1,P1new),(P2,P2new)...) PairOnt is constituted by original Ps and newest substituted Ps.
*/

pairPro(OldPairTree, OldPros, NewPros, PairTreeOut):-
		OldPros = [Hold | Told],	 % Hold is an old P (substituted one \ original one).
		NewPros = [Hnew | Tnew],   % Hnew is a newest P (last substituted one).

		% It is a pair of two Ps which are in the same position in OldPros and NewPros respectively.
		(	member((Hold,_), OldPairTree),
			updatePair(OldPairTree, Hold, Hnew, NewPairTree)	% If P is a substituted ones, this node should be already in the pairTree, then just update.
		;
			addPair(OldPairTree, Hold, Hnew, NewPairTree)			% If P is an original ones, add it.
		),
		pairPro(NewPairTree, Told, Tnew, PairTreeOut).  % continue pairing next Ps.

pairPro(OldPairTree, [], [], OldPairTree):- !.

% Add new substituted P.
addPair(OldPairTree, Original, Substituted, [(Original, Substituted)| OldPairTree]):- !.
addPair(OldPairTree, [], [], OldPairTree):- !.

% Update new substituted proposition and pair it with original clause.
updatePair(OldPairTree, SubOld, SubNew, OutPairTree):-
		subtract(OldPairTree, [(Original, SubOld)], PNew),				% Delete old node and get original P.
		append([(Original, SubNew)], PNew, OutPairTree).		% Add newest P pair into Tree.

updatePair(OldPairTree, [], [], OldPairTree):- !.


/*
Note:
	* Use 'P' to represent for proposition, 'Ps' for propositions.
Input:
	Argument1: Ps is [P1,P2,...], from clauses C1 and C2.
	Argument2: C1 is a parent clause of Ps
	Argument3: C2 is a parent clause of Ps
Output:
	GoalsTree:
*/

findGoals(Ps, C1, C2, GoalsTree):-
	findall((Goal, ParentClause),
					(	member(Goal, Ps), isGoal(Goal), 														% Find goal.
						(member(Goal, C1), ParentClause = C1; ParentClause = C2)),		% Find the parent clause of goal.
					GoalsTree).

findGoals([], _, _, []):- !.


/*
posArg([x,arg], [a, b, [x,arg], c, [a, [x,arg]]], Pos).
Pos is [3, [5,2]].

posArg(Element, List, PosnOut):-
  % length(List, L1), enum(L1, LS1), member(I1, LS1),
  (  append(Front, [Element|RestList], List),     % Use append backwards to identify each argument Arg in turn
      length(Front, I2),
      Posi1 is I2 + 1,
      posArg(Element, RestList, Posi2),
      append(Posi1, Posi2, PosnOut)
  ; 	% find deeper element
    	findall(P3,
            (	member(EL, List),
	            is_list(EL),
	            posArg(EL, List, P1),
	            posArg(Element, EL, P2),
	            P2 =\= [],
	            append(P1, P2, P3)),   % Work out I :what position of Arg in Args is
            PosnOut)       % Recurse on each argument
  ).

posArg(Exp, Exp, [1]):- !.               % The current expression is at the empty position
posArg([Exp], [Exp], [1]):- !.           % The current expression is at the empty position
posArg([Exp], [[Exp]], [1]):- !.         % The current expression is at the empty position
posArg(_, [], []):- !.            		   % The current expression is at the empty position
*/
