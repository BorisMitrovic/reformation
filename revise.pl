% Revises the ontology if inconsistent, until consistency is reached.
%% Boris Mitrovic, 16.05.13; revised on 11.06.16 %%

% Read ontology from a collection of fact assertions. (Expected format of the ontology.)
initOntology(Ontology) :-
	findall((CCl,[]),(fact(Cl), convertClause(Cl,CCl)),Ontology). % convert each fact to internal representation


% each clause in ontology contains parent clauses which inferred it:
% 		(clause,(leftPar,indexTermLeft,rightPar,indexTermRight))
% for initial clauses parents are []:
%		(clause,[])
% repairs should only be carried on parent clauses.

% Find minimal repair by incrementally increasing number of repairs allowed
revise :- retractall(found),revise(0).
/*
% revise using forward inference until no more inference possible.
% Repair the ontology if inconsistent and repeat.
% Find a cheapest (minimal edit distance) repair, which makes the ontology consistent.
Nf,Nt is used for sort in quicksort->q_sort->pivoting.
*/
revise(N) :-
	initOntology(Ontology),									% Initialise ontology
	setof(((Nf,Nt),(Repairs,Revised,N)),					% Find a set of all the repairs needed
		(revise2(Ontology,Revised,[],_,[],Repairs,N),		% Apply forward inference
		costRepairs(Repairs,M), 							% find cost
		M =< N, assert(found),								% if minimal cost, then success
		length(Revised,Nt),Nf=0),
		FullRepairs),										% get all needed repairs
	quicksort(FullRepairs,RepairsSorted),
	eliminateDuplicates(RepairsSorted,SetOfRepairs),		% sort and remove duplicate repairs
	% output each repair
	member(RepairSorted,SetOfRepairs),						% ** unify every sigle repair in the list of repairs (SetOfRepairs) to RepairSorrted
	RepairSorted = ((Nf,Nt),(Repairs,Revised,N)),

	findall(C,member((C,[]),Revised),Cs),
	length(Cs,Nr), Ni is Nt-Nr,
	nl, print('Minimal cost of repairs: '),print(N),		% display minimal cost
	print('  Number of inferences: '), print(Ni),			% display heuristic
	nl, print('Repairs: '),nl,
	printAll(Repairs),nl,
	print('Revised Ontology: '),nl,
	vnl,vnl,  printAll(Cs).

revise(N) :- \+(found), N1 is N+1, revise(N1).				% No repairs found with minimal N1 repairs -> try N1+1
revise(_) :- retract(found),fail.							% Keep track if a repair is found

/*
	eliminateDuplicates: eliminate all duplicate repairs
	Input: 	Reps
	Output:	Set
*/
% eliminate all duplicate repairs
eliminateDuplicates(Reps,Set) :-
	findall( ((Nf,Nt),(RepairsS,RevisedS,N)), 				% find a sorted list, then apply removeDups
		(
		member(Rep,Reps),
		Rep = ((Nf,Nt),(Repairs,Revised,N)),
		sort(Repairs,RepairsS),
		sort(Revised,RevisedS)
		), All),
	removeDups(All,Set).

% removes duplicates from a sorted list
removeDups([],[]) :- !.
removeDups([A|R],T) :- member(A,R), !, removeDups(R,T). 		% if A exists in remainder, then omit it
removeDups([A|R],[A|T]) :- \+(member(A,R)), removeDups(R,T).


% new inference, add to ontology, or new inconsistency, add to Proofs of contradiction
revise2(OldOnt,NewOnt,ProofsIn,ProofsOut,RsIn,RsOut,N) :-
	costRepairs(RsIn,M),
	M=<N,														% if cost within budget
	member((C1,P1),OldOnt),										% binary inference on every pair
	afterClause((C1,P1),OldOnt,AfterOnt),						% make sure every pair visited only once
	member((C2,P2),AfterOnt),
	length(C1,L1), enum(L1,LS1), member(I1,LS1),
	length(C2,L2), enum(L2,LS2), member(I2,LS2),

	resolve( (C1,P1),I1,(C2,P2),I2,[],_,(NewC,ParC) ),			% resolve two ontology clauses
	(	contradiction(NewC), 									% if contradiction
		\+(member((NewC,ParC),ProofsIn)), !,					% new inconsistency is inferred
		vnl,vprint('New Contradiction: '), vprint(NewC),		% print only if verbose switched on
		revise2(OldOnt,NewOnt,[(NewC,ParC)|ProofsIn],ProofsOut,RsIn,RsOut,N)	% recursive call with added contradiction proof
	;
		\+(contradiction(NewC)),								% if no contradiction
		\+(trivialInference(NewC,OldOnt)), !,					% if non trivial inference
		vnl,vprint('New Inference: '), vprint(NewC),
		revise2([(NewC,ParC)|OldOnt],NewOnt,ProofsIn,ProofsOut,RsIn,RsOut,N)	% recursive call with added new clause
	).

% no more inference possible and no inconsistencies found
revise2(Ont,Ont,[],[],Rs,Rs,_) :- !,
	vnl,vprint('Consistent Ontology').

% repair inconsistencies
revise2(OldOnt,NewOnt,ProofsIn,ProofsOut,RsIn,RsOut,N) :-
	costRepairs(RsIn,M),
	M=<N,								% if cost within budget
	detect(ProofsIn,Repairs),			% find all repairs, which would unblock one of the inconsistency proofs
	heuristic(H),
	chooseRepair(Repair,Repairs,H,OldOnt),	% choose repairs based on current heuristic
	repairOnt(OldOnt,RepOnt,Repair),	% apply the repair to the ontology

	RsMid = [Repair|RsIn],
	vnl,vprint('Repair applied: '), vprint(Repair),
	revise2(RepOnt,NewOnt,[],ProofsOut,RsMid,RsOut,N). % continue

% order repairs by heuristic computed
orderRepairs(Repairs,Ordered,OldOnt) :- findall(((Nf,Nt),Repair), (
		member(Repair,Repairs),
		repairOnt(OldOnt,RepOnt,Repair),		% apply current repair to the ontology
		nInconsistencies(RepOnt,Nf,Nt)			% compute number of inconsistencies (heuristic)
	), Pairs),
	quicksort(Pairs,Ordered).		% select maximal number of nInferences

% choose Repair based on current heuristic from Repairs
chooseRepair(Repair,Repairs,"iter",Ont) :-	% `iter` heuristic tries all repairs in order
	orderRepairs(Repairs,Ordered,Ont),
	member((_,Repair),Ordered).


chooseRepair(Repair,Repairs,"best",Ont) :- % efficient mode - only tries the best repair according to heuristic
	orderRepairs(Repairs,[(_,Repair)|_],Ont), !. % ,print(Ntf),nl

% find best repair
bestRepair(Repair,Repairs,OldOnt) :-
	member(Repair,Repairs),
	repairOnt(OldOnt,RepOnt,Repair),		% apply current repair to the ontology
	nInconsistencies(RepOnt,N),				% compute number of inconsistencies (heuristic)
	\+((member(R,Repairs),					% if there is no other repair with better heuristic
		repairOnt(OldOnt,ROnt,R),			% then it's the best repair according to the heuristic
		nInconsistencies(ROnt,M),
		M < N )),
	!.

% number inconsistencies and number inferences
nInconsistencies(Ont,Nf,Nt) :- nInconsistencies2(Ont,[],Incons), length(Incons,Nf), length(Ont,Nt). % convert to internal format
nInconsistencies2(Ont,ProofsIn,ProofsOut) :-
	member((C1,P1),Ont),								% for each pair of clauses
	afterClause((C1,P1),Ont,AfterOnt),
	member((C2,P2),AfterOnt),
	length(C1,L1), enum(L1,LS1), member(I1,LS1),
	length(C2,L2), enum(L2,LS2), member(I2,LS2),
	resolve( (C1,P1),I1,(C2,P2),I2,[],_,(NewC,ParC) ),	% resolve
	(	contradiction(NewC),
		\+(member((NewC,ParC),ProofsIn)), !,					% new inconsistency is inferred
%		vnl,vprint('New Contradiction: '), vprint(NewC),
		nInconsistencies2(Ont,[(NewC,ParC)|ProofsIn],ProofsOut)	% count contradictions
	;
		\+(contradiction(NewC)),
		\+(trivialInference(NewC,Ont)), !,
%		vnl,vprint('New Inference: '), vprint(NewC),
		nInconsistencies2([(NewC,ParC)|Ont],ProofsIn,ProofsOut) % count inferences
	).

% no more inference possible and no inconsistencies found
nInconsistencies2(_,Proofs,Proofs) :- !.
%	vnl,vprint('Inferred Ontology').

/*
costRepairs (R, C): calculate the cost C by split R into members one by one.
costRepair （_,_,C）:C is 0 when (R,_) is a member of Rs, otherwise C is 1.
*/
% if a name was already split, then additional splits to the same name are free
costRepairs([],0) :- !.
costRepairs([R|Rs],C) :- costRepair(R,Rs,C1), costRepairs(Rs,C2), C is C1 + C2.

costRepair((R,_),Rs,0) :- member((R,_),Rs), !.
costRepair(_,_,1).

% detect all possible repairs to block any of the contradiction proofs
detect(Proofs,Repairs) :-
	setof((Rs,Cl,I), Proof^
		(member(Proof,Proofs),			% use any suggested repair from any proof tree
		detect1(Proof,Rs),
		detect2(Proof,(Rs,Cl,I)),
		detect3((Rs,Cl,I)))
	,Repairs).

% detects possible repairs
detect1([],_,_) :- !, fail.

% detects false equality contradiction repairs
detect1(([+([==|[X,Y]])],Par), Rs) :-
	X\=Y, reform3([X],[Y],[],_,success,fail,Rs);
	!, detect1(Par,Rs).

% detects false inequality contradiction repairs
detect1(([-([==|[X,X]])],Par), Rs) :-
	reform3([X],[X],[],_,fail,success,Rs);
	!, detect1(Par,Rs).

% empty clause contradiction, only parent repairs
detect1(([],Par), Rs) :-
	!, detect1(Par,Rs).

% repairs given parent resolution
detect1(((C1,_),I1,(C2,_),I2),Rs) :-
	nth1(I1,C1,T1),
	nth1(I2,C2,T2),
	oppositeSigns(T1,T2,R1,R2),
	reform3([R1],[R2],[],_,fail,_,Rs).

% repairs given ancestor resolution (not parent) ????
detect1(((_,Par1),_,(_,Par2),_),Rs) :-		% or repairs higher up the tree
	detect1(Par1,Rs);
	detect1(Par2,Rs).

% find where repairs apply recursively on the proof tree
detect2((_,((Cl1,Par1),I1,(Cl2,Par2),I2)),(Rs,Cl,I)) :-
detect2( ((Cl1,Par1),I1,(Cl2,Par2),I2),(Rs,Cl,I)).

detect2(((Cl1,Par1),I1,(Cl2,Par2),I2),(Rs,Cl,I)) :-
	(Par1=[],
	I = I1,
	Cl = Cl1);
	(Par2=[],
	I=I2,
	Cl=Cl2);
	detect2(Par1,(Rs,Cl,I));
	detect2(Par2,(Rs,Cl,I)).

detect3((Rs,Cl,I)) :-
	nth1(I,Cl,T),
	repairs(Rs,NReps,T,_),		% count repairs applicable
	sensibleRep(Rs,Cl),
	NReps \= 0.					% some repairs can be applied



% apply the repair to the clause in the ontology
repairOnt(OldOnt,RepOnt,(Rs,RepCl,I)) :-
	nth1(I,RepCl,TIn),
	findall((Cl,[]),member((Cl,[]),OldOnt),LeafOnt),		% apply only to parent clauses
	remove((RepCl,[]),LeafOnt,OntR),
	repairs(Rs,_,TIn,TOut),
	I1 is I-1,
	append(B,[_|E],RepCl), length(B,I1),
	append(B,[TOut|E],ClOut), !,
	RepOnt = [(ClOut,[])|OntR].

% resolution of I1th term of C1 and I2th term of C2 using reformation algorithm
resolve( (C1,P1),I1,(C2,P2),I2,SubstIn,SubstOut,(NewC,((C1,P1),I1,(C2,P2),I2)) ) :-
	nth1(I1,C1,T1),							% for each pair of terms (T1 is the I1th element in list C1)
	nth1(I2,C2,T2),
	oppositeSigns(T1,T2,R1,R2),				% if opposite literals
	reform3([R1],[R2],SubstIn,SubstOut,success,success,[]),		% if successful resolution
	resultingClause(C1,I1,C2,I2,C),
	subst(SubstOut,C,NewC).					% derive new clause

% is the clause a contradiction clause? Hardcode equality meaning  reform3 ？？？
contradiction(Clause) :-
	Clause=[], !;
	Clause= [+([==|[X,Y]])], reform3([X],[Y],[],_,success,fail,_), !;   	   % + a=b
	Clause= [-([==|[X,Y]])], reform3([X],[Y],[],_,success,success,[]).		   % - x=x

% is inferred clause trivially true or already known?
trivialInference(Clause,Ont) :-
	member((Clause,_),Ont);
	removeDups(Clause,ClauseDedup), Clause \== ClauseDedup;
	Clause= [+([==|[X,Y]])], reform3([X],[Y],[],_,success,success,[]);		   % + x=x
	Clause= [-([==|[X,Y]])], reform3([X],[Y],[],_,success,fail,_).   		   % - a=b

% To run use:
%	notrace,[diagnose,repair,reform,revise,util,utilRevise,ontology], revise.
