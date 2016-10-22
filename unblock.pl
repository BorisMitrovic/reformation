/*
Unblock by Xue Li
*/

/*
initPair : Translate into internal representation and pairs up corresponding elements of two lists
output: NE, a list  of unify iterms [[F|Args]=[F2,Args2]]
*/
initPair(NE, Ontology):-
	findall(Cl,fact1(Cl),Ontology),          % convert each fact to internal representation
	member(C1,Ontology),										% binary inference on every pair
	afterClause(C1,Ontology,AfterOnt),		 % make sure every pair visited only once
	member(C2,AfterOnt),
	% nl,print('C1:'), print(C1),
  maplist(convert, C1, NE1S),          % convert Fact1 into internal representation NE1S
  maplist(convert, C2, NE2S),          % convert Fact2 into internal representation NE2S
  pairwise(NE1S,NE2S,NE).                 % Unify each pair of items in a list NE
	% nl,print('NE:'), print(NE).


%		Ontology = [([+[stepmum, [camilla], vble(william)]], []),  ([-[stepmum, [vble, vble(...)], [vble|...]], +[parent, [vble|...], [...|...]]], []),  ([-[parent2, [camilla], vble(...)|...]], [])].

unblock:- retractall(found), unblock(0).

unblock(N):-
  initPair(NE,Ontology),			% NE:		[[F|Args]=[F2,Args2]]

  [UIn]= NE,				% UIn: 	[F|Args]=[F2,Args2]
	setof(	((Nf,Nt),(Repairs,[Unblockeds],N)),					% Find a set of all the repairs needed
					(
						% get repaired theory Rout:[parent,vble(x),vble(y)]=[parent,[camilla],[bill]]
						reform2(NE,[],_,success,_,Repairs),
						repairs(Repairs,UIn,Unblockeds),		% Apply forward inference
						costRepairs(Repairs,M), 							% find cost
						M =< N, assert(found),								% if minimal cost, then success
						length([Unblockeds],Nt),Nf=0),
					FullRepairs),														% get all needed repairs

	quicksort(FullRepairs,RepairsSorted),
	eliminateDuplicates(RepairsSorted,SetOfRepairs),		% sort and remove duplicate repairs

	% print('SetOfRepairs:	'),print(SetOfRepairs),nl,
	% output each repair
	member(RepairSorted,SetOfRepairs),						% ** unify every sigle repair in the list of repairs (SetOfRepairs) to RepairSorrted
	RepairSorted = ((Nf,Nt),(Repairs,Unblocked,N)), % **?

	findall(C,member(C,Unblocked),Cs),
	length(Cs,Nr), Ni is Nt-Nr,
	convertForm(Cs, OntologyR),

	% print screen the repaired theory
  nl, print('Minimal cost of repairs: '),print(N),		% display minimal cost
	print('  Number of inferences: '), print(Ni),			% display heuristic
	nl, print('Repairs: '),nl,
	print(Repairs),nl,nl,
	nl, print('The original theory  : '), nl, printAll(Ontology),
	nl, print('The repaired Ontology: '), nl, printAll(OntologyR).

	unblock(N) :- \+(found), N1 is N+1, unblock(N1).				% No repairs found with minimal N1 repairs -> try N1+1
	unblock(_) :- retract(found),fail.							% Keep track if a repair is found

/*
convertForm : convert the form of Cs into the original form of ontology
Input [C1=C2]:[[F,Args]=[F2,Args2]] [loves,vble(x),vble(x)]
Output Ontology: [F(Args),F2(Args2)]
*/
	convertForm([C1 = C2], Ontology):-
		maplist(revert, C1,Clause1),
		maplist(revert, C2,Clause2),  % list form: [Functor | Args]
		Fact1=..Clause1,							% fact form: Functor(Args)
		Fact2=..Clause2,
		Ontology = [[Fact1],[Fact2]].

/*
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


%为什resolve 一定只用substOut，而不用RS呢

resolve( (C1,P1),I1,(C2,P2),I2,SubstIn,SubstOut,(NewC,((C1,P1),I1,(C2,P2),I2)) ) :-
	nth1(I1,C1,T1),							% for each pair of terms
	nth1(I2,C2,T2),
	oppositeSigns(T1,T2,R1,R2),				% if opposite literals
	reform3([R1],[R2],SubstIn,SubstOut,success,success,[]),		% if successful resolution
	resultingClause(C1,I1,C2,I2,C),
	subst(SubstOut,C,NewC).					% derive new clause

heuristic

resolve(([-[cap_of, vble(x), [britain]], +[==, vble(x), [london]]], ([+[cap_of, [london], [...]]], []), 1, ([-[cap_of|...], -[...|...], + ...], []), 2), 1, ([+[cap_of, [london], [britain]]], []), 1, [], [vble(x)/[london]], ([+[==, [london], [london]]], ([-[cap_of, vble(x), [...]], +[==, vble(...)|...]], ([+[cap_of|...]], []), 1, ([- ...|...], []), 2), 1, ([+[cap_of|...]], []), 1))
				([-[cap_of, vble(x), [...]], +[==, vble(...)|...]], ([+[cap_of|...]], []), 1, ([- ...|...], []), 2), 1, ([+[cap_of|...]], []), 1)
*/
