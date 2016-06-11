# Reformation
Automatic ontology repair using Reformation algorithm, originally written by Alan Bundy.

Requires `SWI-Prolog` (http://www.swi-prolog.org/).  See also a reformation algorithm for Multi-sorted logic: https://github.com/BorisMitrovic/sorted-reformation

To run a sample capital_of ontology, run in SWI-Prolog: 
  > [diagnose,repair,util,reform,revise,utilRevise,capOf]. revise.
  
Replace capOf with another ontology file, to repair another ontology. Ontology file is a collection of `fact` definitions. See `ontology.pl` or `capOf.pl` for an example.

General structure of the code:
 - `revise.pl`: Revises the ontology to a consistent state. Finds minimal repairs and repairs the ontology.
 - `reform.pl`: Performs a reformation algorithm. Either blocks a successful unification, if failure wanted, or unblocks a failed unification if success wanted.
 - `diagnose.pl`: Finds all possible repairs, which could unblock the unification.
 - `repair.pl`: Applies the repairs to either unification, or ontology repairs to the ontology.
 - `utilRevise.pl`: General utility functions for revise algorithm.
 - `util.pl`: General utility functions.
