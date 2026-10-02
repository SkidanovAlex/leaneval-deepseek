import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.CastCard
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.NatCard
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Basic
import Mathlib.Order.SymmDiff
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.Basic

/-!
# Narrow Mathlib imports for the GKO chapter

Modules of this chapter that are on the import path of `Work.Deep.GKO.Deliverable` import this
module instead of `import Mathlib`.  The reason is import hygiene: `import Mathlib` pulls in the
root-level `Hypergraph` structure (`Mathlib.Combinatorics.Hypergraph.Basic`, which nothing else in
Mathlib imports), which makes `ErdosFaberLovaszConjecture.Hypergraph` ambiguous in any consumer
that opens that namespace -- in particular in the fixed `Solution.lean` and in `Submission.lean`.
Since that module is reachable only through `import Mathlib`, any list of specific Mathlib
modules is safe.
-/
