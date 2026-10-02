/-
# A narrow Mathlib prelude

The workspace's trusted statement (`ChallengeDeps.lean`, `Solution.lean`) declares
`ErdosFaberLovaszConjecture.Hypergraph` and writes `Hypergraph` unqualified under
`open ErdosFaberLovaszConjecture`.  Mathlib declares a *root-level* structure `Hypergraph`
(in `Mathlib/Combinatorics/Hypergraph/Basic.lean`), which is imported by nothing in Mathlib
except the root module `Mathlib`; importing it would make `Hypergraph` ambiguous and break the
trusted files.

Every module of this chapter therefore imports this prelude (a list of the specific Mathlib
modules the chapter uses) instead of `import Mathlib`.  All the listed modules are safe: none
of them imports the root `Hypergraph` structure.
-/
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Piecewise
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.SetTheory.Cardinal.NatCard
