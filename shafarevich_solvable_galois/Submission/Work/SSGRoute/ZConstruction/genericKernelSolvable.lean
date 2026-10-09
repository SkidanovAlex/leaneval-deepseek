import Mathlib
import Submission.Work.SSGRoute.theorem15_scholz
import Submission.Work.SSGRoute.genericKernelSolvable_of_flowSolutions
import Submission.Work.SSGRoute.minimalNormalKernelStep_of_genericKernelSolvable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `GenericKernelSolvable`, and the landmark's deep input, from the SSGRoute DAG

`Work.GenericKernelReduction.GenericKernelSolvable`
(`Submission/Work/GenericKernelReduction/Defs.lean`) is the generic-kernel form of the split
embedding theorem over `ℚ`; it is the single hypothesis under the landmark
`Submission.shafarevich_solvable_galois`, through

  `Submission.MinimalNormalKernelStep` ⟸ `GenericKernelSolvable`
    (`Work.SSGRoute.minimalNormalKernelStep_of_genericKernelSolvable`),
  `MinimalNormalKernelStep` ⟹ `Submission.shafarevich_solvable_galois`
    (`Submission.realizable_of_solvable_of`).

This file supplies both statements from the SSGRoute DAG:

* `flowSolutions` — the *flow* form of Theorem 15 of Schmidt–Wingberg over `ℚ`: for every prime
  `p`, every finite normal `K/ℚ` with `μ_{p^{i+1}} ⊆ K`, every `1 ≤ j ≤ i` and every `n ≥ 1` there
  is a proper continuous solution of the split generic embedding problem into
  `F(n)/F(n)^{(i,j)} ⋊ Gal(K/ℚ)`.  It is the projection of
  `Work.SSGRoute.theorem15_scholz` (the SSGRoute DAG's top node, whose proof on disk is complete
  and whose transitive `sorry`-owners are the four declared inputs listed in
  `PING_genericKernelSolvable_obligation_card.md`) onto the flow conditions;
* `genericKernelSolvable` — `GenericKernelSolvable` itself, from `flowSolutions` through the
  *proved* reduction `Work.SSGRoute.genericKernelSolvable_of_flowSolutions` (which constructs the
  `Gal(K/ℚ)`-equivariant surjection of the flow group onto the generic kernel from
  `Work.SSGRoute.equivariant_flowQuotient_surjection` and solves the split embedding problem by
  `Work.SSGRoute.splitEmbeddingSolvable_of_surjective_lift`);
* `minimalNormalKernelStep_proved` — the landmark's deep input `Submission.MinimalNormalKernelStep`
  from `genericKernelSolvable` (universe transport along `Shrink` is inside
  `Work.SSGRoute.minimalNormalKernelStep_of_genericKernelSolvable`).

So as soon as `Work.SSGRoute.theorem15_scholz` is `sorry`-free, the landmark's `sorry`
`Submission.minimalNormalKernelStep` may be replaced by `minimalNormalKernelStep_proved` below
(one line in `Submission/Shafarevich.lean`, a file of another lane).
-/

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

/-- **The flow form of Theorem 15 over `ℚ`**: a proper continuous solution of the split generic
embedding problem into `F(n)/F(n)^{(i,j)} ⋊ Gal(K/ℚ)`.  This is the hypothesis that
`Work.SSGRoute.genericKernelSolvable_of_flowSolutions` consumes; it is the projection of the
Scholz solution supplied by `Work.SSGRoute.theorem15_scholz` (a Scholz solution is a flow solution
together with the two local conditions (i), (ii), which the generic-kernel reduction does not
use). -/
theorem flowSolutions (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i) (n : ℕ) (hn : 1 ≤ n) :
    ∃ φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n i j,
      SSGRoute.IsFlowSolution p K n i j φ := by
  obtain ⟨φ, hφ⟩ := Work.SSGRoute.theorem15_scholz p K i j hj hji hμ n hn
  exact ⟨φ, hφ.1⟩

/-- **The generic-kernel hypothesis over `ℚ`** (Theorem 15 of Schmidt–Wingberg without its local
conditions (i), (ii)); the reduction `flowSolutions ⟹ GenericKernelSolvable` is
`Work.SSGRoute.genericKernelSolvable_of_flowSolutions`. -/
theorem genericKernelSolvable : Work.GenericKernelReduction.GenericKernelSolvable :=
  Work.SSGRoute.genericKernelSolvable_of_flowSolutions flowSolutions

/-- **The deep input of the landmark development**, `Submission.MinimalNormalKernelStep`: if
`A ◁ G` is a nontrivial minimal normal subgroup of a finite solvable group `G` and `G ⧸ A` is
realizable over `ℚ`, then so is `G`.  Proved here from `genericKernelSolvable` by the (sorry-free)
universe transport `Work.SSGRoute.minimalNormalKernelStep_of_genericKernelSolvable`. -/
theorem minimalNormalKernelStep_proved : Submission.MinimalNormalKernelStep :=
  Work.SSGRoute.minimalNormalKernelStep_of_genericKernelSolvable genericKernelSolvable

universe u

/-- **Shafarevich's theorem on solvable Galois groups**, with the landmark's deep input supplied
from `genericKernelSolvable` instead of the `sorry` of `Submission/Shafarevich.lean`: the statement
is that of `Submission.shafarevich_solvable_galois` (up to unfolding `Submission.RealizableOver`,
which is how that theorem is stated in `Submission.lean`), and the proof is
`Submission.realizable_of_solvable_of` (Ore's induction, on disk) applied to
`minimalNormalKernelStep_proved`. -/
theorem shafarevich_solvable_galois_of_genericKernel (G : Type u) [Group G] [Finite G]
    [Group.IsSolvable G] : Submission.RealizableOver ℚ G :=
  Submission.realizable_of_solvable_of minimalNormalKernelStep_proved G

end Work.SSGRoute.ZConstruction
