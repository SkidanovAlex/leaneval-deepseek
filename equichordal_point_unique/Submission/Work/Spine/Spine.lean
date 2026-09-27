import Mathlib
import Submission.Work.Spine.Basic

/-!
# The spine theorem for open surfaces (Johansson/Stallings) — statement and reductions

This module states **the one genuinely geometric input** of the subproject *and nothing else*:

> **Spine theorem.**  A connected, second countable, non-compact Riemann surface is homotopy
> equivalent to a space carrying a CW-complex structure on *all* of its points with no cells of
> dimension `≥ 2`.

In the words of the classical theorem (Johansson 1930s; Stallings), an open surface has the
homotopy type of a (locally finite) graph, equivalently of a wedge of circles.

## What the statement must *not* say

* The CW-complex structure must be on `Set.univ` of the witness `Y` and there must be a genuine
  homotopy equivalence `X ≃ₕ Y`.  An earlier line of work in this workspace stated the conclusion
  with a CW structure on an *arbitrary closed subspace* `C ⊆ Y`; that statement is satisfied
  vacuously by `C = ∅` and cannot feed
  `Commons.AlgebraicTopology.FundamentalGroup.freeGroup_of_oneDimCWComplex`.
* The *deformation retraction* form (`X` strongly deformation retracts onto a locally finite graph
  `S ⊆ X`) is **false** in general.  Refutation: take `U = ℂ ∖ ({0} ∪ {1/n : n ≥ 1})`, which is an
  open subset of `ℂ` and hence an open Riemann surface, and let `S ⊆ U` be a locally finite union
  of segments with a strong deformation retraction `ρ : U × I → U` onto `S`.  Put `p = ρ (i/K, 1)`
  for a point `i/K ∈ U`.  The loops `γ_n` around the punctures `1/n` (n large) are, for n large,
  contained in `B (i/K, 2/K)`; they are linearly independent in `H₁(U;ℤ)` (their winding vectors
  around the punctures are the standard basis vectors), and `ρ₁ = ρ(·,1)` is homotopic to the
  identity, hence induces the identity on `H₁(U;ℤ)`.  So all the classes `[γ_n]` lie in the image
  of `H₁ (S ∩ B (p,δ)) → H₁(U)` for a small ball, and *that* group is finitely generated (finitely
  many segments meet a small ball, by local finiteness of `S`): infinitely many independent elements
  in the image of a finitely generated group — contradiction.  (Compare the Hawaiian earring, whose
  fundamental group is *not* free.)  This is why the honest statement below is a homotopy
  equivalence and *not* a deformation retraction: the homotopy equivalence in the wild cases is
  genuinely not realised by any map into a locally finite graph that is homotopic to the identity.

## What is proved here

* `exists_cwComplex_univ_of_homotopyEquiv_*`: the transport lemmas that turn a spine statement
  phrased for a closed subspace `G ⊆ X` into the space-level statement.
* `exists_homotopyEquiv_oneDimCWComplex_of_subspace_spine`: the subspace form implies the statement
  above (via `Commons.Topology.CWComplex.exists_cwComplex_univ_of_isClosed_subspace`).
* `isFreeGroup_fundamentalGroup_of_noncompact_of_spine`,
  `simplyConnectedSpace_of_subsingleton_hom_toReal_of_spine`: the two target theorems of the
  subproject, derived from the spine theorem by the assembly layer.
-/

namespace Work.Spine

open scoped ContinuousMap Topology

universe u

/-- **A one-dimensional CW spine inside `X` gives the space-level spine statement.**  If `X`
contains a closed subspace `G` carrying a CW structure with no cells of dimension `≥ 2` such that
`X` is homotopy equivalent to `↥G`, then `X` is homotopy equivalent to a space carrying a CW
structure on *all* of itself with no cells of dimension `≥ 2` (namely the subtype `↥G`). -/
theorem exists_homotopyEquiv_oneDimCWComplex_of_subspace_spine
    {X : Type u} [TopologicalSpace X] [T2Space X] {G : Set X} (hGc : IsClosed G)
    (hC : @Topology.CWComplex X _ G)
    (hdim : ∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell X _ G hC n))
    (he : Nonempty (ContinuousMap.HomotopyEquiv X ↥G)) :
    ∃ (Y : Type u) (tY : TopologicalSpace Y),
      @T2Space Y tY ∧
        ∃ (hC' : @Topology.CWComplex Y tY Set.univ),
          (∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell Y tY Set.univ hC' n)) ∧
          Nonempty (@ContinuousMap.HomotopyEquiv X Y _ tY) := by
  obtain ⟨hC', hcell'⟩ :=
    Commons.Topology.CWComplex.exists_cwComplex_univ_of_isClosed_subspace hGc hC
  exact ⟨↥G, inferInstance, inferInstance, hC', fun n hn => hcell' n (hdim n hn), he⟩

/-- **The spine theorem (Johansson/Stallings), space-level form.**

A connected, second countable, non-compact Riemann surface is homotopy equivalent to a Hausdorff
space carrying a CW-complex structure on all of its points with no cells of dimension `≥ 2`.

This is the single geometric input of the subproject `Work.Spine`. -/
theorem exists_homotopyEquiv_oneDimCWComplex_of_noncompact
    {X : Type u} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] (hX : ¬ CompactSpace X) :
    ∃ (Y : Type u) (tY : TopologicalSpace Y),
      @T2Space Y tY ∧
        ∃ (hC : @Topology.CWComplex Y tY Set.univ),
          (∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell Y tY Set.univ hC n)) ∧
          Nonempty (@ContinuousMap.HomotopyEquiv X Y _ tY) := by
  sorry

/-- **Freeness of `π₁` of a connected non-compact Riemann surface** — Johansson's theorem, derived
from the spine theorem. -/
theorem isFreeGroup_fundamentalGroup_of_noncompact_of_spine
    {X : Type u} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (x : X) :
    IsFreeGroup (FundamentalGroup X x) := by
  obtain ⟨Y, tY, hT2, hC, hdim, he⟩ :=
    exists_homotopyEquiv_oneDimCWComplex_of_noncompact (X := X) hX
  exact @isFreeGroup_fundamentalGroup_of_oneDimCWComplex X Y _ tY inferInstance hT2
    inferInstance x hC hdim he

/-- **Hubbard 1.1.2, topological part, derived from the spine theorem.** -/
theorem simplyConnectedSpace_of_subsingleton_hom_toReal_of_spine
    {X : Type u} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (x : X) [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)] :
    SimplyConnectedSpace X := by
  haveI : IsFreeGroup (FundamentalGroup X x) :=
    isFreeGroup_fundamentalGroup_of_noncompact_of_spine (X := X) hX x
  haveI : Subsingleton (FundamentalGroup X x) := subsingleton_fundamentalGroup_of_isFreeGroup x
  haveI : PathConnectedSpace X := pathConnectedSpace_of_chartedSpace_complex
  exact simplyConnectedSpace_of_subsingleton_fundamentalGroup x

end Work.Spine
