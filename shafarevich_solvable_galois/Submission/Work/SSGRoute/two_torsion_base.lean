import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.CohomologicalShrinking.nonempty_prop5Data_one_one
import Submission.Work.SSGRoute.gradedPiece_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Base case of the `p = 2` graded-step family (`σ = (1,1)`)

The group-theoretic heart of the `p = 2` correction (`Work.SSGRoute.two_torsion_lift_two`) is proved
by descending the refined filtration, and each step needs the **graded step** at `σ`:

  `∀ c ∈ ker(Q_{σ+1} → Q_σ), δ c = c⁻¹ → ∃ e ∈ Q_{σ+1}, c = (δ • e)⁻¹ * e`

(see `Submission/Work/SSGRoute/two_torsion_assembly.lean` for the descent itself).  This module
supplies the two ingredients of the base case `σ = (1,1)`: the injectivity of the canonical
identification `F(d)/F(d)^2 → E(2,G,d,1,1)` and the resulting graded step in the vocabulary of the
graded piece.  It deliberately has no dependency on `Work.SSGRoute.two_torsion_lift_two`, so that the
level-by-level developments can use it without importing that module.

## Main results

* `Work.SSGRoute.eLin_injective`
* `Work.SSGRoute.E_one_one_fixed_is_delta_difference`
-/

namespace Work.SSGRoute

open Work.CohomologicalShrinking

/-! ## The base case `σ = (1,1)` of the graded-step family

The group-theoretic heart of the `p = 2` correction is proved by descending the refined filtration,
and each step needs the **graded step** at `σ` (see `Submission/Work/SSGRoute/two_torsion_assembly.lean`
for the descent itself):

  `∀ c ∈ ker(Q_{σ+1} → Q_σ), δ c = c⁻¹ → ∃ e ∈ Q_{σ+1}, c = (δ • e)⁻¹ * e`.

The first (non-trivial) step is `σ = (1,1)`, where `Q_{(1,1)}` is trivial and the kernel is all of
`Q_{(2,1)} = F(d)/F(d)^2`; the graded piece is `E(2,G,d,1,1) ≅ F(d)/F(d)^2`.  For that piece the
`δ`-action permutes the free generators freely, and the construction of the witness is
`Work.SSGRoute.squareQuotient_fixed_is_delta_difference` in the model
`F(d)/F(d)^2 ≅ (Fin d × G → 𝔽₂)`.  Below we prove the two ingredients of the transfer from the model
to the honest group: the injectivity of the canonical identification
`F(d)/F(d)^2 ≅ E(2,G,d,1,1)` (its surjectivity is
`Work.CohomologicalShrinking.eLin_surjective`), and the resulting `σ = (1,1)` graded step. -/

/-- The canonical identification `F(d)/F(d)^2 → E(2,G,d,1,1)` of
`Work.CohomologicalShrinking.nonempty_prop5Data_one_one` is injective (it is the identity map
between two quotients of `F(d)` by the same subgroup `F(d)^2`, up to the propositional equality
`refinedTerm 2 _ 1 1 = ⊤` and `refinedTerm 2 _ 2 1 = pCentralSeries 2 _ 1`). -/
lemma eLin_injective (G : Type*) [Group G] (d : ℕ) :
    Function.Injective (Work.CohomologicalShrinking.eLin 2 G d) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨w, rfl⟩ : ∃ w, Additive.ofMul w = z := ⟨Additive.toMul z, ofMul_toMul z⟩
  obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective
    ((Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G d) 1).subgroupOf
      (Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G d) 0)) w
  have hzw : (Work.CohomologicalShrinking.eLin 2 G d) (Additive.ofMul w) = 0 := hz
  rw [← ht, Work.CohomologicalShrinking.eLin_mk] at hzw
  have h1 : (QuotientGroup.mk'
      ((Work.CohomologicalShrinking.refinedTerm 2 (Work.Shrinking.freeOperatorGroup G d)
        (Work.CohomologicalShrinking.tauSucc 1 1).1
        (Work.CohomologicalShrinking.tauSucc 1 1).2).subgroupOf
        (Work.CohomologicalShrinking.refinedTerm 2 (Work.Shrinking.freeOperatorGroup G d) 1 1))
      ((Work.CohomologicalShrinking.inclToRefined 2 (Work.Shrinking.freeOperatorGroup G d)) t))
      = (1 : Work.CohomologicalShrinking.refinedQuotient 2
          (Work.Shrinking.freeOperatorGroup G d) 1 1) := congrArg Additive.toMul hzw
  have hmem := (QuotientGroup.eq_one_iff
    ((Work.CohomologicalShrinking.inclToRefined 2 (Work.Shrinking.freeOperatorGroup G d)) t)).mp h1
  rw [Subgroup.mem_subgroupOf] at hmem
  have h2 : (t : Work.Shrinking.freeOperatorGroup G d) ∈
      Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G d) 1 := by
    rwa [Work.CohomologicalShrinking.tauSucc_of_le (le_refl 1),
      Work.CohomologicalShrinking.refinedTerm_one] at hmem
  have hgoal : w = 1 := by
    have h3 := (QuotientGroup.eq_one_iff t).mpr (Subgroup.mem_subgroupOf.mpr h2)
    rw [← ht]
    exact h3
  rw [hgoal]
  rfl

/-- **The `σ = (1,1)` graded step**, in the vocabulary of the graded piece: every `δ`-fixed element
of `E(2,G,d,1,1) = F(d)/F(d)^2` is a `δ`-difference there.  This is the transfer of
`Work.SSGRoute.squareQuotient_fixed_is_delta_difference` along the identification `eLin`. -/
lemma E_one_one_fixed_is_delta_difference (G : Type*) [Group G] [Fintype G] (d : ℕ)
    (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) :
    ∀ c : Work.CohomologicalShrinking.E 2 G d 1 1, δ • c = c →
      ∃ e : Work.CohomologicalShrinking.E 2 G d 1 1, c = δ • e - e := by
  intro c hc
  obtain ⟨v, hv⟩ := Work.CohomologicalShrinking.eLin_surjective 2 G d c
  have hvfix : δ • v = v := by
    apply eLin_injective G d
    show (Work.CohomologicalShrinking.eLin 2 G d) (δ • v)
      = (Work.CohomologicalShrinking.eLin 2 G d) v
    rw [Work.CohomologicalShrinking.eLin_smul, hv, hc]
  obtain ⟨w, hw⟩ := squareQuotient_fixed_is_delta_difference G d δ hδ hδ1 v hvfix
  refine ⟨Work.CohomologicalShrinking.eLin 2 G d w, ?_⟩
  have h1 : (Work.CohomologicalShrinking.eLin 2 G d) (δ • w - w)
      = δ • (Work.CohomologicalShrinking.eLin 2 G d w)
        - (Work.CohomologicalShrinking.eLin 2 G d) w := by
    rw [map_sub, Work.CohomologicalShrinking.eLin_smul]
  rw [← h1, ← hw, hv]


end Work.SSGRoute
