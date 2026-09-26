import Mathlib
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.SurgeryInvariance.Core
import Submission.Work.PinchLemma3.Defs
import Submission.Work.PinchLemma3.ClosedDiscA.finrank_windingSpan_union_le_of_pieces_of_components

/-!
# The one-class bound for `Ω⁺ ∪ D°` when `Ω⁺ ∩ D°` splits into three pieces over an open
two-piece splitting of `Ω⁺`

`Work.PinchLemma3.ClosedDiscA.finrank_upperRegion_union_discInterior_le_one_of_three_pieces_split`.

Session 10 established (`Work.PinchLemma3.ClosedDiscA.exists_ne_zero_inf_span_le_of_intersection_three_pieces`)
that when the slice's complement `D° ∩ Ω` in the disc's interior splits into **three** path connected
pieces distributed `2 + 1` over the two *sides* of the cutting plane, the winding span of the box
region still misses a nonzero class.  Its additive-rank companion
(`Work.PinchLemma3.ClosedDiscA.finrank_windingSpan_union_le_of_pieces_of_components`) bounds the
dimension of the winding span by `#pieces - #components = 3 - 1 = 2`; here the two pieces
`K₁, K₂` on one side are *joined inside that side*, and this is what buys the extra dimension.

The precise configuration proved here: the upper half-region splits as `Ω⁺ = U₁ ∪ U₂` into two
disjoint carrier-open path connected pieces, and `D° ∩ Ω⁺ = K₁ ∪ K₂ ∪ K₃` with `K₁ ∪ K₂ ⊆ U₁`,
`K₃ ⊆ U₂`.  Then

  `finrank W(Ω⁺ ∪ D°) ≤ 1`.

The proof is the `2 + 1` criterion `exists_ne_zero_inf_span_le_of_intersection_three_pieces` applied
with `A := D°` (an embedded disc, hence inessential and path connected), `B := Ω⁺` (inessential by
`h0`, and split into `B₁ := U₁`, `B₂ := U₂`), together with the linear algebra
`finrank_le_one_of_inf_span_le_bot`: a subspace of `ℚ²` meeting a nonzero line only in `0` has
dimension at most one.
-/

namespace Work.PinchLemma3.ClosedDiscA

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

set_option linter.unusedVariables false

/-- The interior of an embedded disc of the carrier is path connected: it is the image of the open
unit disc under the embedding.  (Local restatement of the sibling lemma of the same shape, so that
this module depends only on `SurgeryInvariance.Core`.) -/
theorem isPathConnected_discInterior_of_discRegion {P : Work.CoreTopology.ParamTorus}
    (D : Work.SurgeryInvariance.DiscRegion P) : IsPathConnected D.interior := by
  have hpc : IsPathConnected {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1} := by
    have h := IsPathConnected.preimage_coe (X := ℂ) (U := Metric.closedBall (0 : ℂ) 1)
      (W := Metric.ball (0 : ℂ) 1) (Metric.isPathConnected_ball (by norm_num))
      Metric.ball_subset_closedBall
    simpa [Set.preimage, Metric.mem_ball] using h
  have himg : IsPathConnected
      (D.e '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1}) :=
    hpc.image D.e.continuous
  rw [Work.SurgeryInvariance.DiscRegion.interior_def]
  exact himg

theorem finrank_upperRegion_union_discInterior_le_one_of_three_pieces_split
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (D : Work.SurgeryInvariance.DiscRegion P)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    {K₁ K₂ K₃ : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hK₁op : Work.SurgeryInvariance.IsOpenInCarrier P K₁)
    (hK₂op : Work.SurgeryInvariance.IsOpenInCarrier P K₂)
    (hK₃op : Work.SurgeryInvariance.IsOpenInCarrier P K₃)
    (hK₁pc : IsPathConnected K₁) (hK₂pc : IsPathConnected K₂) (hK₃pc : IsPathConnected K₃)
    (hdisj₁₂ : Disjoint K₁ K₂) (hdisj₁₃ : Disjoint K₁ K₃) (hdisj₂₃ : Disjoint K₂ K₃)
    (hinter : D.interior ∩ Work.BoxShrink.Core.upperRegion P s c σ u = K₁ ∪ K₂ ∪ K₃)
    {U₁ U₂ : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hU₁op : Work.SurgeryInvariance.IsOpenInCarrier P U₁)
    (hU₂op : Work.SurgeryInvariance.IsOpenInCarrier P U₂)
    (hU₁pc : IsPathConnected U₁) (hU₂pc : IsPathConnected U₂)
    (hUdisj : Disjoint U₁ U₂)
    (hcov : Work.BoxShrink.Core.upperRegion P s c σ u ⊆ U₁ ∪ U₂)
    (hUsub : U₁ ∪ U₂ ⊆ Work.BoxShrink.Core.upperRegion P s c σ u)
    (hK₁U₁ : K₁ ⊆ U₁) (hK₂U₁ : K₂ ⊆ U₁) (hK₃U₂ : K₃ ⊆ U₂) :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪ D.interior)) ≤ 1 := by
  -- The upper region lies on the surface, and its winding span vanishes by `h0`.
  have hUc : Work.BoxShrink.Core.upperRegion P s c σ u ⊆ P.carrier :=
    fun x hx => (Work.BoxShrink.Core.upperRegion_subset P s c σ u hx).1
  have hVU : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u) = ⊥ :=
    le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P
      (Set.subset_union_left : Work.BoxShrink.Core.upperRegion P s c σ u ⊆
        Work.PinchLemma3.halfRegions P s c σ u)) (le_of_eq h0))
  -- The disc's interior carries no winding.
  have hVd : Work.SurgeryInvariance.WindingSpan P D.interior = ⊥ :=
    D.windingSpan_interior_eq_bot
  -- The two open pieces cover the upper region.
  have hsplit : Work.BoxShrink.Core.upperRegion P s c σ u = U₁ ∪ U₂ :=
    Set.Subset.antisymm hcov hUsub
  have hU₁c : U₁ ⊆ P.carrier := by
    intro x hx
    exact hUc (by rw [hsplit]; exact Or.inl hx)
  have hU₂c : U₂ ⊆ P.carrier := by
    intro x hx
    exact hUc (by rw [hsplit]; exact Or.inr hx)
  -- The three pieces lie in the disc's interior, hence on the surface.
  have hK₁c : K₁ ⊆ P.carrier := by
    intro x hx
    have hx' : x ∈ D.interior ∩ Work.BoxShrink.Core.upperRegion P s c σ u := by
      rw [hinter]; exact Or.inl (Or.inl hx)
    exact D.interior_subset_surface hx'.1
  have hK₂c : K₂ ⊆ P.carrier := by
    intro x hx
    have hx' : x ∈ D.interior ∩ Work.BoxShrink.Core.upperRegion P s c σ u := by
      rw [hinter]; exact Or.inl (Or.inr hx)
    exact D.interior_subset_surface hx'.1
  have hK₃c : K₃ ⊆ P.carrier := by
    intro x hx
    have hx' : x ∈ D.interior ∩ Work.BoxShrink.Core.upperRegion P s c σ u := by
      rw [hinter]; exact Or.inr hx
    exact D.interior_subset_surface hx'.1
  -- The `2 + 1` criterion, with `A = D°`, `B = Ω⁺`, `B₁ = U₁`, `B₂ = U₂`.
  obtain ⟨v, hv0, hvle⟩ :=
    exists_ne_zero_inf_span_le_of_intersection_three_pieces
      (P := P) (A := D.interior) (B := Work.BoxShrink.Core.upperRegion P s c σ u)
      (B₁ := U₁) (B₂ := U₂) (K₁ := K₁) (K₂ := K₂) (K₃ := K₃)
      D.interior_subset_surface hUc D.open_interior'
      (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
      (isPathConnected_discInterior_of_discRegion D) hVd hVU
      hU₁c hU₂c hU₁op hU₂op hsplit hUdisj
      hK₁c hK₂c hK₃c hK₁op hK₂op hK₃op hK₁pc hK₂pc hK₃pc
      hdisj₁₂ hdisj₁₃ hdisj₂₃ hinter hK₁U₁ hK₂U₁ hK₃U₂
  rw [hVd, hVU, bot_sup_eq] at hvle
  -- `W(Ω⁺ ∪ D°) = W(D° ∪ Ω⁺)` misses the nonzero line `ℚ∙v`, so it has dimension at most one.
  rw [Set.union_comm]
  exact finrank_le_one_of_inf_span_le_bot hv0 hvle

end

end Work.PinchLemma3.ClosedDiscA
