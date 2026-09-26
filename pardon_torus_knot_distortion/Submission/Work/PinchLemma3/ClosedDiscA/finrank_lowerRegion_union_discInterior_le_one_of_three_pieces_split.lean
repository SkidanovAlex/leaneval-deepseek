import Mathlib
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.SurgeryInvariance.Core
import Submission.Work.PinchLemma3.Defs
import Submission.Work.PinchLemma3.ClosedDiscA.finrank_windingSpan_union_le_of_pieces_of_components
import Submission.Work.PinchLemma3.ClosedDiscA.finrank_upperRegion_union_discInterior_le_one_of_three_pieces_split

/-!
# The one-class bound for `Ω⁻ ∪ D°` when `Ω⁻ ∩ D°` splits into three pieces over an open
two-piece splitting of `Ω⁻`

`Work.PinchLemma3.ClosedDiscA.finrank_lowerRegion_union_discInterior_le_one_of_three_pieces_split`.

This is the lower-half companion of
`Work.PinchLemma3.ClosedDiscA.finrank_upperRegion_union_discInterior_le_one_of_three_pieces_split`.
The argument is identical, with `Ω⁻` (the *lower* half-region) in place of `Ω⁺`: the two-piece
criterion `exists_ne_zero_inf_span_le_of_intersection_three_pieces` with `A := D°`, `B := Ω⁻`,
`B₁ := U₁`, `B₂ := U₂` produces a nonzero class `v` whose multiples lying in `W(Ω⁻ ∪ D°)` already
lie in `W(D°) ⊔ W(Ω⁻) = ⊥`; the linear algebra `finrank_le_one_of_inf_span_le_bot` then bounds
the dimension of `W(Ω⁻ ∪ D°)` by one.

The only inputs that change relative to the upper case are `Ω⁻ ⊆ halfRegions`
(`Set.subset_union_right`, since `halfRegions = Ω⁺ ∪ Ω⁻`) and the lower-half openness
`Work.BoxShrink.Core.isOpenInCarrier_lowerRegion`.
-/

namespace Work.PinchLemma3.ClosedDiscA

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

set_option linter.unusedVariables false

theorem finrank_lowerRegion_union_discInterior_le_one_of_three_pieces_split
    (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : LeanEval.KnotTheory.PardonDistortion.R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (D : Work.SurgeryInvariance.DiscRegion P)
    (h0 : Work.SurgeryInvariance.WindingSpan P (Work.PinchLemma3.halfRegions P s c σ u) = ⊥)
    {K₁ K₂ K₃ : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hK₁op : Work.SurgeryInvariance.IsOpenInCarrier P K₁)
    (hK₂op : Work.SurgeryInvariance.IsOpenInCarrier P K₂)
    (hK₃op : Work.SurgeryInvariance.IsOpenInCarrier P K₃)
    (hK₁pc : IsPathConnected K₁) (hK₂pc : IsPathConnected K₂) (hK₃pc : IsPathConnected K₃)
    (hdisj₁₂ : Disjoint K₁ K₂) (hdisj₁₃ : Disjoint K₁ K₃) (hdisj₂₃ : Disjoint K₂ K₃)
    (hinter : D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u = K₁ ∪ K₂ ∪ K₃)
    {U₁ U₂ : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hU₁op : Work.SurgeryInvariance.IsOpenInCarrier P U₁)
    (hU₂op : Work.SurgeryInvariance.IsOpenInCarrier P U₂)
    (hU₁pc : IsPathConnected U₁) (hU₂pc : IsPathConnected U₂)
    (hUdisj : Disjoint U₁ U₂)
    (hcov : Work.BoxShrink.Core.lowerRegion P s c σ u ⊆ U₁ ∪ U₂)
    (hUsub : U₁ ∪ U₂ ⊆ Work.BoxShrink.Core.lowerRegion P s c σ u)
    (hK₁U₁ : K₁ ⊆ U₁) (hK₂U₁ : K₂ ⊆ U₁) (hK₃U₂ : K₃ ⊆ U₂) :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.lowerRegion P s c σ u ∪ D.interior)) ≤ 1 := by
  -- The lower region lies on the surface, and its winding span vanishes by `h0`.
  have hUc : Work.BoxShrink.Core.lowerRegion P s c σ u ⊆ P.carrier :=
    fun x hx => (Work.BoxShrink.Core.lowerRegion_subset P s c σ u hx).1
  have hVU : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.lowerRegion P s c σ u) = ⊥ :=
    le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P
      (Set.subset_union_right : Work.BoxShrink.Core.lowerRegion P s c σ u ⊆
        Work.PinchLemma3.halfRegions P s c σ u)) (le_of_eq h0))
  -- The disc's interior carries no winding.
  have hVd : Work.SurgeryInvariance.WindingSpan P D.interior = ⊥ :=
    D.windingSpan_interior_eq_bot
  -- The two open pieces cover the lower region.
  have hsplit : Work.BoxShrink.Core.lowerRegion P s c σ u = U₁ ∪ U₂ :=
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
    have hx' : x ∈ D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u := by
      rw [hinter]; exact Or.inl (Or.inl hx)
    exact D.interior_subset_surface hx'.1
  have hK₂c : K₂ ⊆ P.carrier := by
    intro x hx
    have hx' : x ∈ D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u := by
      rw [hinter]; exact Or.inl (Or.inr hx)
    exact D.interior_subset_surface hx'.1
  have hK₃c : K₃ ⊆ P.carrier := by
    intro x hx
    have hx' : x ∈ D.interior ∩ Work.BoxShrink.Core.lowerRegion P s c σ u := by
      rw [hinter]; exact Or.inr hx
    exact D.interior_subset_surface hx'.1
  -- The `2 + 1` criterion, with `A = D°`, `B = Ω⁻`, `B₁ = U₁`, `B₂ = U₂`.
  obtain ⟨v, hv0, hvle⟩ :=
    exists_ne_zero_inf_span_le_of_intersection_three_pieces
      (P := P) (A := D.interior) (B := Work.BoxShrink.Core.lowerRegion P s c σ u)
      (B₁ := U₁) (B₂ := U₂) (K₁ := K₁) (K₂ := K₂) (K₃ := K₃)
      D.interior_subset_surface hUc D.open_interior'
      (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u)
      (isPathConnected_discInterior_of_discRegion D) hVd hVU
      hU₁c hU₂c hU₁op hU₂op hsplit hUdisj
      hK₁c hK₂c hK₃c hK₁op hK₂op hK₃op hK₁pc hK₂pc hK₃pc
      hdisj₁₂ hdisj₁₃ hdisj₂₃ hinter hK₁U₁ hK₂U₁ hK₃U₂
  rw [hVd, hVU, bot_sup_eq] at hvle
  -- `W(Ω⁻ ∪ D°) = W(D° ∪ Ω⁻)` misses the nonzero line `ℚ∙v`, so it has dimension at most one.
  rw [Set.union_comm]
  exact finrank_le_one_of_inf_span_le_bot hv0 hvle

end

end Work.PinchLemma3.ClosedDiscA
