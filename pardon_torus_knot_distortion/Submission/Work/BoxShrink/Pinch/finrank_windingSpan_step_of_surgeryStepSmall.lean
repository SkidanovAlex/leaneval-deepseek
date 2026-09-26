import Mathlib
import Submission.Work.BoxShrink.Bubble.HalfDefs
import Submission.Work.SurgeryInvariance.Span.union_eq_sup

/-!
# The dimension bound of a single surgery (`step` field of `PinchRegions`)

A `Work.BoxShrink.Bubble.SurgeryStepSmall` step changes the winding span by adjoining or removing a
piece `Z` of winding span `≠ ⊤` (i.e. of dimension at most one), so the dimension of the invariant
changes by at most one — Pardon's *"doing any of the allowed surgeries can change this value by at
most `1`"*, and exactly the `step` field of `Work.BoxShrink.Pinch.PinchRegions` /
`Work.BoxShrink.Pinch.SweepLoopsSmall`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

theorem finrank_windingSpan_step_of_surgeryStepSmall {P : Work.CoreTopology.ParamTorus}
    {A A' : Set R3}
    (h : Work.BoxShrink.Bubble.SurgeryStepSmall P A A') :
    (Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P A') ≤
        Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P A) + 1) ∧
      (Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P A) ≤
        Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P A') + 1) := by
  classical
  obtain ⟨Z, hZtop, hAo, hA'o, hZo, hcase | hcase⟩ := h
  · -- `A = A' ∪ Z`
    obtain ⟨rfl, hd⟩ := hcase
    have hsup : Work.SurgeryInvariance.WindingSpan P (A' ∪ Z) =
        Work.SurgeryInvariance.WindingSpan P A' ⊔ Work.SurgeryInvariance.WindingSpan P Z :=
      Work.SurgeryInvariance.Span.union_eq_sup (P := P) hA'o hZo hd
    -- `Z` spans at most one dimension
    have hZlt : Work.SurgeryInvariance.WindingSpan P Z < ⊤ := lt_top_iff_ne_top.mpr hZtop
    have hZfin : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P Z) ≤ 1 := by
      have h1 : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P Z) <
          Module.finrank ℚ ↥(⊤ : Submodule ℚ (ℚ × ℚ)) :=
        Submodule.finrank_lt_finrank_of_lt hZlt
      rw [finrank_top, Module.finrank_prod, Module.finrank_self] at h1
      norm_num at h1
      omega
    -- sup of the two, and the two inequalities
    have hsupfin : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (A' ∪ Z)) ≤
        Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P A') +
          Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P Z) := by
      rw [hsup]
      have h2 := Submodule.finrank_sup_add_finrank_inf_eq
        (Work.SurgeryInvariance.WindingSpan P A') (Work.SurgeryInvariance.WindingSpan P Z)
      have h3 : 0 ≤ Module.finrank ℚ
          ↥(Work.SurgeryInvariance.WindingSpan P A' ⊓ Work.SurgeryInvariance.WindingSpan P Z) :=
        Nat.zero_le _
      omega
    constructor
    · exact le_trans (Submodule.finrank_mono
        (Work.SurgeryInvariance.WindingSpan_mono P Set.subset_union_left)) (Nat.le_succ _)
    · have h2 := hZfin
      omega
  · -- `A' = A ∪ Z`
    obtain ⟨rfl, hd⟩ := hcase
    have hsup : Work.SurgeryInvariance.WindingSpan P (A ∪ Z) =
        Work.SurgeryInvariance.WindingSpan P A ⊔ Work.SurgeryInvariance.WindingSpan P Z :=
      Work.SurgeryInvariance.Span.union_eq_sup (P := P) hAo hZo hd
    have hZlt : Work.SurgeryInvariance.WindingSpan P Z < ⊤ := lt_top_iff_ne_top.mpr hZtop
    have hZfin : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P Z) ≤ 1 := by
      have h1 : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P Z) <
          Module.finrank ℚ ↥(⊤ : Submodule ℚ (ℚ × ℚ)) :=
        Submodule.finrank_lt_finrank_of_lt hZlt
      rw [finrank_top, Module.finrank_prod, Module.finrank_self] at h1
      norm_num at h1
      omega
    have hsupfin : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (A ∪ Z)) ≤
        Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P A) +
          Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P Z) := by
      rw [hsup]
      have h2 := Submodule.finrank_sup_add_finrank_inf_eq
        (Work.SurgeryInvariance.WindingSpan P A) (Work.SurgeryInvariance.WindingSpan P Z)
      have h3 : 0 ≤ Module.finrank ℚ
          ↥(Work.SurgeryInvariance.WindingSpan P A ⊓ Work.SurgeryInvariance.WindingSpan P Z) :=
        Nat.zero_le _
      omega
    constructor
    · have h2 := hZfin
      omega
    · exact le_trans (Submodule.finrank_mono
        (Work.SurgeryInvariance.WindingSpan_mono P Set.subset_union_left)) (Nat.le_succ _)

end

end Work.BoxShrink.Pinch
