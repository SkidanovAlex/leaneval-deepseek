import Mathlib
import Submission.Work.BoxShrink.Bubble.Basic

namespace Work.BoxShrink.Bubble.Obstruction

open LeanEval.KnotTheory.PardonDistortion
open Set

/-- If two sets have the same preimage in the carrier of `P`, then they have the same trace
there. -/
theorem carrier_inter_eq_of_preimage_eq {P : Work.CoreTopology.ParamTorus} {X Y : Set R3}
    (h : Subtype.val ⁻¹' X = (Subtype.val ⁻¹' Y : Set P.carrier)) :
    P.carrier ∩ X = P.carrier ∩ Y := by
  ext y
  constructor
  · rintro ⟨hy, hyX⟩
    refine ⟨hy, ?_⟩
    have h' : (⟨y, hy⟩ : P.carrier) ∈ Subtype.val ⁻¹' X := hyX
    rw [h] at h'
    exact h'
  · rintro ⟨hy, hyY⟩
    refine ⟨hy, ?_⟩
    have h' : (⟨y, hy⟩ : P.carrier) ∈ Subtype.val ⁻¹' Y := hyY
    rw [← h] at h'
    exact h'

theorem surgeryStepZero_eq_self_or_empty
    {P : Work.CoreTopology.ParamTorus}
    {A A' Z : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hAc : A ⊆ P.carrier)
    (hA' : Work.SurgeryInvariance.IsOpenInCarrier P A')
    (hZ : Work.SurgeryInvariance.IsOpenInCarrier P Z)
    (hcover : A = A' ∪ Z) (hdisj : Disjoint A' Z) (hpre : IsPreconnected A) :
    A' = A ∨ A' = ∅ := by
  have hA'sub : A' ⊆ A := by rw [hcover]; exact Set.subset_union_left
  have hZsub : Z ⊆ A := by rw [hcover]; exact Set.subset_union_right
  have hA'c : A' ⊆ P.carrier := hA'sub.trans hAc
  have hZc : Z ⊆ P.carrier := hZsub.trans hAc
  -- open sets in `ℝ³` cutting out `A'` and `Z` on the carrier
  obtain ⟨U, hUopen, hUeq⟩ :=
    isOpen_induced_iff.mp (show IsOpen (Subtype.val ⁻¹' A' : Set P.carrier) from hA')
  obtain ⟨V, hVopen, hVeq⟩ :=
    isOpen_induced_iff.mp (show IsOpen (Subtype.val ⁻¹' Z : Set P.carrier) from hZ)
  have hUc : P.carrier ∩ U = A' := by
    rw [carrier_inter_eq_of_preimage_eq hUeq, Set.inter_eq_right.mpr hA'c]
  have hVc : P.carrier ∩ V = Z := by
    rw [carrier_inter_eq_of_preimage_eq hVeq, Set.inter_eq_right.mpr hZc]
  have hAU : A ∩ U = A' := by
    calc A ∩ U = (A ∩ P.carrier) ∩ U := by rw [Set.inter_eq_left.mpr hAc]
      _ = A ∩ (P.carrier ∩ U) := by rw [Set.inter_assoc]
      _ = A ∩ A' := by rw [hUc]
      _ = A' := by rw [Set.inter_eq_right.mpr hA'sub]
  have hAV : A ∩ V = Z := by
    calc A ∩ V = (A ∩ P.carrier) ∩ V := by rw [Set.inter_eq_left.mpr hAc]
      _ = A ∩ (P.carrier ∩ V) := by rw [Set.inter_assoc]
      _ = A ∩ Z := by rw [hVc]
      _ = Z := by rw [Set.inter_eq_right.mpr hZsub]
  have hsub : A ⊆ U ∪ V := by
    intro x hx
    rw [hcover] at hx
    rcases hx with hx | hx
    · left
      have hx' : x ∈ P.carrier ∩ U := by rw [hUc]; exact hx
      exact hx'.2
    · right
      have hx' : x ∈ P.carrier ∩ V := by rw [hVc]; exact hx
      exact hx'.2
  have hempty : A ∩ (U ∩ V) = ∅ := by
    have h1 : A ∩ (U ∩ V) = (A ∩ U) ∩ (A ∩ V) := by
      ext x; simp only [Set.mem_inter_iff]; tauto
    rw [h1, hAU, hAV, Set.disjoint_iff_inter_eq_empty.mp hdisj]
  have hcases : A ∩ U = ∅ ∨ A ∩ V = ∅ := by
    by_contra h
    rw [not_or] at h
    exact (hpre U V hUopen hVopen hsub (Set.nonempty_iff_ne_empty.mpr h.1)
      (Set.nonempty_iff_ne_empty.mpr h.2)).ne_empty hempty
  rcases hcases with hU0 | hV0
  · right
    rw [← hAU]
    exact hU0
  · left
    rw [hcover, ← hAV, hV0, Set.union_empty]

end Work.BoxShrink.Bubble.Obstruction
