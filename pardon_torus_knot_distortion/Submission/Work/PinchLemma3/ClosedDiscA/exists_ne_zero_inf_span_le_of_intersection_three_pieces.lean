import Mathlib
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.PinchLemma3.ClosedDiscA.exists_ne_zero_inf_span_le_of_intersection_pair_general
import Submission.Work.PinchLemma3.ClosedDiscA.potential_helpers
import Submission.Work.PinchLemma3.ClosedDiscA.exists_alternating_partition

-- the hypotheses `hApc`, `hBop`, `hK₃c`, `hK₃op`, `hdisj₁₃`, `hdisj₂₃` of the statement are
-- part of the requested interface but are not needed by the argument below.
set_option linter.unusedVariables false

/-!
# A line outside the winding span of the union of two inessential regions, three-piece overlap

`Work.PinchLemma3.ClosedDiscA.exists_ne_zero_inf_span_le_of_intersection_three_pieces` is the
`k = 2` case of the rank bound of Pardon's pinch: `A` is a path connected inessential region,
`B = B₁ ∪ B₂` is the disjoint union of two inessential regions, and the overlap
`A ∩ B = K₁ ∪ K₂ ∪ K₃` is a disjoint union of three path connected pieces, of which `K₁` and `K₂`
lie in `B₁` while `K₃` lies in `B₂`.  Then `WindingSpan P (A ∪ B) ≠ ⊤`, i.e. there is a nonzero
`v` whose line meets the winding span of `A ∪ B` only inside `WindingSpan P A ⊔ WindingSpan P B`.

The argument splits the configuration at the region `B₂`:

* `B₂` meets `A` exactly in the single path connected piece `K₃` (`A ∩ B₂ = K₃`), so the
  two-piece criterion `windingSpan_union_le_sup_of_isPathConnected_inter` gives
  `WindingSpan P (A ∪ B₂) ≤ WindingSpan P A ⊔ WindingSpan P B₂ = ⊥`;
* the pair `(A ∪ B₂, B₁)` then has overlap `(A ∪ B₂) ∩ B₁ = K₁ ∪ K₂` (the `B₂`-part of the
  overlap is killed by disjointness of `B₁` and `B₂`), so the delegated two-piece rank bound
  `exists_ne_zero_inf_span_le_of_intersection_pair_general` applies and exhibits the required
  line.

Both regions `A ∪ B₂` and `B₁` have vanishing winding span, so the right hand side of the rank
bound is `⊥` and the conclusion is the claimed containment.
-/

namespace Work.PinchLemma3.ClosedDiscA

open LeanEval.KnotTheory.PardonDistortion Set

theorem exists_ne_zero_inf_span_le_of_intersection_three_pieces
    {P : Work.CoreTopology.ParamTorus}
    {A B B₁ B₂ : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hAc : A ⊆ P.carrier) (hBc : B ⊆ P.carrier)
    (hAop : Work.SurgeryInvariance.IsOpenInCarrier P A)
    (hBop : Work.SurgeryInvariance.IsOpenInCarrier P B)
    (hApc : IsPathConnected A)
    (hVA : Work.SurgeryInvariance.WindingSpan P A = ⊥)
    (hVB : Work.SurgeryInvariance.WindingSpan P B = ⊥)
    (hB₁co : B₁ ⊆ P.carrier) (hB₂co : B₂ ⊆ P.carrier)
    (hB₁op : Work.SurgeryInvariance.IsOpenInCarrier P B₁)
    (hB₂op : Work.SurgeryInvariance.IsOpenInCarrier P B₂)
    (hBsplit : B = B₁ ∪ B₂) (hBdisj : Disjoint B₁ B₂)
    {K₁ K₂ K₃ : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hK₁c : K₁ ⊆ P.carrier) (hK₂c : K₂ ⊆ P.carrier) (hK₃c : K₃ ⊆ P.carrier)
    (hK₁op : Work.SurgeryInvariance.IsOpenInCarrier P K₁)
    (hK₂op : Work.SurgeryInvariance.IsOpenInCarrier P K₂)
    (hK₃op : Work.SurgeryInvariance.IsOpenInCarrier P K₃)
    (hK₁pc : IsPathConnected K₁) (hK₂pc : IsPathConnected K₂) (hK₃pc : IsPathConnected K₃)
    (hdisj₁₂ : Disjoint K₁ K₂) (hdisj₁₃ : Disjoint K₁ K₃) (hdisj₂₃ : Disjoint K₂ K₃)
    (hinter : A ∩ B = K₁ ∪ K₂ ∪ K₃)
    (hK₁B₁ : K₁ ⊆ B₁) (hK₂B₁ : K₂ ⊆ B₁) (hK₃B₂ : K₃ ⊆ B₂) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      Work.SurgeryInvariance.WindingSpan P (A ∪ B) ⊓ Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤
        Work.SurgeryInvariance.WindingSpan P A ⊔ Work.SurgeryInvariance.WindingSpan P B := by
  classical
  -- `B₁` and `B₂` are contained in `B`
  have hB₁B : B₁ ⊆ B := by rw [hBsplit]; exact Set.subset_union_left
  have hB₂B : B₂ ⊆ B := by rw [hBsplit]; exact Set.subset_union_right
  -- the three pieces lie in `A`
  have hK₁A : K₁ ⊆ A := by
    intro x hx
    have : x ∈ A ∩ B := by rw [hinter]; exact Or.inl (Or.inl hx)
    exact this.1
  have hK₂A : K₂ ⊆ A := by
    intro x hx
    have : x ∈ A ∩ B := by rw [hinter]; exact Or.inl (Or.inr hx)
    exact this.1
  have hK₃A : K₃ ⊆ A := by
    intro x hx
    have : x ∈ A ∩ B := by rw [hinter]; exact Or.inr hx
    exact this.1
  -- the winding spans of the two halves vanish
  have hVB₁ : Work.SurgeryInvariance.WindingSpan P B₁ = ⊥ :=
    le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P hB₁B) (le_of_eq hVB))
  have hVB₂ : Work.SurgeryInvariance.WindingSpan P B₂ = ⊥ :=
    le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P hB₂B) (le_of_eq hVB))
  -- the overlap of `A` with each half: `A ∩ B₁ = K₁ ∪ K₂` and `A ∩ B₂ = K₃`
  have hInter₁ : A ∩ B₁ = K₁ ∪ K₂ := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hxA, hxB₁⟩
      have hxAB : x ∈ A ∩ B := ⟨hxA, hB₁B hxB₁⟩
      rw [hinter] at hxAB
      rcases hxAB with (h | h) | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso; exact Set.disjoint_left.mp hBdisj hxB₁ (hK₃B₂ h)
    · rintro x (h | h)
      · exact ⟨hK₁A h, hK₁B₁ h⟩
      · exact ⟨hK₂A h, hK₂B₁ h⟩
  have hInter₂ : A ∩ B₂ = K₃ := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hxA, hxB₂⟩
      have hxAB : x ∈ A ∩ B := ⟨hxA, hB₂B hxB₂⟩
      rw [hinter] at hxAB
      rcases hxAB with (h | h) | h
      · exfalso; exact Set.disjoint_left.mp hBdisj (hK₁B₁ h) hxB₂
      · exfalso; exact Set.disjoint_left.mp hBdisj (hK₂B₁ h) hxB₂
      · exact h
    · intro x hx
      exact ⟨hK₃A hx, hK₃B₂ hx⟩
  -- `B₂` adds no winding: `WindingSpan P (A ∪ B₂) = ⊥`
  have hWA₂ : Work.SurgeryInvariance.WindingSpan P (A ∪ B₂) = ⊥ := by
    have h := windingSpan_union_le_sup_of_isPathConnected_inter
      (P := P) (A := A) (B := B₂) hAc hB₂co hAop hB₂op (hInter₂.symm ▸ hK₃pc)
    rw [hVA, hVB₂, sup_bot_eq] at h
    exact le_bot_iff.mp h
  -- the overlap of `A ∪ B₂` with `B₁` is `K₁ ∪ K₂`
  have hInter' : (A ∪ B₂) ∩ B₁ = K₁ ∪ K₂ := by
    rw [Set.union_inter_distrib_right, hInter₁]
    have h0 : B₂ ∩ B₁ = ∅ := by
      rw [Set.inter_comm]; exact Set.disjoint_iff_inter_eq_empty.mp hBdisj
    rw [h0, Set.union_empty]
  -- the two-piece rank bound for the pair `(A ∪ B₂, B₁)`
  obtain ⟨v, hvne, hvkey⟩ :=
    exists_ne_zero_inf_span_le_of_intersection_pair_general
      (P := P) (A := A ∪ B₂) (B := B₁)
      (fun x hx => hx.elim (fun h => hAc h) (fun h => hB₂co h)) hB₁co
      (Work.SurgeryInvariance.isOpenInCarrier_union P hAop hB₂op) hB₁op
      hWA₂ hVB₁ hK₁c hK₂c hK₁op hK₂op hK₁pc hK₂pc hdisj₁₂ hInter'
  refine ⟨v, hvne, ?_⟩
  have hset : (A ∪ B₂) ∪ B₁ = A ∪ B := by
    rw [Set.union_assoc, Set.union_comm B₂ B₁, ← hBsplit]
  calc Work.SurgeryInvariance.WindingSpan P (A ∪ B) ⊓ ℚ ∙ v
      = Work.SurgeryInvariance.WindingSpan P ((A ∪ B₂) ∪ B₁) ⊓ ℚ ∙ v := by rw [hset]
    _ ≤ Work.SurgeryInvariance.WindingSpan P (A ∪ B₂) ⊔
          Work.SurgeryInvariance.WindingSpan P B₁ := hvkey
    _ ≤ Work.SurgeryInvariance.WindingSpan P A ⊔
          Work.SurgeryInvariance.WindingSpan P B := by
        rw [hWA₂, hVB₁, hVA, hVB]

end Work.PinchLemma3.ClosedDiscA
