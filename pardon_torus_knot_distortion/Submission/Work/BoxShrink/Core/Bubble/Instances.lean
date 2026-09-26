import Submission.Work.BoxShrink.Core.Bubble.Persistence

/-!
# The double-bubble datum: content, and a non-vacuity instance

This file relates the two forms of the double-bubble datum of
`Submission.Work.BoxShrink.Core.Bubble.Defs`:

* `bubbleSweep_of_doubleBubbleDatum` — the loop-level datum `DoubleBubbleDatum`
  (`RegionEquivalent P (boxRegion) (upperRegion ∪ lowerRegion)`) supplies a `BubbleSweep`: take the
  two-point family which is the region inside the sphere for `t < 1` and the union of the two
  half-regions for `t ≥ 1`; the only exceptional parameter is `t = 1`, where the local move is the
  region-equivalence itself.  So `BubbleSweep` is the "family with local models" form of exactly the
  loop-level statement;
* `bubbleSweep_of_empty_slice` — a `BubbleSweep` exists whenever the plane misses the region of the
  surface inside the sphere: then the region is *already* the union of the two half-regions
  (`boxRegion_eq_union`), and the constant family is a sweep.  This is the non-vacuity check on the
  local-model datum.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Core

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-- The local move at the exceptional parameter of the two-point family: from the region inside the
sphere (`= A'` at time `1`) the loop content is transported to the other region (which is `A` below
time `1` and `A'` above it). -/
theorem surgeryStepZero_or_regionEquivalent_twoPoint {A A' : Set R3}
    (h : Work.SurgeryInvariance.RegionEquivalent P A A') (s : ℝ) :
    Work.SurgeryInvariance.SurgeryStepZero P (if (1 : ℝ) < 1 then A else A')
        (if s < (1 : ℝ) then A else A') ∨
      Work.SurgeryInvariance.RegionEquivalent P (if (1 : ℝ) < 1 then A else A')
        (if s < (1 : ℝ) then A else A') := by
  rw [if_neg (lt_irrefl (1 : ℝ))]
  by_cases hs : s < 1
  · rw [if_pos hs]; exact Or.inr h.symm
  · rw [if_neg hs]; exact Or.inr (Work.SurgeryInvariance.RegionEquivalent.refl A')

/-- Off the exceptional parameter the two-point family is constant (both `t` and `s` lie on the
same side of `1`), so the loop content is transported trivially. -/
theorem regionEquivalent_twoPoint_of_abs_sub_lt {A A' : Set R3} {t s : ℝ} (ht : t ≠ 1)
    (hs : |s - t| < |1 - t|) :
    Work.SurgeryInvariance.RegionEquivalent P (if t < (1 : ℝ) then A else A')
      (if s < (1 : ℝ) then A else A') := by
  rcases lt_trichotomy t 1 with hlt | heq | hgt
  · have hslt : s < 1 := by
      have h1 : |1 - t| = 1 - t := abs_of_pos (by linarith)
      rw [h1] at hs
      linarith [(abs_lt.mp hs).2]
    rw [if_pos hlt, if_pos hslt]
    exact Work.SurgeryInvariance.RegionEquivalent.refl A
  · exact absurd heq ht
  · have hsge : ¬ s < 1 := by
      have h1 : |1 - t| = t - 1 := by rw [abs_of_neg (by linarith)]; ring
      rw [h1] at hs
      linarith [(abs_lt.mp hs).1]
    rw [if_neg (not_lt.mpr (le_of_lt hgt)), if_neg hsge]
    exact Work.SurgeryInvariance.RegionEquivalent.refl A'

/-- **The loop-level datum supplies a `BubbleSweep`.** -/
theorem bubbleSweep_of_doubleBubbleDatum (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (h : DoubleBubbleDatum P s c σ u) : Nonempty (BubbleSweep P s c σ u) := by
  classical
  have hre : Work.SurgeryInvariance.RegionEquivalent P (boxRegion P s c σ)
      (upperRegion P s c σ u ∪ lowerRegion P s c σ u) := h
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact fun t : ℝ => if t < (1 : ℝ) then boxRegion P s c σ
        else upperRegion P s c σ u ∪ lowerRegion P s c σ u
    · exact {1}
    · intro t ht
      have ht1 : t ≠ 1 := by simpa using ht
      refine ⟨|1 - t|, abs_pos.mpr (sub_ne_zero.mpr (Ne.symm ht1)), ?_, ?_⟩
      · intro r hr
        simp only [Finset.mem_singleton]
        intro hr1
        rw [hr1, abs_sub_comm] at hr
        exact absurd hr (lt_irrefl _)
      · intro r hr
        exact regionEquivalent_twoPoint_of_abs_sub_lt (P := P) (A := boxRegion P s c σ)
          (A' := upperRegion P s c σ u ∪ lowerRegion P s c σ u) ht1 hr
    · intro t ht
      have ht1 : t = 1 := by simpa using ht
      subst ht1
      refine ⟨1, one_pos, ?_⟩
      intro r _
      exact surgeryStepZero_or_regionEquivalent_twoPoint (P := P) (A := boxRegion P s c σ)
        (A' := upperRegion P s c σ u ∪ lowerRegion P s c σ u) hre r
  · show (if (0 : ℝ) < 1 then boxRegion P s c σ
        else upperRegion P s c σ u ∪ lowerRegion P s c σ u) = boxRegion P s c σ
    rw [if_pos (by norm_num : (0 : ℝ) < 1)]
  · show (if (1 : ℝ) < 1 then boxRegion P s c σ
        else upperRegion P s c σ u ∪ lowerRegion P s c σ u) =
      upperRegion P s c σ u ∪ lowerRegion P s c σ u
    rw [if_neg (lt_irrefl (1 : ℝ))]

/-- **Non-vacuity of the double-bubble datum.**  If the cutting plane misses the region of the
surface inside the sphere, then that region *is* the union of the two half-regions, and the constant
family is a `BubbleSweep`: the local model is satisfied without any surgery. -/
theorem bubbleSweep_of_empty_slice (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (h : sliceRegion P s c σ u = ∅) : Nonempty (BubbleSweep P s c σ u) := by
  classical
  have hcover : boxRegion P s c σ = upperRegion P s c σ u ∪ lowerRegion P s c σ u := by
    rw [boxRegion_eq_union, h, Set.union_empty]
  exact ⟨{ sweep := Work.SurgeryInvariance.SweepLoops.const (P := P)
              (upperRegion P s c σ u ∪ lowerRegion P s c σ u)
           zero := hcover.symm
           one := rfl }⟩

/-- **Non-vacuity of the conclusion of the double-bubble core.**  If the cutting plane misses the
region of the surface inside the sphere, the conclusion of `Work.BoxShrink.CruxCore` holds outright:
the region is the disjoint union of the two half-regions, which are open in the surface, so the
essential loop of a smaller box lies in one of them.  So the two alternatives of the core are not
empty, and the reduction of `cruxCore_of_bubbleInput` is a statement about a true conclusion. -/
theorem exists_essential_half_of_empty_slice {r s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hrs : r ≤ s) (h : sliceRegion P s c σ u = ∅) (hbox : Submission.HasEssBox P r c σ) :
    (∃ γ : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P γ ∧
        ∀ t : ℝ, γ t ∈ Submission.PBox s c σ ∧ c (σ 2) + u < γ t (σ 2)) ∨
      (∃ γ : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P γ ∧
        ∀ t : ℝ, γ t ∈ Submission.PBox s c σ ∧ γ t (σ 2) < c (σ 2) + u) := by
  obtain ⟨B⟩ := bubbleSweep_of_empty_slice (P := P) s c σ u h
  have hbox' : P.ContainsEssentialLoop (boxRegion P s c σ) :=
    containsEssentialLoop_boxRegion_of_hasEssBox (P := P) (c := c) (σ := σ) hrs hbox
  rcases containsEssentialLoop_half_of_bubbleSweep (P := P) B hbox' with hup | hlo
  · exact Or.inl ((containsEssentialLoop_upperRegion_iff P s c σ u).mp hup)
  · exact Or.inr ((containsEssentialLoop_lowerRegion_iff P s c σ u).mp hlo)

end

end Work.BoxShrink.Core
