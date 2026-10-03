/-
# The regime bookkeeping of the §6 small-scale model approximation (Area A7)

This module collects the *arithmetic* ingredients of the regime analysis of
`Work.KMTAreas.A7.smallModKernelMassBound`:

* `uScale_mono`, `splitCut_mono` — monotonicity of the auxiliary scale `u = ⌊2^{2ρL}⌋` and of the
  small-scale threshold `splitCut ρ L = 2^{2^{u}}`;
* `one_le_uScale` — `1 ≤ uScale ρ L`;
(the "window consequences" `2^{k - Log N} ≤ 2^{-(2u)-1}` and `2^{d(k - Log N)} ≤ 2^{-(2du)-1}` of the
main regime `k + 2u + 1 ≤ Log N`, used to feed the collapse, are proved in
`Submission/Work/KMTAreas/A7/smallModKernelMassBound.lean` and in the notes file
`NOTES_A7_smallModKernelMassBound_PLAN.md`);
* `smallL_le_of_not_nonAliasing` — **failure of the non-aliasing of the exact-height arithmetic
  frequencies at the arc radius `2^{-2u}` forces the loss scale `L = smallL l₁ l₂ k₁ k₂` to be
  bounded in terms of `ρ` alone.**  This is the key to the regime split of the §6 estimate: either
  the non-aliasing holds (and the collapse `concSymb - modSymbC = ∑_β spike_β` applies), or the
  scale `L` is bounded, and then the scale `N` is bounded as well by
  `N ≤ splitCut ρ L ≤ splitCut ρ D`, so the crude single-scale bound applies.

The proof of `smallL_le_of_not_nonAliasing` uses the A6 development (which carries the same
`max(max l₁ l₂)(max k₁ k₂)` scale under the name `lcL`):
`Work.KMTPlan.A6.nonAliasing_of_size` (good major arcs imply non-aliasing) and
`Work.KMTPlan.A6.lcL_le_of_not_nonAliasing` (failure of non-aliasing bounds `lcL`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.collapse
import Submission.Work.KMTPlan.A6.symC_sub_symM_eq_symD
import Submission.Work.KMTPlan.A6.lcL_le_of_not_nonAliasing

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-! ## Monotonicity of the auxiliary scales -/

/-- The auxiliary scale `u = ⌊2^{2ρL}⌋` is monotone in `L`. -/
theorem uScale_mono {ρ : ℝ} (hρ : 0 ≤ ρ) : Monotone fun L : ℕ => uScale ρ L := by
  intro L B hLB
  have hfloor : ⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋
      ≤ ⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (B : ℝ))⌋ := by
    refine Int.floor_mono ?_
    simp only [Nat.cast_one, one_mul]
    rw [Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)]
    have hLB' : (L : ℝ) ≤ (B : ℝ) := by exact_mod_cast hLB
    nlinarith
  have hL0 : (0 : ℤ) ≤ ⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ :=
    Int.floor_nonneg.mpr (by positivity)
  have hB0 : (0 : ℤ) ≤ ⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (B : ℝ))⌋ :=
    Int.floor_nonneg.mpr (by positivity)
  unfold uScale Work.Analysis.EndVar.scaleCount
  have hcast : ((⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋.toNat : ℤ))
      ≤ ((⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (B : ℝ))⌋.toNat : ℤ)) := by
    rw [Int.toNat_of_nonneg hL0, Int.toNat_of_nonneg hB0]
    exact hfloor
  exact_mod_cast hcast

/-- The small-scale threshold `splitCut ρ L = 2^{2^{u}}` is monotone in `L`. -/
theorem splitCut_mono (ρ : ℝ) (hρ : 0 ≤ ρ) {L B : ℕ} (h : L ≤ B) :
    splitCut ρ L ≤ splitCut ρ B := by
  unfold splitCut
  exact Nat.pow_le_pow_right (by norm_num)
    (Nat.pow_le_pow_right (by norm_num) (uScale_mono hρ h))


/-! ## Failure of non-aliasing bounds the loss scale -/

/-- **Failure of the non-aliasing of the exact-height arithmetic frequencies at the arc radius
`2^{-2u}` forces the loss scale `L = smallL l₁ l₂ k₁ k₂` to be bounded in terms of `ρ` alone.** -/
theorem smallL_le_of_not_nonAliasing (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ D : ℕ, ∀ l₁ l₂ k₁ k₂ : ℕ,
      (¬ Work.Analysis.IonescuWainger.NonAliasing
            (-(2 * ((Work.KMTAreas.A7.uScale ρ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂)) : ℤ)))
            (Work.KMTAreas.A7.diffFreqs ρ l₁) ∨
       ¬ Work.Analysis.IonescuWainger.NonAliasing
            (-(2 * ((Work.KMTAreas.A7.uScale ρ (Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂)) : ℤ)))
            (Work.KMTAreas.A7.diffFreqs ρ l₂)) →
      Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂ ≤ D := by
  obtain ⟨Cna, hCnapos, hsize⟩ := Work.KMTPlan.A6.nonAliasing_of_size ρ hρ hρ1
  have hsize' : ∀ (l : ℕ) (K : ℤ),
      (K : ℝ) + Cna * (2 : ℝ) ^ (ρ * (l : ℝ)) < 0 →
        Work.Analysis.IonescuWainger.NonAliasing K
          (Work.Analysis.IonescuWainger.iwArithFreqs ρ l) := by
    intro l K hK
    refine NonAliasing_of_subset (hsize l l K ?_) Finset.subset_union_left
    simpa using hK
  refine ⟨⌈Real.logb 2 Cna / ρ⌉₊ + 1, ?_⟩
  intro l₁ l₂ k₁ k₂ h
  by_contra hcon
  have hna : ¬ Work.Analysis.IonescuWainger.NonAliasing
      (-(2 * ((Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁
        ∪ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) := by
    rintro hNA
    rcases h with h | h
    · exact h (NonAliasing_of_subset hNA (Finset.Subset.trans
        (diffFreqs_subset_iwArithFreqs_le hρ hρ1 (le_refl l₁)) Finset.subset_union_left))
    · exact h (NonAliasing_of_subset hNA (Finset.Subset.trans
        (diffFreqs_subset_iwArithFreqs_le hρ hρ1 (le_refl l₂)) Finset.subset_union_right))
  exact hcon (Work.KMTPlan.A6.lcL_le_of_not_nonAliasing ρ hρ hρ1 Cna hCnapos hsize'
    l₁ l₂ k₁ k₂ hna)

end

end Work.KMTAreas.A7
