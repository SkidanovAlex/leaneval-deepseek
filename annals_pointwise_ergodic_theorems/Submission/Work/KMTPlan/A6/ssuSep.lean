import Mathlib
import Submission.Work.KMTPlan.A6.SsuDefs

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.KMTAreas.A7

/-!
# Separation of the exact-height frequencies from the lower Ionescu--Wainger level

This module proves `ssuSep`: the arithmetic frequencies of the *exact* height layer
`diffFreqs ρ l = (ℚ/ℤ)_{≤l} \ (ℚ/ℤ)_{≤l-1}` are separated from the arithmetic frequencies
`(ℚ/ℤ)_{≤l-1}` of the previous level by at least `2^{k'} + 2^{-3u}`, whenever the two
truncation parameters satisfy `k' ≤ -(C (1 + l 2^{ρl/2} + l) + 1)` and
`3u ≥ C (1 + l 2^{ρl/2} + l) + 1`.

The content is the sharp separation of two distinct elements of `(ℚ/ℤ)_{≤l}`
(`Work.KMTPlan.A6.iwArithFreqs_separated`), together with monotonicity
`iwArithFreqs ρ (l-1) ⊆ iwArithFreqs ρ l`: any `α` of the lower level and any `β` of the exact
layer `l` are distinct elements of `(ℚ/ℤ)_{≤l}`, hence `‖β - α‖ ≥ 2^{-K (1 + l 2^{ρl/2} + l)}`,
and the two truncation errors `2^{k'}`, `2^{-3u}` are each `≤ 2^{-(K+1)(1 + l 2^{ρl/2} + l)}`,
so that their sum is `< 2^{-K (1 + l 2^{ρl/2} + l)}` with room to spare.
-/

theorem ssuSep (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l u : ℕ) (k' : ℤ), 1 ≤ l →
      C * (1 + (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) + (l : ℝ)) + 1 ≤ 3 * (u : ℝ) →
      C * (1 + (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) + (l : ℝ)) + 1 ≤ -(k' : ℝ) →
      ∀ α ∈ iwArithFreqs ρ (l - 1), ∀ β ∈ Work.KMTAreas.A7.diffFreqs ρ l,
        (2 : ℝ) ^ k' + (2 : ℝ) ^ (-(3 * (u : ℤ))) < ‖β - α‖ := by
  obtain ⟨K, hKpos, hK⟩ := iwArithFreqs_separated ρ hρ hρ1
  refine ⟨K + 2, by linarith, ?_⟩
  intro l u k' hl hu hk α hα β hβ
  set E : ℝ := 1 + (l : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) + (l : ℝ) with hE
  -- the two levels are nested, so `α` and `β` both lie in the level-`l` frequency set
  have hl0 : l ≠ 0 := by omega
  have hβ' : β ∈ iwArithFreqs ρ l ∧ β ∉ iwArithFreqs ρ (l - 1) := by
    have h := hβ
    rw [Work.KMTAreas.A7.diffFreqs, if_neg hl0] at h
    exact Finset.mem_sdiff.mp h
  obtain ⟨hβl, hβnot⟩ := hβ'
  have hαl : α ∈ iwArithFreqs ρ l := iwArithFreqs_mono hρ hρ1 (Nat.pred_le l) hα
  have hne : α ≠ β := by
    intro hEq
    exact hβnot (hEq ▸ hα)
  -- the sharp separation of the level-`l` frequency set
  have hsep : (2 : ℝ) ^ (-(K * E)) ≤ ‖α - β‖ := by
    have hh := hK l α β hαl hβl hne
    simpa [hE] using hh
  have huE : (K + 2) * E + 1 ≤ 3 * (u : ℝ) := by simpa [hE] using hu
  have hkE : (K + 2) * E + 1 ≤ -(k' : ℝ) := by simpa [hE] using hk
  have hE1 : (1 : ℝ) ≤ E := by
    rw [hE]
    have ht : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
    have hl0' : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    nlinarith [mul_nonneg hl0' ht]
  have hEpos : (0 : ℝ) < E := lt_of_lt_of_le one_pos hE1
  have hbase : (1 : ℝ) < 2 := by norm_num
  -- the two truncation errors are each `≤ 2^{-((K+2)E+1)}`
  have hkr : (k' : ℝ) ≤ -((K + 2) * E + 1) := by linarith [hkE]
  have hkpow : (2 : ℝ) ^ k' ≤ (2 : ℝ) ^ (-((K + 2) * E + 1)) := by
    calc (2 : ℝ) ^ k' = (2 : ℝ) ^ ((k' : ℝ)) := (Real.rpow_intCast 2 k').symm
      _ ≤ (2 : ℝ) ^ (-((K + 2) * E + 1)) := (Real.rpow_le_rpow_left_iff hbase).mpr hkr
  have hur : -(3 * (u : ℝ)) ≤ -((K + 2) * E + 1) := by linarith [huE]
  have hupow : (2 : ℝ) ^ (-(3 * (u : ℤ))) ≤ (2 : ℝ) ^ (-((K + 2) * E + 1)) := by
    calc (2 : ℝ) ^ (-(3 * (u : ℤ))) = (2 : ℝ) ^ (((-(3 * (u : ℤ)) : ℤ)) : ℝ) :=
          (Real.rpow_intCast 2 (-(3 * (u : ℤ)))).symm
      _ = (2 : ℝ) ^ (-(3 * (u : ℝ))) := by
          congr 1
          push_cast
          ring
      _ ≤ (2 : ℝ) ^ (-((K + 2) * E + 1)) := (Real.rpow_le_rpow_left_iff hbase).mpr hur
  have hsum : (2 : ℝ) ^ k' + (2 : ℝ) ^ (-(3 * (u : ℤ)))
      ≤ (2 : ℝ) ^ (-((K + 2) * E + 1)) + (2 : ℝ) ^ (-((K + 2) * E + 1)) :=
    add_le_add hkpow hupow
  have htwice : (2 : ℝ) ^ (-((K + 2) * E + 1)) + (2 : ℝ) ^ (-((K + 2) * E + 1))
      = (2 : ℝ) ^ (-((K + 2) * E)) := by
    have h1 : (2 : ℝ) ^ (-((K + 2) * E + 1)) + (2 : ℝ) ^ (-((K + 2) * E + 1))
        = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-((K + 2) * E + 1)) := by
      rw [Real.rpow_one]; ring
    rw [h1, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  -- and their sum is strictly below the separation radius, since `K < K + 2` and `E > 0`
  have hlt : (2 : ℝ) ^ (-((K + 2) * E)) < (2 : ℝ) ^ (-(K * E)) := by
    refine (Real.rpow_lt_rpow_left_iff hbase).mpr ?_
    have hKlt : K < K + 2 := by linarith
    have := mul_lt_mul_of_pos_right hKlt hEpos
    linarith
  calc (2 : ℝ) ^ k' + (2 : ℝ) ^ (-(3 * (u : ℤ))) < (2 : ℝ) ^ (-(K * E)) :=
        lt_of_le_of_lt (hsum.trans (le_of_eq htwice)) hlt
    _ ≤ ‖α - β‖ := hsep
    _ = ‖β - α‖ := (norm_sub_rev β α).symm

end Work.KMTPlan.A6
