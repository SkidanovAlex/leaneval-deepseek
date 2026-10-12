import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.UBBInputs3.MatLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs3.MatLoc.profG_num` — the first-difference energy of the triangle profile

For the triangle profile `tri p s = max 0 (p + 1 - |s|)` (support `[-p,p]`, values
`p+1, p, …, 1`) the sum of the squared first differences over the widened interval
`[-p-1, p+1]` is

    Σ_{s=-p-1}^{p+1} (tri(s+1) - tri(s))² = 2 (p+1) .

Indeed `tri(s+1) - tri(s) = ±1` for `-p-1 ≤ s ≤ p` (it is `+1` on the increasing left
slope `[-p-1,-1]` and `-1` on the decreasing right slope `[0,p]`), and `0` at `s = p+1`;
the interval `[-p-1,p+1]` contains exactly `2p+2` such `±1` positions.

This is exactly the value quoted in `Defs` (there written `8(p+1)`, the count of the
`±1` positions weighted by the triangle… in fact `2(p+1)`), and it is the numerator of the
closed form `profG p = 24/(2p²+4p+3)` (see `MatLoc.profG_eq`).
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Work.UBBInputs3.MatLoc

/-- Pointwise value of the squared first difference of `tri p` on the interval
`[-(p+1), p]`: it is always `1`.  (On `[-p-1,-1]` the difference is `+1`, on `[0,p]` it
is `-1`.) -/
lemma triSuccSubSq_eq_one (p : ℕ) {s : ℤ} (hlo : -(p : ℤ) - 1 ≤ s) (hhi : s ≤ (p : ℤ)) :
    (Work.UBBInputs3.tri p (s + 1) - Work.UBBInputs3.tri p s) ^ 2 = 1 := by
  have hs_lo : -((p : ℝ) + 1) ≤ (s : ℝ) := by
    have h : ((-(p : ℤ) - 1 : ℤ) : ℝ) = -((p : ℝ) + 1) := by push_cast; ring
    rw [← h]
    exact_mod_cast hlo
  have hs_hi : (s : ℝ) ≤ (p : ℝ) := by exact_mod_cast hhi
  by_cases hs : s ≤ -1
  · -- left slope: `tri p s = p + s + 1`, `tri p (s+1) = p + s + 2`
    have hsm : (s : ℝ) ≤ -1 := by exact_mod_cast hs
    have h1 : |(s : ℝ)| = -(s : ℝ) := abs_of_nonpos (by linarith)
    have h2 : |((s + 1 : ℤ) : ℝ)| = -((s : ℝ) + 1) := by
      have hcast : ((s + 1 : ℤ) : ℝ) = (s : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      exact abs_of_nonpos (by linarith)
    have e1 : Work.UBBInputs3.tri p s = (p : ℝ) + 1 + (s : ℝ) := by
      simp only [Work.UBBInputs3.tri]
      rw [h1, max_eq_right (by linarith)]
      ring
    have e2 : Work.UBBInputs3.tri p (s + 1) = (p : ℝ) + 1 + ((s : ℝ) + 1) := by
      simp only [Work.UBBInputs3.tri]
      rw [h2, max_eq_right (by linarith)]
      ring
    rw [e1, e2]; ring
  · -- right slope: `tri p s = p + 1 - s`, `tri p (s+1) = p - s`
    have h0 : (0 : ℤ) ≤ s := by omega
    have hsnn : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast h0
    have h1 : |(s : ℝ)| = (s : ℝ) := abs_of_nonneg hsnn
    have h2 : |((s + 1 : ℤ) : ℝ)| = (s : ℝ) + 1 := by
      have hcast : ((s + 1 : ℤ) : ℝ) = (s : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      exact abs_of_nonneg (by linarith)
    have e1 : Work.UBBInputs3.tri p s = (p : ℝ) + 1 - (s : ℝ) := by
      simp only [Work.UBBInputs3.tri]
      rw [h1, max_eq_right (by linarith)]
    have e2 : Work.UBBInputs3.tri p (s + 1) = (p : ℝ) + 1 - ((s : ℝ) + 1) := by
      simp only [Work.UBBInputs3.tri]
      rw [h2, max_eq_right (by linarith)]
    rw [e1, e2]; ring

/-- The squared first difference of `tri p` at the free endpoint `s = p+1` is `0`. -/
lemma triSuccSubSq_eq_zero (p : ℕ) :
    (Work.UBBInputs3.tri p ((p : ℤ) + 1 + 1) - Work.UBBInputs3.tri p ((p : ℤ) + 1)) ^ 2
      = 0 := by
  have h1 : Work.UBBInputs3.tri p ((p : ℤ) + 1) = 0 := by
    simp only [Work.UBBInputs3.tri]
    have hcast : (((p : ℤ) + 1 : ℤ) : ℝ) = (p : ℝ) + 1 := by push_cast; ring
    rw [hcast, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ) + 1), sub_self, max_self]
  have h2 : Work.UBBInputs3.tri p ((p : ℤ) + 1 + 1) = 0 := by
    simp only [Work.UBBInputs3.tri]
    have hcast : (((p : ℤ) + 1 + 1 : ℤ) : ℝ) = (p : ℝ) + 2 := by push_cast; ring
    rw [hcast, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ) + 2)]
    rw [show (p : ℝ) + 1 - ((p : ℝ) + 2) = -1 by ring]
    norm_num
  rw [h1, h2]; ring

/-- On the summation interval `[-(p+1), p+1]` the squared first difference of `tri p`
is the indicator of `s ≤ p`. -/
lemma profG_num_pointwise (p : ℕ) {s : ℤ}
    (hs : s ∈ Finset.Icc (-(p : ℤ) - 1) ((p : ℤ) + 1)) :
    (Work.UBBInputs3.tri p (s + 1) - Work.UBBInputs3.tri p s) ^ 2
      = if s ≤ (p : ℤ) then 1 else 0 := by
  rw [Finset.mem_Icc] at hs
  obtain ⟨hlo, hhi⟩ := hs
  by_cases hc : s ≤ (p : ℤ)
  · rw [if_pos hc]; exact triSuccSubSq_eq_one p hlo hc
  · rw [if_neg hc]
    have hsp : s = (p : ℤ) + 1 := by omega
    rw [hsp]; exact triSuccSubSq_eq_zero p

theorem profG_num (p : ℕ) :
    ∑ s ∈ Finset.Icc (-(p : ℤ) - 1) ((p : ℤ) + 1),
        (Work.UBBInputs3.tri p (s + 1) - Work.UBBInputs3.tri p s) ^ 2
      = 2 * ((p : ℝ) + 1) := by
  rw [Finset.sum_congr rfl (fun s hs => profG_num_pointwise p hs)]
  rw [Finset.sum_boole]
  have hfilt : (Finset.Icc (-(p : ℤ) - 1) ((p : ℤ) + 1)).filter (fun s => s ≤ (p : ℤ))
      = Finset.Icc (-(p : ℤ) - 1) (p : ℤ) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hfilt]
  rw [Int.card_Icc]
  have hz : (p : ℤ) + 1 - (-(p : ℤ) - 1) = ((2 * (p + 1) : ℕ) : ℤ) := by push_cast; ring
  rw [hz, Int.toNat_natCast]
  push_cast
  ring

end Work.UBBInputs3.MatLoc
