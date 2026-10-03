/-
# `Submission.Work.FIArea7CF.Gwt_sum_le` — clash-free copy of `Submission.Work.FIArea7.Gwt_sum_le`

Imports redirected to the `FIArea7CF` copies; renamed: gnorm_mk_eq→cfx_gnorm_mk_eq, mem_gBox_iff→r2c_mem_gBox_iff.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7.ACDefs
import Submission.Work.FIArea7CF.r2count_sq_lower
import Submission.Work.FIArea7.R2_bound

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. Two easy reductions -/

/-- `Gwt 0 = 1`: the empty product over the prime factors of `0`. -/
lemma Gwt_zero : Gwt 0 = 1 := by
  rw [Gwt, Nat.primeFactors_zero]
  simp

/-- The Gaussian box count and the pair count agree (both are `(targetF n).card`). -/
lemma r2count_eq_r2pair (n : ℕ) : r2count n = r2pair n := by
  rw [r2count_eq_targetF_card, ← r2pair_eq_targetF_card]

/-- **`4 · Gwt s ≤ r2count (s²)`**, cast to `ℝ` and with `Gwt` written as the corresponding real
product.  Immediate from `r2count_sq_lower`. -/
lemma four_Gwt_le_r2pair (s : ℕ) (hs : 0 < s) : 4 * Gwt s ≤ (r2pair (s ^ 2) : ℝ) := by
  have h := r2count_sq_lower s hs
  rw [r2count_eq_r2pair] at h
  have h2 : ((4 * ∏ p ∈ s.primeFactors.filter (fun p => p % 4 = 1),
      (2 * s.factorization p + 1) : ℕ) : ℝ) ≤ (r2pair (s ^ 2) : ℝ) := by
    exact_mod_cast h
  rw [Gwt]
  push_cast at h2 ⊢
  exact h2

/-! ## 1. The number of representations of the squares `s²`, `1 ≤ s ≤ Y` -/

/-- The set of integer pairs counted by `r2pair n`. -/
def r2set (n : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ (Finset.Icc (-(n : ℤ)) (n : ℤ))).filter
    (fun q : ℤ × ℤ => q.1 ^ 2 + q.2 ^ 2 = (n : ℤ))

lemma r2pair_eq_card_r2set (n : ℕ) : r2pair n = (r2set n).card := rfl

/-- The fibre over the third coordinate `i + 1`: the pairs representing `(i+1)²` in the box. -/
def piece (i : ℕ) : Finset ((ℤ × ℤ) × ℕ) := (r2set ((i + 1) ^ 2)) ×ˢ ({i + 1} : Finset ℕ)

lemma piece_card (i : ℕ) : (piece i).card = (r2pair ((i + 1) ^ 2)) := by
  rw [piece, Finset.card_product, Finset.card_singleton, Nat.mul_one, r2pair_eq_card_r2set]

/-- Every fibre lies in `SS Y`: if `a² + b² = s²` with `1 ≤ s ≤ Y` then `|a|, |b| ≤ s ≤ Y`. -/
lemma piece_subset_SS {Y i : ℕ} (hi : i ∈ Finset.range Y) : piece i ⊆ SS Y := by
  intro x hx
  obtain ⟨q, c⟩ := x
  rw [piece, Finset.mem_product, Finset.mem_singleton] at hx
  obtain ⟨hq, hc⟩ := hx
  subst hc
  have hY : i + 1 ≤ Y := by have := Finset.mem_range.mp hi; omega
  rw [r2set, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hq
  obtain ⟨⟨hq1, hq2⟩, hsq⟩ := hq
  have hsq' : q.1 ^ 2 + q.2 ^ 2 = ((i : ℤ) + 1) ^ 2 := by
    rw [hsq]; push_cast; ring
  have hb1 : |q.1| ≤ ((i : ℤ) + 1) := by
    have hle : q.1 ^ 2 ≤ ((i : ℤ) + 1) ^ 2 := by nlinarith [sq_nonneg q.2]
    have h3 := sq_le_sq.mp hle
    rwa [abs_of_nonneg (by positivity : (0:ℤ) ≤ (i:ℤ) + 1)] at h3
  have hb2 : |q.2| ≤ ((i : ℤ) + 1) := by
    have hle : q.2 ^ 2 ≤ ((i : ℤ) + 1) ^ 2 := by nlinarith [sq_nonneg q.1]
    have h3 := sq_le_sq.mp hle
    rwa [abs_of_nonneg (by positivity : (0:ℤ) ≤ (i:ℤ) + 1)] at h3
  have hb1Y : |q.1| ≤ (Y : ℤ) := by
    have : ((i : ℤ) + 1) ≤ (Y : ℤ) := by exact_mod_cast hY
    linarith
  have hb2Y : |q.2| ≤ (Y : ℤ) := by
    have : ((i : ℤ) + 1) ≤ (Y : ℤ) := by exact_mod_cast hY
    linarith
  have hqmem : q ∈ (Finset.Icc (-(Y : ℤ)) (Y : ℤ)) ×ˢ (Finset.Icc (-(Y : ℤ)) (Y : ℤ)) := by
    rw [Finset.mem_product]
    exact ⟨by rw [Finset.mem_Icc, ← abs_le]; exact hb1Y,
           by rw [Finset.mem_Icc, ← abs_le]; exact hb2Y⟩
  have hcmem : i + 1 ∈ Finset.Icc 1 Y := by
    rw [Finset.mem_Icc]; exact ⟨by omega, hY⟩
  have hpyth : q.1 ^ 2 + q.2 ^ 2 = ((i + 1 : ℕ) : ℤ) ^ 2 := by
    rw [hsq']; push_cast; ring
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hqmem, hcmem⟩, ?_⟩
  exact hpyth

/-- **`∑_{i<Y} r2count ((i+1)²) ≤ (SS Y).card`**: the `Y` fibres are disjoint subsets of `SS Y`. -/
lemma sum_r2pair_le_SS (Y : ℕ) :
    ∑ i ∈ Finset.range Y, (r2pair ((i + 1) ^ 2) : ℝ) ≤ ((SS Y).card : ℝ) := by
  have hdisj : (Finset.range Y : Set ℕ).PairwiseDisjoint piece := by
    intro a _ b _ hab
    simp only [Function.onFun]
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy hxy
    rw [piece, Finset.mem_product, Finset.mem_singleton] at hx hy
    subst hxy
    omega
  calc ∑ i ∈ Finset.range Y, (r2pair ((i + 1) ^ 2) : ℝ)
      = (((Finset.range Y).biUnion piece).card : ℝ) := by
        rw [Finset.card_biUnion hdisj, Nat.cast_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [piece_card]
    _ ≤ ((SS Y).card : ℝ) := by
        exact_mod_cast Finset.card_le_card ((Finset.biUnion_subset).mpr
          (fun i hi => piece_subset_SS hi))

/-! ## 2. The theorem -/

-- Hint: `Work.FIArea7.Gwt s = ∏_{p ∣ s, p ≡ 1 (4)} (2 v_p(s) + 1)` as a real product, and
-- `r2count_sq_lower` gives, after `push_cast`, `4 * Gwt s ≤ r2count (s ^ 2)` for `s > 0`.
-- Sum over `s ∈ range (Y+1)`: peel off `s = 0`, where `Gwt 0 = 1` (empty product) is absorbed by
-- `(Y+1) * (1 + Real.log (2+Y)) ≥ 1`.  For `1 ≤ s ≤ Y` the set `{w ∈ gBox (s^2) : gnorm w = s^2}`
-- is in bijection with the triples `((a,b),s)` with `|a|,|b| ≤ Y`, `1 ≤ s ≤ Y`, `a^2 + b^2 = s^2`
-- (send `w ↦ (w.re, w.im, s)`; the bounds are automatic since `a^2 ≤ s^2`), and the number of such
-- triples is at most the cardinality `(Work.FIArea7.SS Y).card` bounded by
-- `Work.FIArea7.R2_bound` (already proved): there is `C > 0` with
-- `((SS Y).card : ℝ) ≤ C * ((Y:ℝ) + 1) * (1 + Real.log (2 + (Y:ℝ)))`.  Combine the two constants.
theorem Gwt_sum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℕ,
      (∑ s ∈ Finset.range (Y + 1), Work.FIArea7.Gwt s)
        ≤ C * ((Y : ℝ) + 1) * (1 + Real.log (2 + (Y : ℝ))) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := R2_bound
  refine ⟨1 + C₀ / 4, by linarith, fun Y => ?_⟩
  set M : ℝ := ((Y : ℝ) + 1) * (1 + Real.log (2 + (Y : ℝ))) with hMdef
  have hMge : 1 ≤ M := by
    rw [hMdef]
    have hlog : (1:ℝ) ≤ 1 + Real.log (2 + (Y:ℝ)) := by
      have h1 : (1:ℝ) ≤ 2 + (Y:ℝ) := by
        have : (0:ℝ) ≤ (Y:ℝ) := Nat.cast_nonneg Y
        linarith
      have := Real.log_nonneg h1
      linarith
    have hY1 : (1:ℝ) ≤ (Y:ℝ) + 1 := by
      have : (0:ℝ) ≤ (Y:ℝ) := Nat.cast_nonneg Y
      linarith
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ ((Y:ℝ)+1) * (1 + Real.log (2 + (Y:ℝ))) :=
          mul_le_mul hY1 hlog (by linarith) (by linarith)
  have hterm : ∀ i ∈ Finset.range Y, Gwt (i+1) ≤ (1/4) * (r2pair ((i+1)^2) : ℝ) := by
    intro i _
    have h := four_Gwt_le_r2pair (i+1) (Nat.succ_pos i)
    linarith
  have hsum : ∑ i ∈ Finset.range Y, Gwt (i + 1) ≤ (1/4) * ((SS Y).card : ℝ) := by
    calc ∑ i ∈ Finset.range Y, Gwt (i+1)
        ≤ ∑ i ∈ Finset.range Y, (1/4) * (r2pair ((i+1)^2) : ℝ) := Finset.sum_le_sum hterm
      _ = (1/4) * ∑ i ∈ Finset.range Y, (r2pair ((i+1)^2) : ℝ) := by rw [Finset.mul_sum]
      _ ≤ (1/4) * ((SS Y).card : ℝ) :=
          mul_le_mul_of_nonneg_left (sum_r2pair_le_SS Y) (by norm_num)
  have hC : ((SS Y).card : ℝ) ≤ C₀ * M := by
    rw [show C₀ * M = C₀ * ((Y:ℝ) + 1) * (1 + Real.log (2 + (Y:ℝ))) by rw [hMdef]; ring]
    exact hC₀ Y
  have main : ∑ s ∈ Finset.range (Y + 1), Gwt s ≤ 1 + (1/4) * (C₀ * M) := by
    rw [Finset.sum_range_succ' (fun s => Gwt s) Y, Gwt_zero]
    have h2 : (1/4) * ((SS Y).card : ℝ) ≤ (1/4) * (C₀ * M) :=
      mul_le_mul_of_nonneg_left hC (by norm_num)
    linarith
  have hlast : 1 + (1/4) * (C₀ * M) ≤ (1 + C₀ / 4) * M := by
    nlinarith [hMge, hC₀pos]
  calc ∑ s ∈ Finset.range (Y + 1), Gwt s ≤ 1 + (1/4) * (C₀ * M) := main
    _ ≤ (1 + C₀ / 4) * M := hlast
    _ = (1 + C₀ / 4) * ((Y : ℝ) + 1) * (1 + Real.log (2 + (Y : ℝ))) := by rw [hMdef]; ring

end

end Work.FIArea7
