/-
# The constant comparison for the fibre mass bound

The derivative `∫`-bound of §6 (`fibreMass_hbd`) produces the constant

`fibHbdC = 64 · M₀ · Cφ · Cψ · q²(1+S²/N) · λ₁ · max (λ₂N^d) 1`,
  `λ₁ = 2^{k₁}/2^{Log N}`, `λ₂ = 2^{dk₂}/2^{d Log N}`, `S = 2^{k₁} + 2^{dk₂}`,

while the fibre-mass bound itself is stated with the single constant

`fibConst = max 1 (6400 · 2^{d+1} · M₀ · Cφ · Cψ)`.

This file proves the comparison `100 · fibHbdC ≤ fibConst · q²(1+S²/N) · 2^{k₁+dk₂}/N`, i.e. that
`fibConst` dominates `100 · fibHbdC` up to the harmless pair of factors present on both sides.
This is the arithmetic content of `Work.KMTAreas.A7.FibreMassKernel`.

## The mathematics

Cancelling `64 M₀ Cφ Cψ q²(1+S²/N) ≥ 0` and `2^{k₁}`, the inequality is the two-regime bookkeeping
of `FibreMassHbdDefs.fibHbdc`:

* if `max (λ₂ N^d) 1 = λ₂ N^d` (so `λ₂N^d ≥ 1`), the left side is
  `6400 C N^d/L^{d+1} · 2^{k₁+dk₂}` and one uses `(N/L)^{d+1} ≤ 2^{d+1}`, i.e. `N ≤ 2L`
  (`Log N` is `log₂` of `max N 2`, so `2^{Log N} ≥ N/2`);
* if `max (λ₂ N^d) 1 = 1`, the left side is `6400 C/L · 2^{k₁}` and one uses `2^{dk₂} ≥ 1` and
  `N ≤ 2L` together with the crude `12800 C ≤ fibConst`.

Both cases are absorbed by `fibConstP ≥ 6400·2^{d+1}·M₀CφCψ ≥ 12800·M₀CφCψ`.

## Note on a name clash

`Submission/Work/KMTAreas/A7/FibreMassHbd.lean` also declares
`Work.KMTAreas.A7.fibreMass_const_compare` (there as a `sorry` stub).  The two modules must not be
imported together; the stub in `FibreMassHbd.lean` should be deleted or replaced by an import of
this module.  This module is self-contained and imports neither `FibreMassHbd` nor `FibreMassKernel`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.FibreMassHbdDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

/-! ## Elementary properties of the scale `2^{Log N}` -/

/-- `2^{Log N} = lothN N` is at least `N/2`: since `Log N = ⌊log₂ max(N,2)⌋` and
`max(N,2) < 2^{Log N + 1}`. -/
theorem lothN_ge_half_N (N : ℕ) : (N : ℝ) ≤ 2 * Work.KMTPlan.A6.lothN N := by
  have hlt : max N 2 < 2 ^ (Nat.log 2 (max N 2) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) (max N 2)
  have h2 : max N 2 ≤ 2 * 2 ^ Nat.log 2 (max N 2) := by
    have h : 2 ^ (Nat.log 2 (max N 2) + 1) = 2 * 2 ^ Nat.log 2 (max N 2) := by
      rw [pow_succ, mul_comm]
    omega
  have heq : Work.KMTPlan.A6.lothN N = (((2 : ℕ) ^ Nat.log 2 (max N 2) : ℕ) : ℝ) := by
    rw [Work.KMTPlan.A6.lothN, Work.Analysis.EndVar.logN]
    push_cast
    rw [Real.rpow_natCast]
  rw [heq]
  have hcast : ((max N 2 : ℕ) : ℝ) ≤ 2 * (((2 : ℕ) ^ Nat.log 2 (max N 2) : ℕ) : ℝ) := by
    exact_mod_cast h2
  have hNmax : (N : ℝ) ≤ ((max N 2 : ℕ) : ℝ) := by
    have : N ≤ max N 2 := le_max_left _ _
    exact_mod_cast this
  linarith

/-! ## The two-regime arithmetic -/

/-- The real-inequality core of the constant comparison.  With `L = 2^{Log N} ≥ N/2`, `C = M₀CφCψ`,
`B = q²(1+S²/N)` and `M ≥ 6400·C·2^{d+1}`, one has

`100 · 64 C B (2^{k₁}/L) max(2^{dk₂}N^d/L^d, 1) ≤ M B 2^{k₁+dk₂}/N`.

The case `max = 2^{dk₂}N^d/L^d` uses `(N/L)^{d+1} ≤ 2^{d+1}`; the case `max = 1` uses `2^{dk₂} ≥ 1`
and `N ≤ 2L`. -/
theorem fibreMass_key (C B L N M : ℝ) (k₁ k₂ d : ℕ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hL : 0 < L) (hN : 0 < N)
    (hNL : N ≤ 2 * L) (hM : 6400 * C * 2 ^ (d + 1) ≤ M) :
    100 * (64 * C * B * ((2 : ℝ) ^ k₁ / L) * max ((2 : ℝ) ^ (d * k₂) / L ^ d * N ^ d) 1)
      ≤ M * B * (2 : ℝ) ^ (k₁ + d * k₂) / N := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hP : (0 : ℝ) < (2 : ℝ) ^ k₁ := pow_pos h2 _
  have hQ : (0 : ℝ) < (2 : ℝ) ^ (d * k₂) := pow_pos h2 _
  have hQ1 : (1 : ℝ) ≤ (2 : ℝ) ^ (d * k₂) := one_le_pow₀ (by norm_num)
  have hNLpow : N ^ (d + 1) ≤ 2 ^ (d + 1) * L ^ (d + 1) := by
    have h1 : N / L ≤ 2 := by rw [div_le_iff₀ hL]; linarith
    have h2' := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ N / L) h1 (d + 1)
    rw [div_pow] at h2'
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < L ^ (d + 1))).mp h2'
  have hM2 : 12800 * C ≤ M := by
    have hle : (2 : ℝ) ≤ 2 ^ (d + 1) := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (d + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 6400 * C)
    nlinarith [hM, h]
  rw [pow_add]
  rcases le_or_gt 1 ((2 : ℝ) ^ (d * k₂) / L ^ d * N ^ d) with hA1 | hA1
  · rw [max_eq_left hA1]
    rw [show 100 * (64 * C * B * ((2 : ℝ) ^ k₁ / L) * ((2 : ℝ) ^ (d * k₂) / L ^ d * N ^ d))
        = B * (6400 * C * (2 : ℝ) ^ k₁ * ((2 : ℝ) ^ (d * k₂) / L ^ d * N ^ d) / L)
        by ring]
    rw [show M * B * ((2 : ℝ) ^ k₁ * (2 : ℝ) ^ (d * k₂)) / N
        = B * (M * (2 : ℝ) ^ k₁ * (2 : ℝ) ^ (d * k₂) / N) by ring]
    refine mul_le_mul_of_nonneg_left ?_ hB
    rw [show 6400 * C * (2 : ℝ) ^ k₁ * ((2 : ℝ) ^ (d * k₂) / L ^ d * N ^ d) / L
        = (2 : ℝ) ^ k₁ * (6400 * C * ((2 : ℝ) ^ (d * k₂) / L ^ d * N ^ d) / L) by ring]
    rw [show M * (2 : ℝ) ^ k₁ * (2 : ℝ) ^ (d * k₂) / N
        = (2 : ℝ) ^ k₁ * (M * (2 : ℝ) ^ (d * k₂) / N) by ring]
    rw [mul_le_mul_iff_of_pos_left hP]
    rw [show 6400 * C * ((2 : ℝ) ^ (d * k₂) / L ^ d * N ^ d) / L
        = (2 : ℝ) ^ (d * k₂) * (6400 * C * (N ^ d / (L ^ d * L))) by ring]
    rw [show M * (2 : ℝ) ^ (d * k₂) / N = (2 : ℝ) ^ (d * k₂) * (M / N) by ring]
    rw [mul_le_mul_iff_of_pos_left hQ]
    rw [le_div_iff₀ hN]
    rw [show 6400 * C * (N ^ d / (L ^ d * L)) * N = 6400 * C * (N ^ d * N) / (L ^ d * L)
        by ring]
    rw [← pow_succ]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < L ^ d * L)]
    rw [← pow_succ]
    have h4 := mul_le_mul_of_nonneg_right hM (by positivity : (0 : ℝ) ≤ L ^ (d + 1))
    have h5 := mul_le_mul_of_nonneg_left hNLpow (by positivity : (0 : ℝ) ≤ 6400 * C)
    nlinarith [h4, h5]
  · rw [max_eq_right (le_of_lt hA1)]
    rw [show 100 * (64 * C * B * ((2 : ℝ) ^ k₁ / L) * 1)
        = B * (6400 * C * (2 : ℝ) ^ k₁ / L) by ring]
    rw [show M * B * ((2 : ℝ) ^ k₁ * (2 : ℝ) ^ (d * k₂)) / N
        = B * (M * ((2 : ℝ) ^ k₁ * (2 : ℝ) ^ (d * k₂)) / N) by ring]
    refine mul_le_mul_of_nonneg_left ?_ hB
    rw [show 6400 * C * (2 : ℝ) ^ k₁ / L = (2 : ℝ) ^ k₁ * (6400 * C / L) by ring]
    rw [show M * ((2 : ℝ) ^ k₁ * (2 : ℝ) ^ (d * k₂)) / N
        = (2 : ℝ) ^ k₁ * (M * (2 : ℝ) ^ (d * k₂) / N) by ring]
    rw [mul_le_mul_iff_of_pos_left hP]
    have hMnn : 0 ≤ M := by
      have : (0 : ℝ) ≤ 6400 * C * 2 ^ (d + 1) := by positivity
      linarith [hM]
    have hQN : M / N ≤ M * (2 : ℝ) ^ (d * k₂) / N := by
      rw [le_div_iff₀ hN, div_mul_cancel₀ _ (ne_of_gt hN)]
      simpa using (mul_le_mul_of_nonneg_left hQ1 hMnn)
    have hbase : 6400 * C / L ≤ M / N := by
      rw [div_le_div_iff₀ hL hN]
      have ha := mul_le_mul_of_nonneg_left hNL (by positivity : (0 : ℝ) ≤ 6400 * C)
      have hb := mul_le_mul_of_nonneg_right hM2 (le_of_lt hL)
      nlinarith [ha, hb]
    linarith

/-! ## The comparison of the two constants -/

/-- **The constant comparison.**  `100 · fibHbdC` is dominated by `fibConst` times the two factors
`q²(1+S²/N)` and `2^{k₁+dk₂}/N` that occur on both sides of the fibre mass bound. -/
theorem fibreMass_const_compare (P : Polynomial ℤ) (N q k₁ k₂ : ℕ) (hN : 1 ≤ N) (hq : 0 < q) :
    100 * fibHbdC P N q k₁ k₂
      ≤ fibConst P * (q : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ))
          * (2 : ℝ) ^ (k₁ + P.natDegree * k₂) / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hBnn : 0 ≤ (q : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ)) := by positivity
  have hCnn : 0 ≤ fibM0C P * fibBumpCφ P * fibBumpCψ P :=
    mul_nonneg (mul_nonneg (fibM0C_pos P).le (fibBumpCφ_pos P).le) (fibBumpCψ_pos P).le
  have hM : 6400 * (fibM0C P * fibBumpCφ P * fibBumpCψ P) * 2 ^ (P.natDegree + 1)
      ≤ fibConst P := by
    rw [fibConst]
    exact le_trans (le_of_eq (by ring)) (le_max_right _ _)
  have hkey := fibreMass_key (fibM0C P * fibBumpCφ P * fibBumpCψ P)
      ((q : ℝ) ^ 2 * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ)))
      (Work.KMTPlan.A6.lothN N) (N : ℝ) (fibConst P)
      k₁ k₂ P.natDegree hCnn hBnn (Work.KMTPlan.A6.lothN_pos N) hNpos (lothN_ge_half_N N) hM
  rw [fibHbdC, fibLam₁, fibLam₂]
  convert hkey using 2 <;> ring

end

end Work.KMTAreas.A7
