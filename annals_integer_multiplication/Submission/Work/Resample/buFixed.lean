import Mathlib
import Submission.Work.ResMath.diagDp_entry_le_one

/-!
# `Work.Resample.buFixed`: the fixed-point bookkeeping of step `bu`

Paper §4.1, step **M7** of `resample.lean` (Harvey–van der Hoeven, "Integer multiplication in
time O(n log n)"): two facts about the fixed-point data.

* **Halving.** If `z = (x,y) ∈ C̃◦` (`x² + y² ≤ 2^{2p}`) then the pair `(x tdiv 2, y tdiv 2)`
  is again in `C̃◦` (truncation toward zero does not increase the absolute value), and it
  represents `z/2` up to error `≤ 1` in the scaled norm `2^p ‖·‖`:
  `2^p ‖fxC p (x tdiv 2, y tdiv 2) - fxC p z / 2‖ ≤ 1`.
  Writing `n = 2·(n tdiv 2) + n tmod 2` with `n tmod 2 ∈ {-1,0,1}`, each coordinate loses at most
  `1/2`, hence the two coordinates together at most `√2/2 < 1`.

* **The strict diagonal bound.** `‖D'_{ℓℓ}‖ ≤ 7/8` for `α ≥ 2`, where
  `D'_{ℓℓ} = e^{π α² β_ℓ²} / 2^{2α²-2}` with `|β_ℓ| ≤ 1/2`. The exponent is
  `π α² β² - (2α²-2) log 2 ≤ 2 log 2 - (2 log 2 - π/4)·α² ≤ -1` for `α² ≥ 4`, using
  `π < 3.1416` and `log 2 > 0.6931`; then `e^{-1} ≤ 1/2 ≤ 7/8`.
-/

namespace Work.Resample

open HvdH

/-! ## The halving of a fixed-point number -/

/-- Truncating division by `2` is within `1/2` of the true halving: `n = 2·(n tdiv 2) + n tmod 2`
with `n tmod 2 ∈ {-1,0,1}`. -/
private lemma tdiv_two_abs_sub_half (n : ℤ) :
    |(((n.tdiv 2 : ℤ) : ℝ) - (n : ℝ) / 2)| ≤ 1 / 2 := by
  have h : 2 * (n.tdiv 2) + n.tmod 2 = n := Int.mul_tdiv_add_tmod n 2
  rcases Int.tmod_two_eq n with h3 | h3 | h3
  · have h' : ((n.tdiv 2 : ℤ) : ℝ) = ((n : ℝ) + 1) / 2 := by
      have := congrArg (fun k : ℤ => (k : ℝ)) h
      rw [h3] at this; push_cast at this; linarith
    rw [h', abs_le]; constructor <;> linarith
  · have h' : ((n.tdiv 2 : ℤ) : ℝ) = (n : ℝ) / 2 := by
      have := congrArg (fun k : ℤ => (k : ℝ)) h
      rw [h3] at this; push_cast at this; linarith
    rw [h']; simp
  · have h' : ((n.tdiv 2 : ℤ) : ℝ) = ((n : ℝ) - 1) / 2 := by
      have := congrArg (fun k : ℤ => (k : ℝ)) h
      rw [h3] at this; push_cast at this; linarith
    rw [h', abs_le]; constructor <;> linarith

/-- Complex form of `tdiv_two_abs_sub_half`. -/
private lemma norm_tdiv_half_le (n : ℤ) : ‖(Int.tdiv n 2 : ℂ) - (n : ℂ) / 2‖ ≤ 1 / 2 := by
  have h := tdiv_two_abs_sub_half n
  have hcast : (Int.tdiv n 2 : ℂ) - (n : ℂ) / 2
      = ((((n.tdiv 2 : ℤ) : ℝ) - (n : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  exact h

/-- Truncating division by `2` does not increase the square: `(n tdiv 2)² ≤ n²`. -/
private lemma sq_tdiv_two_le (n : ℤ) : (n.tdiv 2) ^ 2 ≤ n ^ 2 := by
  rw [sq_le_sq, ← Int.natCast_natAbs (n.tdiv 2), ← Int.natCast_natAbs n, Int.natAbs_tdiv]
  exact_mod_cast Nat.div_le_self n.natAbs 2

/-- Scaling identity: `2^p · fxC p z` is the complex number `z.1 + i z.2` coded by `z`. -/
private lemma fxC_scale (p : ℕ) (z : ℤ × ℤ) :
    (((2 : ℝ) ^ p : ℝ) : ℂ) * HvdH.fxC p z = (z.1 : ℂ) + (z.2 : ℂ) * Complex.I := by
  rw [HvdH.fxC]
  have h : (((2 : ℝ) ^ p : ℝ) : ℂ) = (2 : ℂ) ^ p := by push_cast; ring
  rw [h]
  field_simp

/-! ## The strict bound on the diagonal of `D'` -/

/-- `β_ℓ = tℓ/s - rnd(tℓ/s)` lies in `[-1/2, 1/2]`. -/
private lemma betaR_abs_le_half (s t ℓ : ℕ) : |HvdH.betaR s t ℓ| ≤ 1 / 2 := by
  unfold HvdH.betaR HvdH.rnd
  set x : ℝ := (t : ℝ) * (ℓ : ℝ) / (s : ℝ) with hx
  have h1 : ((⌊x + 1 / 2⌋ : ℤ) : ℝ) ≤ x + 1 / 2 := Int.floor_le _
  have h2 : x + 1 / 2 - 1 < ((⌊x + 1 / 2⌋ : ℤ) : ℝ) := Int.sub_one_lt_floor _
  rw [abs_le]
  constructor <;> linarith

/-- The exponent of `D'_{ℓℓ}` is at most `-1` for `α ≥ 2`, `|β| ≤ 1/2`:
`π α² β² - (2α²-2) log 2 ≤ 2 log 2 - (2 log 2 - π/4) α² ≤ 1.3863 - 2.4 ≤ -1`. -/
private lemma exp_arg_le_neg_one (α : ℕ) (hα : 2 ≤ α) (β : ℝ) (hβ : |β| ≤ 1 / 2) :
    Real.pi * (α : ℝ) ^ 2 * β ^ 2 - ((2 * α ^ 2 - 2 : ℕ) : ℝ) * Real.log 2 ≤ -1 := by
  have hA4 : (4 : ℝ) ≤ (α : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα
    nlinarith
  have hA0 : (0 : ℝ) ≤ (α : ℝ) ^ 2 := by linarith
  have hB : β ^ 2 ≤ 1 / 4 := by
    rcases abs_le.mp hβ with ⟨h1, h2⟩
    nlinarith [sq_nonneg β]
  have hk : ((2 * α ^ 2 - 2 : ℕ) : ℝ) = 2 * (α : ℝ) ^ 2 - 2 := by
    have : 2 ≤ 2 * α ^ 2 := by nlinarith
    rw [Nat.cast_sub this]
    push_cast
    ring
  have hπ : Real.pi < 3.1416 := lt_trans Real.pi_lt_d20 (by norm_num)
  have hl1 : (0.6931 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hk0 : (0 : ℝ) ≤ 2 * (α : ℝ) ^ 2 - 2 := by linarith
  have h1 : Real.pi * (α : ℝ) ^ 2 * β ^ 2 ≤ (α : ℝ) ^ 2 * (3.1416 / 4) := by
    have hπA : (0 : ℝ) ≤ Real.pi * (α : ℝ) ^ 2 := mul_nonneg Real.pi_pos.le hA0
    have hstep : Real.pi * (α : ℝ) ^ 2 * β ^ 2 ≤ Real.pi * (α : ℝ) ^ 2 * (1 / 4) :=
      mul_le_mul_of_nonneg_left hB hπA
    have hπ4 : Real.pi / 4 ≤ 3.1416 / 4 := by linarith
    have hstep2 : (α : ℝ) ^ 2 * (Real.pi / 4) ≤ (α : ℝ) ^ 2 * (3.1416 / 4) :=
      mul_le_mul_of_nonneg_left hπ4 hA0
    nlinarith [hstep, hstep2]
  have h2 : (2 * (α : ℝ) ^ 2 - 2) * 0.6931 ≤ (2 * (α : ℝ) ^ 2 - 2) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hl1.le hk0
  rw [hk]
  linarith [h1, h2, hA4]

/-- `e^{π α² β²} / 2^{2α²-2} = e^{π α² β² - (2α²-2) log 2} ≤ e^{-1} ≤ 7/8`. -/
private lemma exp_bound_seven_eighths (α : ℕ) (hα : 2 ≤ α) (β : ℝ) (hβ : |β| ≤ 1 / 2) :
    Real.exp (Real.pi * (α : ℝ) ^ 2 * β ^ 2
      - ((2 * α ^ 2 - 2 : ℕ) : ℝ) * Real.log 2) ≤ 7 / 8 := by
  calc Real.exp (Real.pi * (α : ℝ) ^ 2 * β ^ 2 - ((2 * α ^ 2 - 2 : ℕ) : ℝ) * Real.log 2)
      ≤ Real.exp (-1) := Real.exp_le_exp.mpr (exp_arg_le_neg_one α hα β hβ)
    _ = (Real.exp 1)⁻¹ := Real.exp_neg 1
    _ ≤ 7 / 8 := by
        have h1 : (2 : ℝ) ≤ Real.exp 1 := by
          have := Real.add_one_le_exp (1 : ℝ)
          linarith
        have h2 : (Real.exp 1)⁻¹ ≤ ((2 : ℝ))⁻¹ := inv_anti₀ (by norm_num) h1
        linarith [h2]

/-- The diagonal entries of `D' = D/2^{2α²-2}` are bounded by `7/8` (strict form of
`Work.ResMath.diagDp_entry_le_one`, needed for the contraction `‖D'‖ ≤ 7/8` of step `bu`). -/
private lemma diagDp_entry_le_seven_eighths (s t α : ℕ) (hα : 2 ≤ α) (ℓ : Fin s) :
    ‖HvdH.diagD' s t α ℓ ℓ‖ ≤ 7 / 8 := by
  have hβ : |HvdH.betaR s t (ℓ : ℕ)| ≤ 1 / 2 := betaR_abs_le_half s t (ℓ : ℕ)
  have hval : HvdH.diagD' s t α ℓ ℓ
      = ((((1 : ℝ) / (2 : ℝ) ^ (2 * α ^ 2 - 2) *
          Real.exp (Real.pi * (α : ℝ) ^ 2 * (HvdH.betaR s t (ℓ : ℕ)) ^ 2)) : ℝ) : ℂ) := by
    simp [HvdH.diagD', HvdH.diagD, Matrix.diagonal_apply_eq]
  rw [hval, Complex.norm_real, Real.norm_eq_abs]
  have hpos : (0 : ℝ) ≤ (1 : ℝ) / (2 : ℝ) ^ (2 * α ^ 2 - 2) *
      Real.exp (Real.pi * (α : ℝ) ^ 2 * (HvdH.betaR s t (ℓ : ℕ)) ^ 2) :=
    mul_nonneg (by positivity) (Real.exp_pos _).le
  rw [abs_of_nonneg hpos]
  have hsplit : (1 : ℝ) / (2 : ℝ) ^ (2 * α ^ 2 - 2) *
      Real.exp (Real.pi * (α : ℝ) ^ 2 * (HvdH.betaR s t (ℓ : ℕ)) ^ 2)
      = Real.exp (Real.pi * (α : ℝ) ^ 2 * (HvdH.betaR s t (ℓ : ℕ)) ^ 2
          - ((2 * α ^ 2 - 2 : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    ring
  rw [hsplit]
  exact exp_bound_seven_eighths α hα _ hβ

/-! ## The target lemma -/

theorem buFixed (p α s t : ℕ) (hα : 2 ≤ α) (z : ℤ × ℤ) (hz : HvdH.inDisc p z) (ℓ : Fin s) :
    (HvdH.inDisc p (Int.tdiv z.1 2, Int.tdiv z.2 2) ∧
      (2 : ℝ) ^ p * ‖HvdH.fxC p (Int.tdiv z.1 2, Int.tdiv z.2 2) - HvdH.fxC p z / 2‖ ≤ 1) ∧
    ‖HvdH.diagD' s t α ℓ ℓ‖ ≤ 7 / 8 := by
  refine ⟨⟨?_, ?_⟩, diagDp_entry_le_seven_eighths s t α hα ℓ⟩
  · -- `(z.1 tdiv 2, z.2 tdiv 2)` is again in the disc `C̃◦`
    have h1 := sq_tdiv_two_le z.1
    have h2 := sq_tdiv_two_le z.2
    have hz' : z.1 ^ 2 + z.2 ^ 2 ≤ (4 : ℤ) ^ p := hz
    show (Int.tdiv z.1 2) ^ 2 + (Int.tdiv z.2 2) ^ 2 ≤ (4 : ℤ) ^ p
    linarith
  · -- the halving error in scaled units
    have hkey : (((2 : ℝ) ^ p : ℝ) : ℂ) *
        (HvdH.fxC p (Int.tdiv z.1 2, Int.tdiv z.2 2) - HvdH.fxC p z / 2)
        = ((Int.tdiv z.1 2 : ℂ) - (z.1 : ℂ) / 2)
          + ((Int.tdiv z.2 2 : ℂ) - (z.2 : ℂ) / 2) * Complex.I := by
      rw [mul_sub, fxC_scale p (Int.tdiv z.1 2, Int.tdiv z.2 2), ← mul_div_assoc,
        fxC_scale p z]
      ring
    have hnorm : (2 : ℝ) ^ p *
          ‖HvdH.fxC p (Int.tdiv z.1 2, Int.tdiv z.2 2) - HvdH.fxC p z / 2‖
        = ‖(((2 : ℝ) ^ p : ℝ) : ℂ) *
          (HvdH.fxC p (Int.tdiv z.1 2, Int.tdiv z.2 2) - HvdH.fxC p z / 2)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hnorm, hkey]
    calc ‖((Int.tdiv z.1 2 : ℂ) - (z.1 : ℂ) / 2)
          + ((Int.tdiv z.2 2 : ℂ) - (z.2 : ℂ) / 2) * Complex.I‖
        ≤ ‖(Int.tdiv z.1 2 : ℂ) - (z.1 : ℂ) / 2‖
          + ‖((Int.tdiv z.2 2 : ℂ) - (z.2 : ℂ) / 2) * Complex.I‖ := norm_add_le _ _
      _ = ‖(Int.tdiv z.1 2 : ℂ) - (z.1 : ℂ) / 2‖
          + ‖(Int.tdiv z.2 2 : ℂ) - (z.2 : ℂ) / 2‖ := by
          rw [norm_mul, Complex.norm_I, mul_one]
      _ ≤ 1 := by
          have h1 := norm_tdiv_half_le z.1
          have h2 := norm_tdiv_half_le z.2
          linarith

end Work.Resample
