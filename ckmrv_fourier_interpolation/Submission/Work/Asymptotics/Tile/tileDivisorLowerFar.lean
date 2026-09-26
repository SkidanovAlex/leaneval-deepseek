/-
# The tile divisor lower bound in the *near* regime `1 ≤ Im z ≤ Im (S • w) - 1`

For `w` in the cusp-`0` tile `E = KEpsilon`, `n = ±1` and `z = i t` with
`1 ≤ t ≤ Im (S • w) - 1`, the divisor `Δ(z) (j(n +ᵥ w) - j(z))` of the CKMRV kernel is bounded
below by an absolute constant.

Put `τ := S • w`; since `w ∈ E` we have `Im τ ≥ 2`, and `j(n +ᵥ w) = j(w) = j τ` by the
`T`-invariance and `S`-invariance of `j`.  Using `Δ · j = E₄³`,

  `Δ(it)(j τ - j(it)) = Δ(it) j τ - E₄(it)³`,

and the two summands are estimated separately:

* `‖Δ(it) j τ‖ ≥ (1/2) e^{-2πt} · (1/16) e^{2π Im τ} = (1/32) e^{2π (Im τ - t)} ≥ (1/32) e^{2π}`,
  from the sharp imaginary-axis lower bound `‖Δ(it)‖ ≥ (1/2) e^{-2πt}`
  (`DeltaFun_imagAxis_lower_sharp`) and the funnel lower bound `‖j τ‖ ≥ (1/16) e^{2π Im τ}`
  (from `‖E₄ τ‖ ≥ 1/2` at height `≥ 2` and `‖Δ τ‖ ≤ 2 e^{-2π Im τ}`, `DeltaFun_upper_sharp`);
* `‖E₄(it)³‖ ≤ (3/2)³ = 27/8` for `Im = t ≥ 1` (`E4Fun_upper_half`).

Since `Im τ - t ≥ 1`, this gives `‖Δ(it)(j τ - j(it))‖ ≥ (1/32)·216 - 27/8 ≥ 1/4`.
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.DeltaFun_upper_sharp
import Submission.Work.Asymptotics.DeltaFun_imagAxis_lower_sharp
import Submission.Work.Asymptotics.E4Fun_upper_half
import Submission.Work.Asymptotics.E4Fun_sub_one_explicit
import Submission.Work.Asymptotics.jInvariantFun_imagAxis_atTop

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups UpperHalfPlane

noncomputable section

/-! ## Numerical inputs -/

/-- `216 ≤ e^{2π}`. -/
private lemma exp_two_pi_ge_216 : (216 : ℝ) ≤ Real.exp (2 * Real.pi) := by
  have h6 : (6 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h2 : (2.7 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 := pow_le_pow_left₀ (by norm_num) h1 6
  have h3 : Real.exp 6 = (Real.exp 1) ^ 6 := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  have h4 : (216 : ℝ) ≤ Real.exp 6 := by
    rw [h3]
    linarith [(by norm_num : (216 : ℝ) ≤ (2.7 : ℝ) ^ 6)]
  exact le_trans h4 (Real.exp_le_exp.mpr h6)

/-- `e^{-2π Im τ} ≤ 1/40000` for `Im τ ≥ 2`. -/
private lemma exp_neg_two_pi_im_le (τ : ℍ) (hτ : 2 ≤ τ.im) :
    Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 / 40000 := by
  have h12 : (12 : ℝ) ≤ 2 * Real.pi * τ.im := by nlinarith [Real.pi_gt_three, hτ]
  have h40000 : (40000 : ℝ) ≤ Real.exp (2 * Real.pi * τ.im) := by
    have h2 : Real.exp 12 ≤ Real.exp (2 * Real.pi * τ.im) := Real.exp_le_exp.mpr h12
    have h3 : (40000 : ℝ) ≤ Real.exp 12 := by
      have h4 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h5 : (2.7 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 := pow_le_pow_left₀ (by norm_num) h4 12
      have h6 : Real.exp 12 = (Real.exp 1) ^ 12 := by
        rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
      rw [h6]
      linarith [(by norm_num : (40000 : ℝ) ≤ (2.7 : ℝ) ^ 12)]
    linarith
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) h40000

/-! ## The two funnel estimates at height `≥ 2` -/

/-- `‖E₄ τ - 1‖ ≤ 1/2` for `Im τ ≥ 2`. -/
private lemma E4_sub_one_le_half {τ : ℍ} (hτ : 2 ≤ τ.im) :
    ‖Work.Kernels.E4Fun τ - 1‖ ≤ 1 / 2 := by
  have h := Work.Asymptotics.E4Fun_sub_one_explicit (le_trans (by norm_num) hτ)
  rw [Work.Asymptotics.norm_qParamFun] at h
  have h4 := exp_neg_two_pi_im_le τ hτ
  have h6 : (20000 : ℝ) * Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ 20000)
    linarith
  linarith

/-- `‖j τ‖ ≥ (1/16) e^{2π Im τ}` for `Im τ ≥ 2`. -/
private lemma jInvariant_lower_funnel {τ : ℍ} (hτ : 2 ≤ τ.im) :
    (1 / 16 : ℝ) * Real.exp (2 * Real.pi * τ.im) ≤ ‖Work.Kernels.jInvariantFun τ‖ := by
  have hτ1 : (1 : ℝ) ≤ τ.im := le_trans (by norm_num) hτ
  have hE4 : (1 / 2 : ℝ) ≤ ‖Work.Kernels.E4Fun τ‖ := by
    have h := E4_sub_one_le_half hτ
    have h11 : (1 : ℝ) - ‖(1 : ℂ) - Work.Kernels.E4Fun τ‖ ≤ ‖Work.Kernels.E4Fun τ‖ := by
      have hh := abs_norm_sub_norm_le (1 : ℂ) ((1 : ℂ) - Work.Kernels.E4Fun τ)
      rw [show (1 : ℂ) - ((1 : ℂ) - Work.Kernels.E4Fun τ) = Work.Kernels.E4Fun τ by ring,
        norm_one] at hh
      exact le_trans (le_abs_self _) hh
    have h12 : ‖(1 : ℂ) - Work.Kernels.E4Fun τ‖ = ‖Work.Kernels.E4Fun τ - 1‖ := by
      rw [show (1 : ℂ) - Work.Kernels.E4Fun τ = -(Work.Kernels.E4Fun τ - 1) by ring, norm_neg]
    linarith [h11, h12 ▸ h]
  have hD : ‖Work.Kernels.DeltaFun τ‖ ≤ 2 * Real.exp (-(2 * Real.pi * τ.im)) :=
    Work.Asymptotics.DeltaFun_upper_sharp τ hτ1
  have hDpos : 0 < ‖Work.Kernels.DeltaFun τ‖ :=
    norm_pos_iff.mpr (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
  have hj : ‖Work.Kernels.jInvariantFun τ‖
      = ‖Work.Kernels.E4Fun τ‖ ^ 3 / ‖Work.Kernels.DeltaFun τ‖ := by
    simp only [Work.Kernels.jInvariantFun, norm_div, norm_pow]
  rw [hj]
  have hnum : (1 / 2 : ℝ) ^ 3 ≤ ‖Work.Kernels.E4Fun τ‖ ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hE4 3
  have step1 : (1 / 2 : ℝ) ^ 3 / ‖Work.Kernels.DeltaFun τ‖
      ≤ ‖Work.Kernels.E4Fun τ‖ ^ 3 / ‖Work.Kernels.DeltaFun τ‖ :=
    div_le_div_of_nonneg_right hnum hDpos.le
  have hdenpos : 0 < 2 * Real.exp (-(2 * Real.pi * τ.im)) := by positivity
  have step2 : (1 / 2 : ℝ) ^ 3 / (2 * Real.exp (-(2 * Real.pi * τ.im)))
      ≤ (1 / 2 : ℝ) ^ 3 / ‖Work.Kernels.DeltaFun τ‖ :=
    div_le_div_of_nonneg_left (by norm_num) hDpos hD
  have heq : (1 / 16 : ℝ) * Real.exp (2 * Real.pi * τ.im)
      = (1 / 2 : ℝ) ^ 3 / (2 * Real.exp (-(2 * Real.pi * τ.im))) := by
    rw [Real.exp_neg]
    field_simp
    ring
  rw [heq]
  linarith [step1, step2]

/-- `j` is invariant under translation by `±1`. -/
private lemma jInvariant_vadd_int (n : ℤ) (hn : n = 1 ∨ n = -1) (w : ℍ) :
    Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) = Work.Kernels.jInvariantFun w := by
  rcases hn with h | h
  · rw [h, Int.cast_one]; exact Work.Kernels.KernelFacts.jInvariantFun_vadd_one w
  · rw [h, Int.cast_neg, Int.cast_one]
    have h1 := Work.Kernels.KernelFacts.jInvariantFun_vadd_one ((-1 : ℝ) +ᵥ w)
    have h2 : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ w) = w := by rw [← add_vadd]; norm_num
    rw [h2] at h1
    exact h1.symm

/-! ## The main theorem -/

theorem tileDivisorLowerFar :
    ∃ c : ℝ, 0 < c ∧ ∀ (w : UpperHalfPlane) (n : ℤ) (z : UpperHalfPlane) (t : ℝ),
      (n = 1 ∨ n = -1) → w ∈ Work.Asymptotics.KEpsilon →
      (z : ℂ) = (t : ℂ) * Complex.I → 1 ≤ t → t ≤ (ModularGroup.S • w).im - 1 →
      c ≤ ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w)
            - Work.Kernels.jInvariantFun z)‖ := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro w n z t hn hw hz ht1 htle
  have ht : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  set τ : UpperHalfPlane := ModularGroup.S • w with hτdef
  have hτ2 : 2 ≤ τ.im := by
    rw [hτdef]
    exact (Work.Asymptotics.S_smul_mem_funnel hw).2
  -- the `j`-value at `n +ᵥ w` is the one at `τ = S • w`
  have hjn : Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) = Work.Kernels.jInvariantFun τ := by
    rw [jInvariant_vadd_int n hn w, hτdef]
    exact (Work.Kernels.KernelFacts.jInvariantFun_S_smul w).symm
  -- identify `z` with the point `i t`
  have hzeq : z = Work.Kernels.imagAxis t ht := UpperHalfPlane.ext (by rw [hz]; rfl)
  rw [hjn, hzeq]
  -- the two summands of `Δ(i t) j τ - E₄(i t)³`
  have hΔl : (1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * t))
      ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ :=
    Work.Asymptotics.DeltaFun_imagAxis_lower_sharp t ht ht1
  have hjτ : (1 / 16 : ℝ) * Real.exp (2 * Real.pi * τ.im)
      ≤ ‖Work.Kernels.jInvariantFun τ‖ := jInvariant_lower_funnel hτ2
  have hE4z : ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖ ≤ 3 / 2 := by
    refine Work.Asymptotics.E4Fun_upper_half _ ?_
    rw [show (Work.Kernels.imagAxis t ht).im = t by simp [Work.Kernels.imagAxis]]
    exact ht1
  have hE4z3 : ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht) ^ 3‖ ≤ 27 / 8 := by
    rw [norm_pow]
    calc ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖ ^ 3 ≤ (3 / 2 : ℝ) ^ 3 :=
          pow_le_pow_left₀ (norm_nonneg _) hE4z 3
      _ = 27 / 8 := by norm_num
  -- the product `Δ(i t) j τ` dominates `e^{2π(Im τ - t)}`
  have hprod : (1 / 32 : ℝ) * Real.exp (2 * Real.pi * τ.im) * Real.exp (-(2 * Real.pi * t))
      ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)
          * Work.Kernels.jInvariantFun τ‖ := by
    rw [norm_mul]
    have hstep : (1 / 32 : ℝ) * Real.exp (2 * Real.pi * τ.im) * Real.exp (-(2 * Real.pi * t))
        = (1 / 2 * Real.exp (-(2 * Real.pi * t)))
          * (1 / 16 * Real.exp (2 * Real.pi * τ.im)) := by ring
    rw [hstep]
    exact mul_le_mul hΔl hjτ (by positivity) (norm_nonneg _)
  have hexpmono : Real.exp (2 * Real.pi)
      ≤ Real.exp (2 * Real.pi * τ.im) * Real.exp (-(2 * Real.pi * t)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h1 : (1 : ℝ) ≤ τ.im - t := by linarith
    nlinarith [Real.pi_pos, h1]
  have hlow : (1 / 32 : ℝ) * Real.exp (2 * Real.pi)
      ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)
          * Work.Kernels.jInvariantFun τ‖ := by
    have hmul := mul_le_mul_of_nonneg_left hexpmono (by norm_num : (0 : ℝ) ≤ 1 / 32)
    have hrew : (1 / 32 : ℝ) * (Real.exp (2 * Real.pi * τ.im) * Real.exp (-(2 * Real.pi * t)))
        = (1 / 32 : ℝ) * Real.exp (2 * Real.pi * τ.im) * Real.exp (-(2 * Real.pi * t)) := by
      ring
    rw [hrew] at hmul
    linarith [hmul, hprod]
  -- conclude with the reverse triangle inequality
  have hkey : ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))‖
      = ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) * Work.Kernels.jInvariantFun τ
          - Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht) ^ 3‖ := by
    rw [mul_sub, Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun]
  rw [hkey]
  have h1 : ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) * Work.Kernels.jInvariantFun τ‖
        - ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht) ^ 3‖
      ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) * Work.Kernels.jInvariantFun τ
          - Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht) ^ 3‖ :=
    le_trans (le_abs_self _)
      (abs_norm_sub_norm_le _ _)
  have hnum : (1 / 4 : ℝ) ≤ (1 / 32) * Real.exp (2 * Real.pi) - 27 / 8 := by
    nlinarith [exp_two_pi_ge_216]
  linarith [h1, hE4z3, hlow, hnum]

end

end Work.Asymptotics.Tile
