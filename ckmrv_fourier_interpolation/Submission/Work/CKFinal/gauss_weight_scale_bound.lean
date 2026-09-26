import Mathlib
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Asymptotics.abs_pow_mul_exp_le

/-!
# A Gaussian weight bound in the scale `S τ = 1 + (im τ)⁻¹ + |τ|`

We prove that for every pair of exponents `k M : ℕ` there are constants `C, N ≥ 0` with

  `|r|^k (1+|r|)^M exp(-π (im τ) r²) ≤ C · (S τ)^N`   for all `τ ∈ ℍ`, `r ∈ ℝ`,

where `S τ = 1 + (im τ)⁻¹ + |τ|` is the scale of `Work.Kernels.ModerateGrowth`.

The point is that the `r`-dependence (a polynomial factor times a Gaussian, whose height
blows up as `im τ → 0⁺`) is absorbed by a *fixed* power of `S τ`, because
`(im τ)⁻¹ ≤ S τ`.

## Strategy

Write the polynomial factor as `(1+|r|)^M ≤ 2^M (1 + |r|^M)`, so that

  `|r|^k (1+|r|)^M e^{-π t r²} ≤ 2^M ( |r|^k e^{-π t r²} + |r|^{k+M} e^{-π t r²} )`.

Each summand is bounded by the paper's elementary Gaussian maximum
(`Work.Asymptotics.abs_pow_mul_exp_le`), which gives `|r|^n e^{-π t r²} ≤
((n)/(2πet))^{n/2} = ((n)/(2πe))^{n/2} · t^{-n/2}`, and `t^{-n/2} ≤ (S τ)^{n/2}`
since `t⁻¹ = (im τ)⁻¹ ≤ S τ` and `S τ ≥ 1`.  Taking `N = (k+M)/2` finishes.

## Main results

* `Work.CKFinal.one_add_pow_le` : `(1+x)^M ≤ 2^M (1+x^M)` for `x ≥ 0`.
* `Work.CKFinal.gauss_pow_scale_le` : `|r|^n e^{-π (im τ) r²} ≤ A_n (S τ)^{n/2}`.
* `Work.CKFinal.gauss_weight_scale_bound` : the target bound.
-/

noncomputable section

open UpperHalfPlane

namespace Work.CKFinal

/-- `(1 + x)^M ≤ 2^M (1 + x^M)` for `x ≥ 0`: since `1 + x ≤ 2 max 1 x`, raising to the
`M`-th power and using `max 1 x ^ M ≤ 1 + x^M`. -/
lemma one_add_pow_le (M : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ M ≤ (2:ℝ) ^ M * (1 + x ^ M) := by
  have h : (1 + x : ℝ) ≤ 2 * max 1 x := by
    rcases le_total 1 x with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h' : (1 + x) ^ M ≤ (2 * max 1 x) ^ M :=
    pow_le_pow_left₀ (by positivity) h M
  have hmax : (max 1 x) ^ M ≤ 1 + x ^ M := by
    rcases le_total 1 x with hh | hh
    · rw [max_eq_right hh]
      exact le_add_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
    · rw [max_eq_left hh, one_pow]
      exact le_add_of_nonneg_right (pow_nonneg hx M)
  calc (1 + x) ^ M ≤ (2 * max 1 x) ^ M := h'
    _ = (2:ℝ) ^ M * (max 1 x) ^ M := by rw [mul_pow]
    _ ≤ (2:ℝ) ^ M * (1 + x ^ M) :=
        mul_le_mul_of_nonneg_left hmax (pow_nonneg (by norm_num) M)

/-- The Gaussian maximum `|r|^n e^{-π (im τ) r²} ≤ A_n (S τ)^{n/2}`, where
`A_n = ((n)/(2πe))^{n/2}`.  This is `Work.Asymptotics.abs_pow_mul_exp_le` together with
`(im τ)⁻¹ ≤ S τ`. -/
lemma gauss_pow_scale_le (n : ℕ) (τ : UpperHalfPlane) (r : ℝ) :
    |r| ^ n * Real.exp (-(Real.pi * τ.im * r ^ 2))
      ≤ ((n:ℝ) / (2 * Real.pi * Real.exp 1)) ^ ((n:ℝ) / 2)
        * (Work.Kernels.scale τ) ^ ((n:ℝ) / 2) := by
  have ht : 0 < τ.im := τ.im_pos
  have h1 := Work.Asymptotics.abs_pow_mul_exp_le n ht r
  rw [show -(Real.pi * r ^ 2 * τ.im) = -(Real.pi * τ.im * r ^ 2) by ring] at h1
  refine le_trans h1 ?_
  have hx : (0:ℝ) ≤ (n:ℝ) / (2 * Real.pi * Real.exp 1) := by positivity
  have hy : (0:ℝ) ≤ (τ.im)⁻¹ := inv_nonneg.mpr ht.le
  have hsplit : (n:ℝ) / (2 * Real.pi * Real.exp 1 * τ.im)
      = ((n:ℝ) / (2 * Real.pi * Real.exp 1)) * (τ.im)⁻¹ := by
    field_simp
  rw [hsplit, Real.mul_rpow hx hy]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hy (Work.Kernels.inv_im_le_scale τ) (by positivity))
    (Real.rpow_nonneg hx _)

theorem gauss_weight_scale_bound (k M : ℕ) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      |r| ^ k * (1 + |r|) ^ M * Real.exp (-(Real.pi * τ.im * r ^ 2))
        ≤ C * (Work.Kernels.scale τ) ^ N := by
  refine ⟨(2:ℝ)^M * ((((k:ℝ) / (2 * Real.pi * Real.exp 1)) ^ ((k:ℝ) / 2))
          + ((((k + M : ℕ):ℝ) / (2 * Real.pi * Real.exp 1)) ^ (((k + M : ℕ):ℝ) / 2))),
          (((k + M : ℕ):ℝ) / 2), ?_, ?_, ?_⟩
  · -- `C ≥ 0`
    refine mul_nonneg (pow_nonneg (by norm_num) M) (add_nonneg ?_ ?_)
    · exact Real.rpow_nonneg (by positivity) _
    · exact Real.rpow_nonneg (by positivity) _
  · -- `N ≥ 0`
    positivity
  · intro τ r
    set A1 : ℝ := ((k:ℝ) / (2 * Real.pi * Real.exp 1)) ^ ((k:ℝ) / 2) with hA1
    set A2 : ℝ := (((k + M : ℕ):ℝ) / (2 * Real.pi * Real.exp 1)) ^ (((k + M : ℕ):ℝ) / 2)
      with hA2
    set N : ℝ := (((k + M : ℕ):ℝ) / 2) with hN
    have hscale : (1:ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hA1nn : 0 ≤ A1 := by rw [hA1]; exact Real.rpow_nonneg (by positivity) _
    have hkN : (k:ℝ)/2 ≤ N := by
      rw [hN]
      have h : (k:ℝ) ≤ ((k + M : ℕ):ℝ) := by exact_mod_cast Nat.le_add_right k M
      linarith
    have step_k : |r| ^ k * Real.exp (-(Real.pi * τ.im * r ^ 2))
        ≤ A1 * (Work.Kernels.scale τ) ^ N := by
      rw [hA1]
      refine le_trans (gauss_pow_scale_le k τ r) ?_
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hscale hkN) (Real.rpow_nonneg (by positivity) _)
    have step_kM : |r| ^ (k + M) * Real.exp (-(Real.pi * τ.im * r ^ 2))
        ≤ A2 * (Work.Kernels.scale τ) ^ N := by
      rw [hA2, hN]
      exact gauss_pow_scale_le (k + M) τ r
    calc |r| ^ k * (1 + |r|) ^ M * Real.exp (-(Real.pi * τ.im * r ^ 2))
        ≤ |r| ^ k * ((2:ℝ)^M * (1 + |r| ^ M)) * Real.exp (-(Real.pi * τ.im * r ^ 2)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (one_add_pow_le M (abs_nonneg r))
              (pow_nonneg (abs_nonneg r) k))
            (Real.exp_nonneg _)
      _ = (2:ℝ)^M * (|r| ^ k * Real.exp (-(Real.pi * τ.im * r ^ 2))
            + |r| ^ (k + M) * Real.exp (-(Real.pi * τ.im * r ^ 2))) := by
          rw [pow_add]; ring
      _ ≤ (2:ℝ)^M * (A1 * (Work.Kernels.scale τ) ^ N + A2 * (Work.Kernels.scale τ) ^ N) :=
          mul_le_mul_of_nonneg_left (add_le_add step_k step_kM) (pow_nonneg (by norm_num) M)
      _ = ((2:ℝ)^M * (A1 + A2)) * (Work.Kernels.scale τ) ^ N := by ring

end Work.CKFinal
