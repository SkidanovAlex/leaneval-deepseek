import Mathlib
import Submission.Work.CNum.Basic

/-! # CNum: the cosine form of `Hfun` and its term calculus

`Hfun φ = log 192 + Σ' n, 24 log ‖1 + (3/4)^{n+1} e^{i(n+1)φ}‖`.  Writing
`u = r^m` (`r = 3/4`) and `θ = m φ`, the `m`-th summand of the shifted sum is

`cterm m φ = 12 log (1 + 2 u cos θ + u²)`,   `eterm m φ = 1 + 2 u cos θ + u²`,

and its first two derivatives are `ctermDeriv` and `ctermDeriv2` below.  These notation
lemmas are the interface for the certified numerical bound on `Hfun`. -/

namespace Work.CNum

open Complex Metric Filter Topology
open scoped BigOperators

/-- `r = 3/4`, the radius of the circle `|z| = 3/4` on which `Hfun` is evaluated. -/
noncomputable def r34 : ℝ := 3 / 4

lemma r34_pos : 0 < r34 := by norm_num [r34]
lemma r34_lt_one : r34 < 1 := by norm_num [r34]
lemma r34_nonneg : 0 ≤ r34 := le_of_lt r34_pos
lemma r34_pow_pos (m : ℕ) : 0 < r34 ^ m := pow_pos r34_pos m

lemma r34_pow_lt_one {m : ℕ} (hm : 1 ≤ m) : r34 ^ m < 1 :=
  pow_lt_one₀ r34_nonneg r34_lt_one (by omega)

lemma one_sub_r34 : 1 - r34 = 1 / 4 := by norm_num [r34]

/-- `‖1 + (c : ℂ) e^{iθ}‖² = 1 + 2 c cos θ + c²`. -/
lemma normSq_one_add_exp (c θ : ℝ) :
    Complex.normSq (1 + (c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      1 + 2 * c * Real.cos θ + c ^ 2 := by
  rw [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  nlinarith [Real.cos_sq_add_sin_sq θ]

/-- `24 log ‖1 + c e^{iθ}‖ = 12 log (1 + 2c cos θ + c²)` for `0 ≤ c < 1`. -/
lemma log_norm_one_add_exp (c θ : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    24 * Real.log ‖1 + (c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ =
      12 * Real.log (1 + 2 * c * Real.cos θ + c ^ 2) := by
  have hXpos : 0 < 1 + 2 * c * Real.cos θ + c ^ 2 := by
    have h1 := Real.neg_one_le_cos θ
    nlinarith [sq_nonneg (1 - c), hc1, h1]
  rw [Complex.norm_def, normSq_one_add_exp, Real.log_sqrt (le_of_lt hXpos)]
  ring

/-- The "inside" `1 + 2 r^m cos(mφ) + (r^m)²` of the `m`-th summand. -/
noncomputable def eterm (m : ℕ) (φ : ℝ) : ℝ :=
  1 + 2 * r34 ^ m * Real.cos ((m : ℝ) * φ) + (r34 ^ m) ^ 2

/-- `12 log (1 + 2 r^m cos(mφ) + (r^m)²)`. -/
noncomputable def cterm (m : ℕ) (φ : ℝ) : ℝ := 12 * Real.log (eterm m φ)

/-- The derivative of `cterm m`:
`-24 m r^m sin(mφ) / (1 + 2 r^m cos(mφ) + (r^m)²)`. -/
noncomputable def ctermDeriv (m : ℕ) (φ : ℝ) : ℝ :=
  -24 * (m : ℝ) * r34 ^ m * Real.sin ((m : ℝ) * φ) / eterm m φ

/-- The second derivative of `cterm m`. -/
noncomputable def ctermDeriv2 (m : ℕ) (φ : ℝ) : ℝ :=
  -24 * (m : ℝ) ^ 2 * r34 ^ m *
      (Real.cos ((m : ℝ) * φ) * (1 + (r34 ^ m) ^ 2) + 2 * r34 ^ m) / (eterm m φ) ^ 2

/-- The `n = m+1` summand of `Hfun` in cosine form, as a function of `φ`. -/
theorem Hfun_term (n : ℕ) (φ : ℝ) :
    24 * Real.log
        ‖1 + ((3 / 4 : ℝ) : ℂ) ^ (n + 1) * Complex.exp (Complex.I * (n + 1 : ℝ) * φ)‖ =
      cterm (n + 1) φ := by
  rw [cterm, eterm, show r34 = (3 / 4 : ℝ) from rfl]
  have hc : (0 : ℝ) ≤ (3 / 4) ^ (n + 1) := by positivity
  have hclt : (3 / 4 : ℝ) ^ (n + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  rw [← Complex.ofReal_pow (3 / 4) (n + 1)]
  rw [show Complex.I * ((n + 1 : ℝ) : ℂ) * (φ : ℂ) =
      ((((n + 1 : ℝ) * φ : ℝ)) : ℂ) * Complex.I from by push_cast; ring]
  rw [log_norm_one_add_exp _ _ hc hclt]
  rw [show ((n + 1 : ℕ) : ℝ) = (↑n + 1) from by push_cast; ring]

/-- `∑' m, cterm (m+1) φ`, so that `Hfun φ = log 192 + Kfun φ`. -/
noncomputable def Kfun (φ : ℝ) : ℝ := ∑' m : ℕ, cterm (m + 1) φ

/-- `∑' m, ctermDeriv (m+1) φ`, the derivative of `Kfun`. -/
noncomputable def KfunDeriv (φ : ℝ) : ℝ := ∑' m : ℕ, ctermDeriv (m + 1) φ

/-- `∑' m, ctermDeriv2 (m+1) φ`, the second derivative of `Kfun`. -/
noncomputable def KfunDeriv2 (φ : ℝ) : ℝ := ∑' m : ℕ, ctermDeriv2 (m + 1) φ

/-- `Hfun` in cosine form. -/
theorem Hfun_eq (φ : ℝ) : Hfun φ = Real.log 192 + Kfun φ := by
  unfold Hfun Kfun
  rw [tsum_congr (fun n => Hfun_term n φ)]

end Work.CNum
