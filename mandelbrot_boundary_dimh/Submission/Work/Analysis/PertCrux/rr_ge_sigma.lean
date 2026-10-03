import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Interfaces.Parabolic

/-!
# PERT crux: the covering radius bounds `‖σ‖`

`Work.Pert.tauC σ α w = σ / (1 - exp (-2πi α w))` is the universal cover `ℂ → ℂ ∖ {0, σ}`
of Shishikura (A.1.5), and `Work.Pert.Qp ξ α = 𝒬(ξ, -ξ + 1/α)` is the upper gate of §4.2.
This file proves that if `τ_f` maps the gate `Qp Ξ' α` into the ball of radius `rr`, then
necessarily `‖σ‖ ≤ rr`: the gate contains points on which the denominator
`1 - exp (-2πi α w)` has modulus `< 1`, so `‖σ‖` is no larger than the sup of `‖τ_f‖` there.

The point is produced on a vertical line `w = X + i t`, `X = 1/Re α`: choosing `t` far below
with `(Im α) · t ∈ ℤ` makes `exp (-2πi α w) = exp (2π (Re α · t + Im α · X))` a *positive real*
number `< 1`.  It only remains to check that the gate does contain such a point, which is the
direct computation below (the hypothesis `Re (1/α) > 0` follows from `α ∈ 𝓕₁`).
-/

namespace Work.Analysis.PertCrux

open Complex

/-- For every real `b` and every threshold `T` there is `t ≤ T` with `b * t` an integer.
(If `b = 0` all `t` work; otherwise `t = k / b` for a suitable integer `k`.) -/
lemma exists_mul_int_le (b T : ℝ) : ∃ t : ℝ, t ≤ T ∧ ∃ k : ℤ, b * t = (k : ℝ) := by
  by_cases hb : b = 0
  · exact ⟨T, le_rfl, 0, by simp [hb]⟩
  · rcases lt_or_gt_of_ne hb with hlt | hgt
    · refine ⟨((⌈b * T⌉ : ℤ) : ℝ) / b, ?_, ⌈b * T⌉, ?_⟩
      · rw [div_le_iff_of_neg hlt]
        simpa [mul_comm] using Int.le_ceil (b * T)
      · field_simp
    · refine ⟨((⌊b * T⌋ : ℤ) : ℝ) / b, ?_, ⌊b * T⌋, ?_⟩
      · rw [div_le_iff₀ hgt]
        simpa [mul_comm] using Int.floor_le (b * T)
      · field_simp

/-- The norm of a real number seen in `ℂ`. -/
lemma norm_ofReal_eq_abs (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  rw [← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, Complex.normSq_ofReal, ← sq,
    Real.sqrt_sq_eq_abs]

/-- The exponent identity behind the construction: for `a * X = 1` and `b * t = k ∈ ℤ`,
`-(2πi (a + ib)(X + it))` differs from the real number `2π (a t + b X)` by an integral
multiple of `2πi`. -/
lemma exp_neg_two_pi_I_mul (a b X t : ℝ) (k : ℤ) (hX : a * X = 1) (hk : b * t = (k : ℝ)) :
    -(2 * Real.pi * Complex.I * ((a : ℂ) + (b : ℂ) * Complex.I) * ((X : ℂ) + (t : ℂ) * Complex.I))
      = ((2 * Real.pi * (a * t + b * X) : ℝ) : ℂ)
        + ((k - 1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  have hX' : (a : ℂ) * (X : ℂ) = 1 := by exact_mod_cast hX
  have hk' : (b : ℂ) * (t : ℂ) = (k : ℂ) := by exact_mod_cast hk
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_mul, Complex.ofReal_add, Complex.intCast_re, Complex.intCast_im] <;>
    norm_num <;>
    ring_nf
  · linear_combination (-(2 * Real.pi)) * hX + (2 * Real.pi) * hk

theorem rr_ge_sigma {Ξ' : ℝ} (hΞ' : 1 + 64 * Real.pi ≤ Ξ') {σ α : ℂ}
    (hσ : σ ≠ 0) (hα : α ≠ 0) (hinf : MandelDim.InF1 α)
    (hadm : MandelDim.QAdm (some (Ξ' : ℂ)) (some (-(Ξ' : ℂ) + 1 / α)))
    {rr : ℝ} (h : ∀ z ∈ Work.Pert.Qp Ξ' α, Work.Pert.tauC σ α z ∈ Metric.ball 0 rr) :
    ‖σ‖ ≤ rr := by
  have _ := hadm -- the admissibility of the gate is not needed for this bound
  -- `α ∈ 𝓕₁` gives `Re α > 0`, hence `Re (1/α) > 0`; the gate contains a point far below.
  have ha : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hinf
  have hβre : 0 < (1 / α).re := by
    rw [one_div, Complex.inv_re]
    exact div_pos ha (Complex.normSq_pos.mpr hα)
  have hΞ : 0 ≤ Ξ' := by linarith [Real.pi_pos]
  set X : ℝ := 1 / α.re with hXdef
  have hXpos : 0 < X := by rw [hXdef]; exact div_pos one_pos ha
  have hXa : α.re * X = 1 := by rw [hXdef]; field_simp
  -- all constraints on `t` are of the form `t ≤ …`
  set T : ℝ := min (min (X - Ξ' - 1) ((1 / α).im - (1 / α).re - Ξ' - X - 1))
    (min (-1) (-(α.im * X) / α.re - 1)) with hTdef
  obtain ⟨t, htT, k, hbt⟩ := exists_mul_int_le α.im T
  have ht1 : t ≤ X - Ξ' - 1 := le_trans htT (le_trans (min_le_left _ _) (min_le_left _ _))
  have ht2 : t ≤ (1 / α).im - (1 / α).re - Ξ' - X - 1 :=
    le_trans htT (le_trans (min_le_left _ _) (min_le_right _ _))
  have ht0 : t ≤ -1 := le_trans htT (le_trans (min_le_right _ _) (min_le_left _ _))
  have htρ : t ≤ -(α.im * X) / α.re - 1 :=
    le_trans htT (le_trans (min_le_right _ _) (min_le_right _ _))
  -- the point lies in the gate
  have hzQp : ((X : ℂ) + (t : ℂ) * Complex.I) ∈ Work.Pert.Qp Ξ' α := by
    rw [Work.Pert.Qp, MandelDim.Qreg]
    constructor
    · intro c hc
      obtain rfl : c = (Ξ' : ℂ) := (Option.mem_some_iff.mp hc).symm
      have hre1 : (((X : ℂ) + (t : ℂ) * Complex.I) - (Ξ' : ℂ)).re = X - Ξ' := by simp
      have him1 : (((X : ℂ) + (t : ℂ) * Complex.I) - (Ξ' : ℂ)).im = t := by simp
      rw [hre1, him1, abs_of_neg (by linarith), neg_neg]
      linarith
    · intro c hc
      obtain rfl : c = (-(Ξ' : ℂ) + 1 / α) := (Option.mem_some_iff.mp hc).symm
      have hre1 : (((X : ℂ) + (t : ℂ) * Complex.I) - (-(Ξ' : ℂ) + 1 / α)).re
          = X + Ξ' - (1 / α).re := by
        simp; ring
      have him1 : (((X : ℂ) + (t : ℂ) * Complex.I) - (-(Ξ' : ℂ) + 1 / α)).im
          = t - (1 / α).im := by simp
      rw [hre1, him1, abs_of_neg (by linarith)]
      linarith
  have hτ : ‖Work.Pert.tauC σ α ((X : ℂ) + (t : ℂ) * Complex.I)‖ < rr := by
    have hh := h _ hzQp
    rwa [Metric.mem_ball, dist_zero_right] at hh
  -- the denominator is `1 - ρ` with `0 < ρ < 1`
  have hαc : ((α.re : ℂ) + (α.im : ℂ) * Complex.I) = α := Complex.re_add_im α
  have hid : -(2 * Real.pi * Complex.I * α * ((X : ℂ) + (t : ℂ) * Complex.I))
      = ((2 * Real.pi * (α.re * t + α.im * X) : ℝ) : ℂ)
        + ((k - 1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    have h1 := exp_neg_two_pi_I_mul α.re α.im X t k hXa hbt
    rw [hαc] at h1
    exact h1
  have hExp : Complex.exp (-(2 * Real.pi * Complex.I * α * ((X : ℂ) + (t : ℂ) * Complex.I)))
      = ((Real.exp (2 * Real.pi * (α.re * t + α.im * X)) : ℝ) : ℂ) := by
    rw [hid, Complex.exp_add, Complex.ofReal_exp, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have harg : 2 * Real.pi * (α.re * t + α.im * X) < 0 := by
    have h2 := mul_le_mul_of_nonneg_left htρ (le_of_lt ha)
    have h3 : α.re * (-(α.im * X) / α.re - 1) = -(α.im * X) - α.re := by field_simp
    rw [h3] at h2
    nlinarith [Real.pi_pos]
  have hρ1 : Real.exp (2 * Real.pi * (α.re * t + α.im * X)) < 1 := Real.exp_lt_one_iff.mpr harg
  have hρ0 : 0 < Real.exp (2 * Real.pi * (α.re * t + α.im * X)) := Real.exp_pos _
  have hden : (1 : ℂ) - Complex.exp (-(2 * Real.pi * Complex.I * α * ((X : ℂ) + (t : ℂ) * Complex.I)))
      = ((1 - Real.exp (2 * Real.pi * (α.re * t + α.im * X)) : ℝ) : ℂ) := by
    rw [hExp, ← Complex.ofReal_one, ← Complex.ofReal_sub]
  have hpos : (0 : ℝ) < 1 - Real.exp (2 * Real.pi * (α.re * t + α.im * X)) := by linarith
  -- conclude `‖σ‖ ≤ ‖τ_f w‖ < rr`
  have hnorm : ‖Work.Pert.tauC σ α ((X : ℂ) + (t : ℂ) * Complex.I)‖
      = ‖σ‖ / (1 - Real.exp (2 * Real.pi * (α.re * t + α.im * X))) := by
    rw [Work.Pert.tauC, norm_div, hden, norm_ofReal_eq_abs, abs_of_pos hpos]
  have hle1 : 1 - Real.exp (2 * Real.pi * (α.re * t + α.im * X)) ≤ 1 := by linarith [hρ0]
  have hσeq : ‖σ‖ = ‖Work.Pert.tauC σ α ((X : ℂ) + (t : ℂ) * Complex.I)‖
      * (1 - Real.exp (2 * Real.pi * (α.re * t + α.im * X))) := by
    rw [hnorm]; field_simp
  have hbnd := mul_le_mul_of_nonneg_left hle1
    (norm_nonneg (Work.Pert.tauC σ α ((X : ℂ) + (t : ℂ) * Complex.I)))
  linarith

end Work.Analysis.PertCrux
