import Mathlib
import Submission.Work.Modular.ThetaFuncs

/-!
# The value of `θ₂` at the cusp `i∞`

The Jacobi theta function `θ₂(τ) = ∑_{n ∈ ℤ} exp (π i τ (n + 1/2)²)` vanishes at the
cusp `i∞`.  We prove this by a direct estimate of the defining series: for `Im τ ≥ 1`
every summand is bounded by `exp (-π Im τ / 4) · exp (π/2) · exp (-π n² / 2)`, whose
sum is a fixed constant.  Hence

`‖θ₂(τ)‖ ≤ C · exp (-π Im τ / 4) → 0` as `Im τ → ∞`.

This is the analytic input identifying the `θ₂`-coordinate of the modular
transformation of the theta functions at the cusp (used together with the
`S`-transformation `theta2_S_smul`).
-/

open Filter
open scoped Topology UpperHalfPlane

namespace Work.Modular

/-- The constant multiplying the exponential decay of `θ₂`: the sum of the dominating
series `∑_n exp (π/2) exp (-π n² / 2)`. -/
noncomputable def theta2BoundConst : ℝ :=
  Real.exp (Real.pi / 2) * ∑' n : ℤ, Real.exp (-Real.pi * (n : ℝ) ^ 2 / 2)

/-- The dominating series `∑_n exp (-π n² / 2)` is summable (it is a theta series). -/
lemma summable_theta2_bound_series :
    Summable (fun n : ℤ => Real.exp (-Real.pi * (n : ℝ) ^ 2 / 2)) := by
  have h := summable_pow_mul_jacobiTheta₂_term_bound (0 : ℝ) (show (0 : ℝ) < 1 / 2 by norm_num) 0
  refine h.congr (fun n => ?_)
  simp only [pow_zero, one_mul, mul_zero]
  congr 1
  ring

/-- For every integer `n`, `n (n + 1) ≥ 0`. -/
lemma theta2_int_mul_succ_nonneg (n : ℤ) : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) := by
  rcases lt_or_ge (0 : ℤ) n with hn | hn
  · have h : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_of_lt hn
    exact mul_nonneg h (by linarith)
  · rcases eq_or_lt_of_le hn with h | h
    · subst h; norm_num
    · have hn1 : n ≤ -1 := by omega
      have hn1' : (n : ℝ) ≤ -1 := by exact_mod_cast hn1
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)

/-- The norm of the `n`-th summand of `theta2_eq_tsum`. -/
lemma theta2_term_norm (τ : ℍ) (n : ℤ) :
    ‖Complex.exp ((Real.pi : ℂ) * Complex.I * (τ : ℂ) * ((n : ℂ) + 1 / 2) ^ 2)‖
      = Real.exp (-Real.pi * (τ : ℂ).im * ((n : ℝ) + 1 / 2) ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  rw [show (Real.pi : ℂ) * Complex.I * (τ : ℂ) * ((n : ℂ) + 1 / 2) ^ 2
      = ((((Real.pi * ((n : ℝ) + 1 / 2) ^ 2 : ℝ))) : ℂ) * (Complex.I * (τ : ℂ)) by
        push_cast; ring]
  rw [Complex.re_ofReal_mul, Complex.I_mul_re]
  ring

/-- Pointwise decay estimate for the `n`-th summand of `θ₂`: for `Im τ ≥ 1` it is
bounded by `exp (-π Im τ / 4)` times a summable, `τ`-independent term. -/
lemma theta2_term_decay (τ : ℍ) (hy : 1 ≤ (τ : ℂ).im) (n : ℤ) :
    Real.exp (-Real.pi * (τ : ℂ).im * ((n : ℝ) + 1 / 2) ^ 2)
      ≤ Real.exp (-Real.pi * (τ : ℂ).im / 4) *
          (Real.exp (Real.pi / 2) * Real.exp (-Real.pi * (n : ℝ) ^ 2 / 2)) := by
  rw [show Real.exp (-Real.pi * (τ : ℂ).im * ((n : ℝ) + 1 / 2) ^ 2)
      = Real.exp (-Real.pi * (τ : ℂ).im / 4) *
          Real.exp (-Real.pi * (τ : ℂ).im * ((n : ℝ) * ((n : ℝ) + 1))) by
    rw [← Real.exp_add]; congr 1; ring]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h0 : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) := theta2_int_mul_succ_nonneg n
  have h1 : (n : ℝ) ^ 2 / 2 - 1 / 2 ≤ (n : ℝ) * ((n : ℝ) + 1) := by
    nlinarith [sq_nonneg ((n : ℝ) + 1)]
  have h2 : (n : ℝ) * ((n : ℝ) + 1) ≤ (τ : ℂ).im * ((n : ℝ) * ((n : ℝ) + 1)) :=
    le_mul_of_one_le_left h0 hy
  have hchain : (n : ℝ) ^ 2 / 2 - 1 / 2 ≤ (τ : ℂ).im * ((n : ℝ) * ((n : ℝ) + 1)) :=
    le_trans h1 h2
  have h4 := mul_le_mul_of_nonneg_left hchain Real.pi_pos.le
  nlinarith [h4]

/-- The series of norms of the summands of `θ₂` is summable for `Im τ ≥ 1`. -/
lemma summable_theta2_norm_terms (τ : ℍ) (hy : 1 ≤ (τ : ℂ).im) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * (τ : ℂ).im * ((n : ℝ) + 1 / 2) ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun n => Real.exp_nonneg _)
    (fun n => theta2_term_decay τ hy n) ?_
  exact (summable_theta2_bound_series.mul_left _).mul_left _

/-- The main estimate: for `Im τ ≥ 1`, `‖θ₂(τ)‖` is bounded by `exp (-π Im τ / 4)`
times a constant. -/
lemma norm_theta2_le_exp (τ : ℍ) (hy : 1 ≤ (τ : ℂ).im) :
    ‖theta2 τ‖ ≤ Real.exp (-Real.pi * (τ : ℂ).im / 4) * theta2BoundConst := by
  rw [theta2_eq_tsum]
  have hs : Summable (fun n : ℤ =>
      ‖Complex.exp ((Real.pi : ℂ) * Complex.I * (τ : ℂ) * ((n : ℂ) + 1 / 2) ^ 2)‖) :=
    (summable_theta2_norm_terms τ hy).congr (fun n => (theta2_term_norm τ n).symm)
  calc ‖∑' n : ℤ, Complex.exp ((Real.pi : ℂ) * Complex.I * (τ : ℂ) * ((n : ℂ) + 1 / 2) ^ 2)‖
      ≤ ∑' n : ℤ, ‖Complex.exp ((Real.pi : ℂ) * Complex.I * (τ : ℂ) * ((n : ℂ) + 1 / 2) ^ 2)‖ :=
        norm_tsum_le_tsum_norm hs
    _ = ∑' n : ℤ, Real.exp (-Real.pi * (τ : ℂ).im * ((n : ℝ) + 1 / 2) ^ 2) :=
        tsum_congr (fun n => theta2_term_norm τ n)
    _ ≤ ∑' n : ℤ, Real.exp (-Real.pi * (τ : ℂ).im / 4) *
          (Real.exp (Real.pi / 2) * Real.exp (-Real.pi * (n : ℝ) ^ 2 / 2)) :=
        Summable.tsum_le_tsum (fun n => theta2_term_decay τ hy n)
          (summable_theta2_norm_terms τ hy)
          ((summable_theta2_bound_series.mul_left _).mul_left _)
    _ = Real.exp (-Real.pi * (τ : ℂ).im / 4) * theta2BoundConst := by
        rw [tsum_mul_left, tsum_mul_left]
        unfold theta2BoundConst
        rfl

/-- `θ₂(τ) = ∑_{n ∈ ℤ} exp (π i τ (n + 1/2)²)` vanishes at the cusp `i∞`. -/
theorem theta2_at_cusp :
    Filter.Tendsto Work.Modular.theta2 UpperHalfPlane.atImInfty (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hev : ∀ᶠ τ : ℍ in UpperHalfPlane.atImInfty, (1 : ℝ) ≤ (τ : ℂ).im := by
    rw [Filter.eventually_iff, UpperHalfPlane.atImInfty_mem]
    exact ⟨1, fun z hz => by simpa only [Set.mem_ofPred_eq, UpperHalfPlane.coe_im] using hz⟩
  have him : Tendsto (fun τ : ℍ => (τ : ℂ).im) UpperHalfPlane.atImInfty atTop := by
    simpa only [UpperHalfPlane.atImInfty, UpperHalfPlane.coe_im] using
      tendsto_comap (f := UpperHalfPlane.im) (x := atTop)
  have hlin : Tendsto (fun τ : ℍ => Real.pi / 4 * (τ : ℂ).im) UpperHalfPlane.atImInfty atTop :=
    him.const_mul_atTop (by positivity)
  have hexp : Tendsto (fun τ : ℍ => Real.exp (-(Real.pi / 4 * (τ : ℂ).im)))
      UpperHalfPlane.atImInfty (𝓝 0) :=
    (Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr hlin))
  have hconv : (fun τ : ℍ => Real.exp (-(Real.pi / 4 * (τ : ℂ).im)))
      = (fun τ : ℍ => Real.exp (-Real.pi * (τ : ℂ).im / 4)) := by
    funext τ; congr 1; ring
  rw [hconv] at hexp
  have hg : Tendsto (fun τ : ℍ => Real.exp (-Real.pi * (τ : ℂ).im / 4) * theta2BoundConst)
      UpperHalfPlane.atImInfty (𝓝 0) := by
    simpa using hexp.mul_const theta2BoundConst
  refine squeeze_zero' (Eventually.of_forall (fun τ => norm_nonneg _)) ?_ hg
  filter_upwards [hev] with τ hτ
  exact norm_theta2_le_exp τ hτ

end Work.Modular
