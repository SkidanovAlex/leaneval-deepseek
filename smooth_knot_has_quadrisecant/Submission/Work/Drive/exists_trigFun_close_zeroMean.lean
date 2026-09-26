import Mathlib
import Submission.Work.Drive.trigFun
import Submission.Work.Drive.exists_trigFun_close

namespace Work.Drive

open scoped Real

open TrigFun

noncomputable section

/-- The integral of `t ↦ cos (k t)` over one period `[0, 2π]` is `2π` for `k = 0` and `0`
otherwise. -/
lemma integral_cos_int_mul_two_pi (k : ℤ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), Real.cos ((k : ℝ) * t)
      = if k = 0 then 2 * Real.pi else 0 := by
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    simp
  · rw [if_neg hk]
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hkR]
    simp only [mul_zero]
    rw [integral_cos]
    have hsin : Real.sin ((k : ℝ) * (2 * Real.pi)) = 0 := by
      simpa using (Real.sin_add_int_mul_two_pi 0 k)
    rw [hsin, Real.sin_zero, sub_zero, smul_zero]

/-- The integral of `t ↦ sin (k t)` over one period `[0, 2π]` vanishes for every integer `k`. -/
lemma integral_sin_int_mul_two_pi (k : ℤ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), Real.sin ((k : ℝ) * t) = 0 := by
  rcases eq_or_ne k 0 with hk | hk
  · subst hk; simp
  · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hkR]
    simp only [mul_zero]
    rw [integral_sin, Real.cos_zero, Real.cos_int_mul_two_pi, sub_self, smul_zero]

/-- **The integral of a real trigonometric sum over one period is `2π` times its constant
coefficient**: `∫₀^{2π} P.toFun = 2π * P.c 0`. -/
lemma integral_toFun_two_pi (P : TrigFun ℝ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), P.toFun t = (2 * Real.pi) * P.c 0 := by
  have hdecomp : ∀ t : ℝ, P.toFun t =
      (∑ k ∈ P.c.support, Real.cos ((k : ℝ) * t) * P.c k) +
      (∑ k ∈ P.d.support, Real.sin ((k : ℝ) * t) * P.d k) := by
    intro t
    simp [TrigFun.toFun, Finsupp.sum, smul_eq_mul]
  have hcos : (∫ t in (0 : ℝ)..(2 * Real.pi),
        ∑ k ∈ P.c.support, Real.cos ((k : ℝ) * t) * P.c k)
      = (2 * Real.pi) * P.c 0 := by
    rw [intervalIntegral.integral_finsetSum]
    · have h1 : ∀ k ∈ P.c.support,
          (∫ t in (0 : ℝ)..(2 * Real.pi), Real.cos ((k : ℝ) * t) * P.c k)
            = (if k = 0 then 2 * Real.pi else 0) * P.c k := by
        intro k _
        rw [intervalIntegral.integral_mul_const, integral_cos_int_mul_two_pi k]
      rw [Finset.sum_congr rfl h1, Finset.sum_eq_single 0]
      · simp
      · intro b _ hb0; simp [hb0]
      · intro h0
        simp only [Finsupp.mem_support_iff, not_not] at h0
        simp [h0]
    · intro k _
      exact Continuous.intervalIntegrable (by fun_prop) _ _
  have hsin : (∫ t in (0 : ℝ)..(2 * Real.pi),
        ∑ k ∈ P.d.support, Real.sin ((k : ℝ) * t) * P.d k) = 0 := by
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.sum_eq_zero]
      intro k _
      rw [intervalIntegral.integral_mul_const, integral_sin_int_mul_two_pi k, zero_mul]
    · intro k _
      exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [show (fun t : ℝ => P.toFun t) =
      (fun t => (∑ k ∈ P.c.support, Real.cos ((k : ℝ) * t) * P.c k) +
        (∑ k ∈ P.d.support, Real.sin ((k : ℝ) * t) * P.d k)) from funext hdecomp]
  rw [intervalIntegral.integral_add]
  · rw [hcos, hsin, add_zero]
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- **Trigonometric density, mean-zero form** (`2 * Real.pi` is the period of the workspace).
A continuous `2π`-periodic real function of zero mean over one period is uniformly approximated by a
finite trigonometric sum whose frequency-`0` (constant) coefficient vanishes.  This is the density
step of `Work.Drive.exists_analytic_periodic_close`; `Work.Drive.TrigFun`
(file `Submission/Work/Drive/trigFun.lean`) is the finite-trigonometric-sum model, in which the
constant coefficient `q.c 0` is exactly the mean of `q.toFun`.

Proof route: this is `Work.Drive.exists_trigFun_close` plus the constant correction.  Lift `h` to
`H : C(AddCircle (2 * Real.pi), ℝ)` via `AddCircle.liftIco_zero_continuous` (`h 0 = h (2π)`),
complexify to `Hc`, and use `span_fourier_closure_eq_top` + `Metric.mem_closure_iff` to get
`P ∈ Submodule.span ℂ (range fourier)` with `dist P Hc < ε/2`.  `Submodule.span_induction` shows
every `P` in that span has a representation `P (t : AddCircle (2π)) = q.toFun t` for some
`q : TrigFun ℂ` with `q.c 0 = fourierCoeff P 0` (generators `TrigFun.expFun k` +
`fourier_coe_apply` + `Complex.exp_mul_I`; addition `toFun_add`; complex scalar multiplication
`TrigFun.mulComplex` + `toFun_mulComplex`; coefficients via `MeasureTheory.fourierCoeff.add`,
`fourierCoeff.const_smul`, `fourierCoeff_fourier`).  Since `fourierCoeff Hc 0 = 0` (from `hmean`
via `fourierCoeff_eq_intervalIntegral`) and `‖fourierCoeff F 0‖ ≤ ‖F‖`, we get `|q.c 0| < ε/2`;
then `q' := q - TrigFun.constTrig (q.c 0)` has `q'.c 0 = 0` (`TrigFun.toFun_sub`,
`toFun_constTrig`) and `|q'.toFun t - ↑(h t)| < ε`, and `TrigFun.reTrig` + `toFun_reTrig` give the
real trigonometric sum.  Alternatively (`Work.Drive.trigFun_integral_toFun`), use any density
approximant `q₀` and replace it by `q₀ - constTrig (q₀.c 0)`, whose constant coefficient is
`≤ ‖q₀ - h‖` since `h` has mean `0`. -/
theorem exists_trigFun_close_zeroMean {h : ℝ → ℝ} (hc : Continuous h)
    (hp : Function.Periodic h (2 * Real.pi))
    (hmean : ∫ t in (0 : ℝ)..(2 * Real.pi), h t = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : Work.Drive.TrigFun ℝ, q.c 0 = 0 ∧ ∀ t : ℝ, |q.toFun t - h t| < ε := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2pi_ne : (2 * Real.pi) ≠ 0 := ne_of_gt h2pi
  obtain ⟨q₀, hq₀⟩ := exists_trigFun_close hc hp (ε := ε / 2) (by linarith)
  -- `q₀.toFun` is continuous, hence interval integrable
  have hdecomp : ∀ t : ℝ, q₀.toFun t =
      (∑ k ∈ q₀.c.support, Real.cos ((k : ℝ) * t) * q₀.c k) +
      (∑ k ∈ q₀.d.support, Real.sin ((k : ℝ) * t) * q₀.d k) := by
    intro t
    simp [TrigFun.toFun, Finsupp.sum, smul_eq_mul]
  have hcont : Continuous (fun t : ℝ => q₀.toFun t) := by
    have heq : (fun t : ℝ => q₀.toFun t) =
        (fun t => (∑ k ∈ q₀.c.support, Real.cos ((k : ℝ) * t) * q₀.c k) +
          (∑ k ∈ q₀.d.support, Real.sin ((k : ℝ) * t) * q₀.d k)) := funext hdecomp
    rw [heq]
    fun_prop
  have hInt : IntervalIntegrable (fun t : ℝ => q₀.toFun t) MeasureTheory.volume 0
      (2 * Real.pi) :=
    hcont.intervalIntegrable _ _
  -- the constant coefficient of `q₀` is bounded by the uniform distance to `h`
  have hmean_q : q₀.c 0
      = (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..(2 * Real.pi), (q₀.toFun t - h t) := by
    have hsplit : (∫ t in (0 : ℝ)..(2 * Real.pi), (q₀.toFun t - h t))
        = (∫ t in (0 : ℝ)..(2 * Real.pi), q₀.toFun t) -
          (∫ t in (0 : ℝ)..(2 * Real.pi), h t) :=
      intervalIntegral.integral_sub hInt (hc.intervalIntegrable _ _)
    rw [hsplit, hmean, sub_zero, integral_toFun_two_pi q₀, ← mul_assoc,
      inv_mul_cancel₀ h2pi_ne, one_mul]
  have hb1 : |∫ t in (0 : ℝ)..(2 * Real.pi), (q₀.toFun t - h t)| ≤ (ε / 2) * (2 * Real.pi) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ))
      (b := 2 * Real.pi) (C := ε / 2)
      (f := fun t : ℝ => q₀.toFun t - h t) (fun x _ => by
        rw [Real.norm_eq_abs]; exact le_of_lt (hq₀ x))
    rwa [sub_zero, abs_of_pos h2pi] at h
  have hbound : |q₀.c 0| ≤ ε / 2 := by
    calc |q₀.c 0|
        = (2 * Real.pi)⁻¹ * |∫ t in (0 : ℝ)..(2 * Real.pi), (q₀.toFun t - h t)| := by
          rw [hmean_q, abs_mul, abs_of_pos (inv_pos.mpr h2pi)]
      _ ≤ (2 * Real.pi)⁻¹ * ((ε / 2) * (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_left hb1 (le_of_lt (inv_pos.mpr h2pi))
      _ = ε / 2 := by field_simp
  refine ⟨q₀ - TrigFun.constTrig (q₀.c 0), ?_, fun t => ?_⟩
  · simp [TrigFun.c_sub, TrigFun.c_constTrig]
  · have hq : (q₀ - TrigFun.constTrig (q₀.c 0)).toFun t = q₀.toFun t - q₀.c 0 := by
      rw [TrigFun.toFun_sub, TrigFun.toFun_constTrig]
    rw [hq]
    have h1 : |q₀.toFun t - q₀.c 0 - h t| = |(q₀.toFun t - h t) - q₀.c 0| := by
      ring_nf
    rw [h1]
    have h2 : |(q₀.toFun t - h t) - q₀.c 0| ≤ |q₀.toFun t - h t| + |q₀.c 0| := by
      simpa [sub_eq_add_neg] using abs_add_le (q₀.toFun t - h t) (-(q₀.c 0))
    linarith [h2, hq₀ t, hbound]

end

end Work.Drive
