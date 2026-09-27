import Mathlib

/-!
# Vanishing of a continuous function on a circle from the vanishing of all its moments

If a continuous function `g` on the sphere `|z| = r` (`r > 0`) has all its "moments"
`∮_{C(0,r)} g z * z ^ n` (for `n : ℤ`) equal to zero, then `g` vanishes identically on that
sphere.

The proof transports the moment conditions to the vanishing of all Fourier coefficients of the
continuous function `θ ↦ g (circleMap 0 r θ)` on the additive circle `AddCircle (2π)`, using that
the Fourier monomials are dense (in fact, that the Fourier series of a continuous function with
summable coefficients converges uniformly to it).
-/

open Complex MeasureTheory
open scoped Real

namespace Work.Potential

/-- Pointwise identity underlying the comparison between the circle integral
`∮ z in C(0,r), g z * z ^ k` and the "exponential moments" of `θ ↦ g (circleMap 0 r θ)`. -/
private lemma deriv_smul_mul_zpow (r : ℝ) (hr : r ≠ 0) (k : ℤ) (θ : ℝ) (g : ℂ → ℂ) :
    deriv (circleMap 0 r) θ • (g (circleMap 0 r θ) * circleMap 0 r θ ^ k) =
      ((r : ℂ) ^ (k + 1) * Complex.I) *
        (Complex.exp (((k + 1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I) * g (circleMap 0 r θ)) := by
  rw [deriv_circleMap, smul_eq_mul, circleMap_zero_zpow]
  have h1 : (↑r : ℂ) ^ (k + 1) = ↑r * ↑(r ^ k) := by
    rw [show k + 1 = 1 + k by ring, zpow_add₀ (by simpa using hr), zpow_one,
      Complex.ofReal_zpow]
  have h2 : Complex.exp (((k + 1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I) =
      Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (((↑k * θ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h1, h2, circleMap_zero (R := r) θ, circleMap_zero (R := r ^ k) (↑k * θ)]
  ring

/-- The circle integral of `g z * z ^ k` is a constant multiple of the `(k+1)`-st exponential
moment of `θ ↦ g (circleMap 0 r θ)`. -/
private lemma circleIntegral_mul_zpow_eq {r : ℝ} (hr : r ≠ 0) (k : ℤ) (g : ℂ → ℂ) :
    (∮ z in C(0, r), g z * z ^ k) =
      ((r : ℂ) ^ (k + 1) * Complex.I) *
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (((k + 1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I) * g (circleMap 0 r θ) := by
  rw [circleIntegral]
  rw [intervalIntegral.integral_congr (fun θ _ => deriv_smul_mul_zpow r hr k θ g)]
  rw [intervalIntegral.integral_const_mul]

theorem eq_zero_of_forall_moments_eq_zero
    {r : ℝ} (hr : 0 < r) {g : ℂ → ℂ}
    (hg : ContinuousOn g (Metric.sphere 0 r))
    (h : ∀ n : ℤ, (∮ z in C(0, r), g z * z ^ n) = 0) :
    ∀ z ∈ Metric.sphere 0 r, g z = 0 := by
  have hpi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  set F : ℝ → ℂ := fun θ => g (circleMap 0 r θ) with hF
  have hFcont : Continuous F := by
    rw [hF]
    exact hg.comp_continuous (continuous_circleMap 0 r)
      (fun θ => circleMap_mem_sphere 0 hr.le θ)
  have hFper : Function.Periodic F (2 * Real.pi) := by
    intro θ
    simp only [hF]
    exact congr_arg g (periodic_circleMap 0 r θ)
  have hFc_cont : Continuous hFper.lift := by
    refine continuous_coinduced_dom.mpr ?_
    convert hFcont using 1
    exact funext fun x => Function.Periodic.lift_coe hFper x
  set Fc : C(AddCircle (2 * Real.pi), ℂ) := ⟨hFper.lift, hFc_cont⟩ with hFc
  have hpt : ∀ x : ℝ, Fc (x : AddCircle (2 * Real.pi)) = F x := by
    intro x
    rw [hFc]
    exact Function.Periodic.lift_coe hFper x
  -- All exponential moments of `F` vanish.
  have hE : ∀ k : ℤ, (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (((k : ℤ) : ℂ) * (θ : ℂ) * Complex.I) * F θ) = 0 := by
    intro k
    have h1 : ((r : ℂ) ^ k * Complex.I) * (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (((k : ℤ) : ℂ) * (θ : ℂ) * Complex.I) * F θ) = 0 := by
      have h2 := h (k - 1)
      rw [circleIntegral_mul_zpow_eq (ne_of_gt hr) (k - 1) g] at h2
      have hsub : (k - 1) + 1 = k := by ring
      rw [hsub] at h2
      simpa only [hF] using h2
    exact (mul_eq_zero.mp h1).resolve_left (by
      apply mul_ne_zero
      · exact zpow_ne_zero _ (by exact_mod_cast hr.ne')
      · exact Complex.I_ne_zero)
  -- Hence all Fourier coefficients of `Fc` vanish.
  have hcoeff : ∀ n : ℤ, fourierCoeff Fc n = 0 := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral Fc n 0]
    have hfun : ∀ x ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
        fourier (-n) (x : AddCircle (2 * Real.pi)) • Fc (x : AddCircle (2 * Real.pi))
          = Complex.exp (((-n : ℤ) : ℂ) * (x : ℂ) * Complex.I) * F x := by
      intro x _
      rw [fourier_coe_apply, smul_eq_mul, hpt x]
      congr 1
      push_cast
      field_simp
    have h2 : (∫ x in (0 : ℝ)..(2 * Real.pi),
        fourier (-n) (x : AddCircle (2 * Real.pi)) • Fc (x : AddCircle (2 * Real.pi))) = 0 := by
      rw [intervalIntegral.integral_congr hfun]
      exact hE (-n)
    simp only [zero_add]
    rw [h2, smul_zero]
  -- A continuous function on the circle with vanishing Fourier coefficients is zero.
  have hFc_zero : Fc = 0 := by
    have hs : Summable (fourierCoeff (⇑Fc)) := by
      rw [show fourierCoeff (⇑Fc) = fun _ => 0 from funext hcoeff]
      exact summable_zero
    refine HasSum.unique (hasSum_fourier_series_of_summable (f := Fc) hs) ?_
    rw [show (fun i : ℤ => fourierCoeff (⇑Fc) i • fourier i) = fun _ => 0 from by
      funext i
      rw [hcoeff i, zero_smul]]
    exact hasSum_zero
  intro z hz
  have hzr : ‖z‖ = r := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
    exact hz
  have hzarg : circleMap 0 r z.arg = z := by
    rw [circleMap_zero, ← hzr]
    exact Complex.norm_mul_exp_arg_mul_I z
  calc g z = g (circleMap 0 r z.arg) := by rw [hzarg]
    _ = F z.arg := by rw [hF]
    _ = Fc (z.arg : AddCircle (2 * Real.pi)) := (hpt z.arg).symm
    _ = 0 := by rw [hFc_zero]; rfl

end Work.Potential
