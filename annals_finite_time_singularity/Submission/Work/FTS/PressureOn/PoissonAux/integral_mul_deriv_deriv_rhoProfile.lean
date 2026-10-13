/-
# The total mass of `r ↦ r · ρ_ε''(r)`

The profile `ρ_ε(r) = 1 - χ(r²/ε²)` (see `PoissonAux/Defs`) vanishes for `|r| ≤ ε` and equals `1`
for `|r| ≥ √2 ε`, so it is a smooth monotone "switch" and

  `∫_0^∞ r · ρ_ε''(r) dr = -1`.

This is the one-dimensional content of `∫ x, massKernel ε x = -1` (the total mass of the truncated
Laplacian kernel), used in `tendsto_integral_massKernel_mul`: the truncated Newtonian kernel
`smallCut ε · newtonKernel` has Laplacian `massKernel ε`, and its total mass has to be `-1` for
the fundamental-solution identity `Δ(1/4π‖x‖) = -δ₀`.

## Proof

Integration by parts on `[0,R]` with `R > √2 ε` and `u(r) = r`, `v = ρ_ε'`:

  `∫_0^R r ρ_ε''(r) dr = R · ρ_ε'(R) - 0 · ρ_ε'(0) - ∫_0^R ρ_ε'(r) dr
                      = - (ρ_ε(R) - ρ_ε(0)) = -1`,

because `ρ_ε'` vanishes at `R` (`ρ_ε ≡ 1` near `R`) and `ρ_ε(R) = 1`, `ρ_ε(0) = 0`.  The integrand
vanishes on `(R,∞)` as well, so the improper integral over `Ioi 0` equals the one over `Ioc 0 R`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PressureOn.PoissonAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set MeasureTheory Filter
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.PoissonAux

/-! ## Pointwise values of `rhoProfile` to the right of `√2 ε` -/

/-- `ρ_ε` is identically `1` at every point to the right of `√2 ε`. -/
theorem rhoProfile_eq_one_of_sqrt_two_mul_lt {ε x : ℝ} (hε : 0 < ε)
    (hx : Real.sqrt 2 * ε < x) : Work.FTS.PressureOn.rhoProfile ε x = 1 := by
  refine Work.FTS.PressureOn.rhoProfile_eq_one hε ?_
  have hs : (Real.sqrt 2 * ε) ^ 2 = 2 * ε ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : 0 < Real.sqrt 2 * ε := by positivity
  nlinarith [hx, hs, h2]

/-- `ρ_ε` is *eventually* identically `1` near every point to the right of `√2 ε`. -/
theorem eventuallyEq_one_rhoProfile_of_sqrt_two_mul_lt {ε x : ℝ} (hε : 0 < ε)
    (hx : Real.sqrt 2 * ε < x) :
    Work.FTS.PressureOn.rhoProfile ε =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact rhoProfile_eq_one_of_sqrt_two_mul_lt hε hy

/-- `ρ_ε''` vanishes to the right of `√2 ε` (where `ρ_ε ≡ 1`). -/
theorem deriv_deriv_rhoProfile_eq_zero_of_sqrt_two_mul_lt {ε x : ℝ} (hε : 0 < ε)
    (hx : Real.sqrt 2 * ε < x) :
    deriv (deriv (Work.FTS.PressureOn.rhoProfile ε)) x = 0 := by
  have h1 : Work.FTS.PressureOn.rhoProfile ε =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
    eventuallyEq_one_rhoProfile_of_sqrt_two_mul_lt hε hx
  have h2 : deriv (Work.FTS.PressureOn.rhoProfile ε) =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    (h1.deriv).trans (Eventually.of_forall fun y => by simp)
  have h3 := h2.deriv_eq
  simpa using h3

/-! ## The integral -/

/-- **The total mass of `r ↦ r ρ_ε''(r)`**: for `ε > 0`,
`∫_0^∞ r · ρ_ε''(r) dr = -1`, where `ρ_ε = rhoProfile ε`. -/
theorem integral_mul_deriv_deriv_rhoProfile (ε : ℝ) (hε : 0 < ε) :
    ∫ r in Set.Ioi (0 : ℝ), r * deriv (deriv (Work.FTS.PressureOn.rhoProfile ε)) r = -1 := by
  -- a cutoff radius beyond the support of `ρ_ε''`
  set R : ℝ := Real.sqrt 2 * ε + 1 with hRdef
  have h2pos : 0 < Real.sqrt 2 * ε := by positivity
  have hR2 : Real.sqrt 2 * ε < R := by rw [hRdef]; linarith
  have hRpos : 0 < R := lt_trans h2pos hR2
  -- `ρ_ε` is `C²`
  have hC2 : ContDiff ℝ 2 (Work.FTS.PressureOn.rhoProfile ε) :=
    contDiff_const.sub ((Work.FTS.PressureOn.contDiff_radialCut 2).comp
      ((contDiff_id (𝕜 := ℝ)).pow 2 |>.div_const (ε ^ 2)))
  have hderiv2 : Differentiable ℝ (deriv (Work.FTS.PressureOn.rhoProfile ε)) :=
    hC2.differentiable_deriv_two
  have hderivcont : Continuous (deriv (Work.FTS.PressureOn.rhoProfile ε)) :=
    hC2.continuous_deriv (by norm_num)
  have hderiv2cont : Continuous (deriv (deriv (Work.FTS.PressureOn.rhoProfile ε))) := by
    fun_prop
  -- the integrand vanishes beyond `R`
  have hsupp : ∀ x ∈ Set.Ioi (0 : ℝ) \ Set.Ioc 0 R,
      x * deriv (deriv (Work.FTS.PressureOn.rhoProfile ε)) x = 0 := by
    intro x hx
    have hxR : R < x := by
      by_contra h
      exact hx.2 ⟨hx.1, not_lt.mp h⟩
    rw [deriv_deriv_rhoProfile_eq_zero_of_sqrt_two_mul_lt hε (lt_trans hR2 hxR), mul_zero]
  have h1 : (∫ r in Set.Ioi (0 : ℝ),
        r * deriv (deriv (Work.FTS.PressureOn.rhoProfile ε)) r)
      = ∫ r in Set.Ioc 0 R, r * deriv (deriv (Work.FTS.PressureOn.rhoProfile ε)) r :=
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun x hx => hx.1) hsupp
  rw [h1, ← intervalIntegral.integral_of_le hRpos.le]
  -- integration by parts on `[0,R]`
  have hibp : ∫ r in (0:ℝ)..R, r * deriv (deriv (Work.FTS.PressureOn.rhoProfile ε)) r
      = R * deriv (Work.FTS.PressureOn.rhoProfile ε) R
        - 0 * deriv (Work.FTS.PressureOn.rhoProfile ε) 0
        - ∫ x in (0:ℝ)..R, (1:ℝ) * deriv (Work.FTS.PressureOn.rhoProfile ε) x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun r : ℝ => r) (v := deriv (Work.FTS.PressureOn.rhoProfile ε))
      (u' := fun _ : ℝ => (1:ℝ))
      (v' := deriv (deriv (Work.FTS.PressureOn.rhoProfile ε)))
      (fun x _ => hasDerivAt_id x)
      (fun x _ => hasDerivAt_deriv_iff.mpr (hderiv2 x))
      (continuous_const.intervalIntegrable _ _)
      (hderiv2cont.intervalIntegrable _ _)
  rw [hibp]
  -- the boundary terms and the fundamental theorem of calculus
  have hρR : Work.FTS.PressureOn.rhoProfile ε R = 1 :=
    rhoProfile_eq_one_of_sqrt_two_mul_lt hε hR2
  have hρ0 : Work.FTS.PressureOn.rhoProfile ε 0 = 0 :=
    Work.FTS.PressureOn.rhoProfile_eq_zero hε (by simpa using sq_nonneg ε)
  have hdR : deriv (Work.FTS.PressureOn.rhoProfile ε) R = 0 := by
    have h := (eventuallyEq_one_rhoProfile_of_sqrt_two_mul_lt hε hR2).deriv_eq
    simpa using h
  have hftc : ∫ x in (0:ℝ)..R, deriv (Work.FTS.PressureOn.rhoProfile ε) x
      = Work.FTS.PressureOn.rhoProfile ε R - Work.FTS.PressureOn.rhoProfile ε 0 :=
    intervalIntegral.integral_deriv_eq_sub
      (fun x _ => hC2.differentiable (by norm_num) x)
      (hderivcont.intervalIntegrable _ _)
  have hone : (∫ x in (0:ℝ)..R, (1:ℝ) * deriv (Work.FTS.PressureOn.rhoProfile ε) x)
      = ∫ x in (0:ℝ)..R, deriv (Work.FTS.PressureOn.rhoProfile ε) x := by
    simp_rw [one_mul]
  rw [hone, hftc, hdR, hρR, hρ0]
  ring

end Work.FTS.PressureOn.PoissonAux
