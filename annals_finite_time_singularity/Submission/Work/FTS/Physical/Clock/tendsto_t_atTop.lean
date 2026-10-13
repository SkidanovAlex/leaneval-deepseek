/-
# The physical clock exhausts the blow-up interval: `t(τ) → T`

`Work.FTS.Physical.PhysClock` bundles the amplitude `A` of the dynamic rescaling: `A > 0` and
continuous on `[0,∞)`, solving the modulation ODE `A' = -(1+μ)A` there, with the modulation
bounds `1/2 ≤ 1+μ ≤ 2`.  The physical time is `t(τ) = ∫₀^τ A` and the blow-up time is
`T = ∫₀^∞ A`.

This file proves the requested lemma `PhysClock.tendsto_t_atTop`:

  `Tendsto C.t atTop (𝓝 C.T)`,

i.e. as fake time tends to infinity the physical clock exhausts the blow-up interval.  The
argument is self-contained and uses both modulation bounds exactly once each:

* **Exponential decay** (`PhysClock.A_le_exp_decay`): the function `τ ↦ A τ · e^{τ/2}` is
  antitone on `[0,∞)`, because its derivative there is
  `A τ · e^{τ/2} · (1/2 - (1 + μ τ)) ≤ 0` by the lower bound `1/2 ≤ 1 + μ`.  Hence
  `A τ ≤ A 0 · e^{-τ/2}` for `τ ≥ 0`.
* **Integrability** (`PhysClock.integrableOn_A_Ici`): `A` is dominated on `[0,∞)` by the
  integrable function `A 0 · e^{-x/2}`, so `IntegrableOn A (Ici 0)`.
* **The limit**: the interval integrals `τ ↦ ∫₀^τ A` converge to the improper integral
  `∫_{(0,∞)} A` (`MeasureTheory.intervalIntegral_tendsto_integral_Ioi`, applied with
  `IntegrableOn A (Ioi 0)`, which follows from the previous point by `mono_set`).  The latter is
  `T = ∫_{[0,∞)} A` because `(0,∞) =ᵐ [0,∞)` for Lebesgue measure (`{0}` is a null set).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.Physical.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Physical.Clock

open MeasureTheory Filter Topology Set
open scoped Topology

set_option autoImplicit false

/-! ## Elementary consequences of the modulation bounds -/

/-- The amplitude is nonnegative on the fake-time half-line. -/
theorem PhysClock.A_nonneg_of_nonneg (C : Work.FTS.Physical.PhysClock) {τ : ℝ} (hτ : 0 ≤ τ) :
    0 ≤ C.A τ := (C.hApos τ hτ).le

/-- **Exponential decay of the amplitude.**  `A τ ≤ A 0 · e^{-τ/2}` for `τ ≥ 0`.

Proof: `f τ = A τ · e^{τ/2}` has derivative `A τ · e^{τ/2} · (1/2 - (1 + μ τ)) ≤ 0` on `(0,∞)`
(here `1/2 ≤ 1 + μ τ` is used), and `f` is continuous on `[0,∞)`; hence `f` is antitone there,
so `A τ · e^{τ/2} ≤ A 0`, and multiplying by `e^{-τ/2} > 0` gives the claim. -/
theorem PhysClock.A_le_exp_decay (C : Work.FTS.Physical.PhysClock) {τ : ℝ} (hτ : 0 ≤ τ) :
    C.A τ ≤ C.A 0 * Real.exp (-τ / 2) := by
  set f : ℝ → ℝ := fun τ => C.A τ * Real.exp (τ / 2) with hf
  have hcont : ContinuousOn f (Set.Ici 0) := by
    rw [hf]
    exact C.hAcont.mul (Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn
  have hdiff : DifferentiableOn ℝ f (interior (Set.Ici (0:ℝ))) := by
    intro x hx
    rw [interior_Ici] at hx
    have hxA : HasDerivAt C.A (-(1 + C.mu x) * C.A x) x := C.hAderiv x hx.le
    have hxexp : HasDerivAt (fun y : ℝ => Real.exp (y / 2)) (Real.exp (x / 2) * (1 / 2)) x := by
      have h1 : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := by
        simpa using (hasDerivAt_id x).div_const 2
      have h2 := (Real.hasDerivAt_exp (x / 2)).comp x h1
      simpa [Function.comp_def] using h2
    rw [hf]
    exact (hxA.mul hxexp).differentiableAt.differentiableWithinAt
  have hmono : AntitoneOn f (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont hdiff ?_
    intro x hx
    rw [interior_Ici] at hx
    have hxA : HasDerivAt C.A (-(1 + C.mu x) * C.A x) x := C.hAderiv x hx.le
    have hxexp : HasDerivAt (fun y : ℝ => Real.exp (y / 2)) (Real.exp (x / 2) * (1 / 2)) x := by
      have h1 : HasDerivAt (fun y : ℝ => y / 2) (1 / 2) x := by
        simpa using (hasDerivAt_id x).div_const 2
      have h2 := (Real.hasDerivAt_exp (x / 2)).comp x h1
      simpa [Function.comp_def] using h2
    have hderiv : deriv f x =
        -(1 + C.mu x) * C.A x * Real.exp (x / 2) + C.A x * (Real.exp (x / 2) * (1 / 2)) := by
      rw [hf]; exact (hxA.mul hxexp).deriv
    rw [hderiv]
    have hA0 : 0 ≤ C.A x := (C.hApos x hx.le).le
    have hexp : 0 ≤ Real.exp (x / 2) := (Real.exp_pos _).le
    have hmu : 1 / 2 ≤ 1 + C.mu x := by have := C.hmu_lo x hx.le; linarith
    have key : -(1 + C.mu x) * C.A x * Real.exp (x / 2) + C.A x * (Real.exp (x / 2) * (1 / 2))
        = C.A x * Real.exp (x / 2) * (1 / 2 - (1 + C.mu x)) := by ring_nf
    rw [key]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hA0 hexp) (by linarith)
  have h2 : C.A τ * Real.exp (τ / 2) ≤ C.A 0 := by
    have h0mem : (0 : ℝ) ∈ Set.Ici 0 := by simp
    have h3 := hmono h0mem hτ hτ
    simpa [hf] using h3
  have hexp : 0 < Real.exp (-(τ / 2)) := Real.exp_pos _
  have h4 := mul_le_mul_of_nonneg_right h2 hexp.le
  have h5 : C.A τ * Real.exp (τ / 2) * Real.exp (-(τ / 2)) = C.A τ := by
    rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  rw [h5] at h4
  calc C.A τ ≤ C.A 0 * Real.exp (-(τ / 2)) := h4
    _ = C.A 0 * Real.exp (-τ / 2) := by rw [neg_div]

/-- **`A` is integrable on `[0,∞)`**: the blow-up happens in finite time.  Comparison of the
exponential decay bound with the integrable function `A 0 · e^{-x/2}`. -/
theorem PhysClock.integrableOn_A_Ici (C : Work.FTS.Physical.PhysClock) :
    IntegrableOn C.A (Set.Ici 0) := by
  have h1 : IntegrableOn (fun x : ℝ => Real.exp ((-(1 / 2)) * x)) (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (a := -(1 / 2)) (by norm_num) 0
  have h2 : IntegrableOn (fun x : ℝ => Real.exp ((-(1 / 2)) * x)) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi
      (f := fun x : ℝ => Real.exp ((-(1 / 2)) * x)) (b := (0 : ℝ))).mpr h1
  have h3 : Integrable (fun x : ℝ => Real.exp ((-(1 / 2)) * x)) (volume.restrict (Set.Ici 0)) := h2
  have hb : Integrable (fun x : ℝ => C.A 0 * Real.exp (-(1 / 2) * x))
      (volume.restrict (Set.Ici 0)) := by
    simpa only [smul_eq_mul] using h3.const_mul (C.A 0)
  refine hb.mono' (C.hAcont.aestronglyMeasurable measurableSet_Ici) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (C.hApos x hx).le]
  calc C.A x ≤ C.A 0 * Real.exp (-x / 2) := PhysClock.A_le_exp_decay C hx
    _ = C.A 0 * Real.exp (-(1 / 2) * x) := by
        congr 1
        rw [show -x / 2 = -(1 / 2) * x by ring]

/-! ## The clock exhausts the blow-up interval -/

/-- **`t(τ) → T`** as `τ → ∞`: the physical time exhausts the blow-up interval. -/
theorem tendsto_t_atTop (C : Work.FTS.Physical.PhysClock) :
    Filter.Tendsto C.t Filter.atTop (nhds C.T) := by
  have hfi : IntegrableOn C.A (Set.Ioi 0) :=
    (PhysClock.integrableOn_A_Ici C).mono_set Set.Ioi_subset_Ici_self
  have hT : (∫ x in Set.Ioi 0, C.A x) = C.T := by
    show (∫ x in Set.Ioi 0, C.A x) = ∫ x in Set.Ici (0 : ℝ), C.A x
    exact MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici' (measure_singleton 0))
  have h := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (μ := volume) (f := C.A)
    (b := fun τ : ℝ => τ) 0 hfi tendsto_id
  rw [hT] at h
  exact h

end Work.FTS.Physical.Clock
