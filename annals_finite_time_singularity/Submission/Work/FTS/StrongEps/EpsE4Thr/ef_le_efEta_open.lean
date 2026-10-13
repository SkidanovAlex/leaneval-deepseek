import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts
import Submission.Work.Coercivity.Ef_le_EfEta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- On the open angular interval `(0,π/2)` the `ℋ¹`-weight `w / sin(2θ)^{η/2}` dominates
the plain radial weight `w`: there `0 < sin(2θ) ≤ 1`, so `1 ≤ sin(2θ)^{-η/2}`, and `w ≥ 0`. -/
private theorem w_le_w_div_sin {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.w z ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hpow_pos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    Real.rpow_pos_of_pos hs _
  have hpow_le : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hs) (Real.sin_le_one _) (by rw [Work.Spaces.eta]; norm_num)
  have hinv : (1 : ℝ) ≤ ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))⁻¹ :=
    (one_le_inv₀ hpow_pos).mpr hpow_le
  have hw : 0 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w]
    positivity
  calc Work.Spaces.w z = Work.Spaces.w z * 1 := by ring
    _ ≤ Work.Spaces.w z * ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hw
    _ = Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
        (div_eq_mul_inv _ _).symm

/-- **The `η`-weighted energy dominates the unweighted one, in the open-quadrant class.**

Both energies are squared iterated `L²`-norms of `f` against the radial weight `w` resp. the
`ℋ¹`-weight `w·sin(2θ)^{-η/2}`.  On the open angular interval the second weight dominates
the first, and `HkMem α 1 f` supplies exactly the honesty of the `η`-weighted iterated
integral: `f·w/sin(2θ)^{η/2}` is (definitionally) the `D_z⁰`-summand of `HkIntegrand α 1 f`,
so `i2Mem_sq_of_le` gives that `∫_z ∫_θ (f·w/sin(2θ)^{η/2})²` is an honest iterated integral.
Monotonicity of the iterated integral then yields `Ef f ≤ EfEta f`. -/
theorem ef_le_efEta_open {α : ℝ} {f : Work.FTS.Galerkin.Fn}
    (hs : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 1 f) :
    Work.Coercivity.Ef f ≤ Work.Coercivity.EfEta f := by
  -- ## The `D_z⁰`-weighted summand is continuous on the open quadrant
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Coercivity.U0 f p.1 p.2) ^ 2)
      Work.FTS.CoercivityFix.Coer1.Qd := by
    have h := (hs.continuousOn_summand 0).pow 2
    have hfun : (fun p : ℝ × ℝ => (Work.Coercivity.U0 f p.1 p.2) ^ 2)
        = fun p : ℝ × ℝ => (Work.Spaces.DzIter 0 f p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      funext p
      simp only [Work.Coercivity.U0, Work.Spaces.DzIter_zero]
    rw [hfun]
    exact h
  -- ## `(f·w/sin(2θ)^{η/2})²` is one of the summands of the `ℋ¹`-integrand
  have hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Coercivity.U0 f z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 1 f z θ := by
    intro z _ θ _
    have h := Work.Spaces.sq_le_HkIntegrand_z α 1 f z θ 0 (by norm_num)
    simpa only [Work.Coercivity.U0, Work.Spaces.DzIter_zero] using h
  -- ## Honesty of the `η`-weighted iterated integral
  have hB : Work.Coercivity.I2Mem (fun z θ => (Work.Coercivity.U0 f z θ) ^ 2) :=
    Work.FTS.CoercivityFix.Coer1.i2Mem_sq_of_le α 1 hm hcont hle
  -- ## Both energies as iterated integrals
  have hEf : Work.Coercivity.Ef f
      = Work.Spaces.L2Sq (fun z θ => f z θ * Work.Spaces.w z) := rfl
  have hEfEta : Work.Coercivity.EfEta f = Work.Spaces.L2Sq (Work.Coercivity.U0 f) :=
    (Work.Coercivity.L2Sq_U0_eq_EfEta f).symm
  rw [hEf, hEfEta, Work.Spaces.L2Sq, Work.Spaces.L2Sq]
  -- ## The outer integral
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hB.2 ?_
  refine MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici) fun z hz => ?_
  -- ## The inner (angular) integral
  refine MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun θ => sq_nonneg _) (hB.1 z hz) ?_
  filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo] with θ hθ
  have hw : 0 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w]
    positivity
  have h2 : (Work.Spaces.w z) ^ 2
      ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
    pow_le_pow_left₀ hw (w_le_w_div_sin hθ) 2
  have hmain := mul_le_mul_of_nonneg_left h2 (sq_nonneg (f z θ))
  simpa only [Work.Coercivity.U0, Work.Spaces.DzIter_zero, mul_pow] using hmain

end Work.FTS.StrongEps.EpsE4Thr
