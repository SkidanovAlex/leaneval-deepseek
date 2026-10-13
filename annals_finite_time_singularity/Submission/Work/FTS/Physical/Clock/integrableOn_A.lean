import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.Physical.Defs
import Submission.Work.FTS.Physical.Clock.A_le_exp_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter Asymptotics
open scoped Topology ENNReal

namespace Work.FTS.Physical.Clock

/-- **The modulated amplitude is antitone.**  The function `τ ↦ A τ · e^{τ/2}` is antitone on
`[0,∞)`: its derivative is `A τ · e^{τ/2} · (1/2 - (1 + μ τ)) ≤ 0` by the lower modulation bound
`1 ≤ 2 (1 + μ τ)`.  This is the integrated form of `A' = -(1+μ) A` with `1 + μ ≥ 1/2`. -/
private theorem antitoneOn_A_mul_exp (C : Work.FTS.Physical.PhysClock) :
    AntitoneOn (fun τ : ℝ => C.A τ * Real.exp (τ / 2)) (Set.Ici 0) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (D := Set.Ici 0) (convex_Ici 0)
    (f := fun τ : ℝ => C.A τ * Real.exp (τ / 2))
    (f' := fun x : ℝ => (-(1 + C.mu x) * C.A x) * Real.exp (x / 2)
      + C.A x * (Real.exp (x / 2) * (1 / 2))) ?_ ?_ ?_
  · exact C.hAcont.mul (Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn
  · intro x hx
    have hx0 : 0 ≤ x := le_of_lt (mem_Ioi.mp (by simpa only [interior_Ici] using hx))
    exact ((C.hAderiv x hx0).mul (((hasDerivAt_id x).div_const 2).exp)).hasDerivWithinAt
  · intro x hx
    have hx0 : 0 ≤ x := le_of_lt (mem_Ioi.mp (by simpa only [interior_Ici] using hx))
    have hA0 : 0 ≤ C.A x := (C.hApos x hx0).le
    have hE : 0 ≤ Real.exp (x / 2) := (Real.exp_pos _).le
    have hm : 0 ≤ 1 / 2 + C.mu x := by linarith [C.hmu_lo x hx0]
    have hkey : (-(1 + C.mu x) * C.A x) * Real.exp (x / 2)
        + C.A x * (Real.exp (x / 2) * (1 / 2))
        = -(C.A x * Real.exp (x / 2) * (1 / 2 + C.mu x)) := by ring
    rw [hkey]
    exact neg_nonpos.mpr (mul_nonneg (mul_nonneg hA0 hE) hm)

/-- **The decay bound**: `A s ≤ A τ · e^{-(s-τ)/2}` for `0 ≤ τ ≤ s`. -/
private theorem A_le_exp_mul_decay (C : Work.FTS.Physical.PhysClock) {τ s : ℝ}
    (hτ : 0 ≤ τ) (hτs : τ ≤ s) :
    C.A s ≤ C.A τ * Real.exp (-(s - τ) / 2) := by
  have hs : 0 ≤ s := hτ.trans hτs
  have h := antitoneOn_A_mul_exp C hτ hs hτs
  have hEs : 0 < Real.exp (s / 2) := Real.exp_pos _
  have h1 : C.A s ≤ C.A τ * Real.exp (τ / 2) / Real.exp (s / 2) :=
    (le_div_iff₀ hEs).mpr h
  have h2 : C.A τ * Real.exp (τ / 2) / Real.exp (s / 2)
      = C.A τ * Real.exp (-(s - τ) / 2) := by
    rw [mul_div_assoc, ← Real.exp_sub,
      show τ / 2 - s / 2 = -(s - τ) / 2 from by ring]
  rwa [h2] at h1

theorem integrableOn_A (C : Work.FTS.Physical.PhysClock) : MeasureTheory.IntegrableOn C.A (Set.Ici 0) := by
  have hO : Asymptotics.IsBigO Filter.atTop C.A (fun x : ℝ => Real.exp (-(1 / 2) * x)) := by
    refine Asymptotics.IsBigO.of_bound (C.A 0) ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have hdec : C.A x ≤ C.A 0 * Real.exp (-(1 / 2) * x) := by
      have h := A_le_exp_mul_decay C (le_refl (0 : ℝ)) hx
      rw [show -(x - 0) / 2 = -(1 / 2) * x from by ring] at h
      exact h
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (C.hApos x hx).le,
      abs_of_pos (Real.exp_pos _)]
    exact hdec
  have hInt : MeasureTheory.IntegrableOn C.A (Set.Ioi 0) :=
    integrable_of_isBigO_exp_neg (by norm_num) C.hAcont hO
  rwa [← integrableOn_Ici_iff_integrableOn_Ioi] at hInt

end Work.FTS.Physical.Clock
