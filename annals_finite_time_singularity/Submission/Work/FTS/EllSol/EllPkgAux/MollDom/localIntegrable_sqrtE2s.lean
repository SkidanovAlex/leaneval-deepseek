/-
# `Work.FTS.EllSol.EllPkgAux.MollDom.localIntegrable_sqrtE2s`

The logarithmic slice energy `t ↦ √(E2s G (exp t))` of a trace-class datum `G` is locally
integrable on `ℝ`.

**Route.**  Since `√(E2s G u) = √(ttIntS G u)/((w u)²)·u` (here `ttIntS G u = (w u)² E2s G u` is
the honest `H⁰`-mass of the slice), the substitution `u = exp t` turns the `t`-integral over a
compact interval `[p,q]` into the `u`-integral of `u ↦ √(E2s G u)/u` over `[exp p, exp q]`, and
there the radial factor `1/u` is *bounded* (`1/u ≤ exp(-p)` on `[exp p, ∞)`), so

`√(E2s G u)/u ≤ exp(-p)·√(E2s G u) ≤ exp(-p)·(1 + ttIntS G u)`

with the elementary `√a ≤ 1 + a`.  The last function is integrable over the `u`-window because
`ttIntS G` is (this is the `ttIntS`-half of the `FourInts` hypothesis) and the window has finite
measure.  Everything is transported by the one-dimensional change-of-variables formula
`MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul` with `f = Real.exp`; local
integrability in `t` then follows at every `x ∈ ℝ` from integrability on the neighbourhood
`Icc (x-1) (x+1)` (`MeasureTheory.IntegrableAtFilter`).

Note that **global** integrability in `t` is *false* in general (`E2s G` need not decay at
`∞`), which is why the argument is carried out on compact windows and the global
`MeasureTheory.integrable_comp_exp` is *not* applicable.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.mollSliceBound
import Submission.Work.FTS.EllSol.EllPkgAux.MollAux.aesmE2s

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

/-- **Pointwise estimate for the `u`-integrand.**  For `u ≥ exp p`,
`√(E2s G u)/u ≤ exp(-p)·(1 + ttIntS G u)`: the factor `1/u ≤ exp(-p)` is bounded on the range of
`exp` over `[p, ∞)`, and `√(E2s) ≤ 1 + ttIntS` is the honest `H⁰`-bound on the slice energy. -/
theorem sqrt_E2s_div_le (G : ℝ → ℝ → ℝ) {p u : ℝ} (hu : Real.exp p ≤ u) :
    Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G u) / u
      ≤ Real.exp (-p) * (1 + Work.EllipticEst.Core.ttIntS G u) := by
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos p) hu
  have hC : (1 : ℝ) / u ≤ Real.exp (-p) := by
    simpa [one_div, Real.exp_neg] using one_div_le_one_div_of_le (Real.exp_pos p) hu
  calc Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G u) / u
      = Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G u) * (1 / u) := by
        rw [div_eq_mul_inv, one_div]
    _ ≤ Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G u) * Real.exp (-p) :=
        mul_le_mul_of_nonneg_left hC (Real.sqrt_nonneg _)
    _ = Real.exp (-p) * Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G u) := by ring
    _ ≤ Real.exp (-p) * (1 + Work.EllipticEst.Core.ttIntS G u) :=
        mul_le_mul_of_nonneg_left (Work.FTS.EllSol.EllPkgAux.sqrt_e2s_le_one_add_ttIntS G hu0)
          (Real.exp_pos (-p)).le

/-- **Integrability on a compact logarithmic window.**  For any `p q : ℝ`, the function
`t ↦ √(E2s G (exp t))` is integrable on `Icc p q`. -/
theorem integrableOn_sqrt_E2s_exp (G : ℝ → ℝ → ℝ)
    (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (p q : ℝ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G (Real.exp t)))
      (Set.Icc p q) MeasureTheory.volume := by
  -- the honest `H⁰`-mass `ttIntS G` is integrable on the `u`-window
  have h1 : MeasureTheory.IntegrableOn (fun u : ℝ => Work.EllipticEst.Core.ttIntS G u)
      (Set.Icc (Real.exp p) (Real.exp q)) MeasureTheory.volume :=
    hF.2.2.1.mono_set (fun u hu => by
      show (0 : ℝ) ≤ u
      exact le_trans (Real.exp_pos p).le hu.1)
  have h2 : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Set.Icc (Real.exp p) (Real.exp q)) MeasureTheory.volume :=
    MeasureTheory.integrableOn_const (C := (1 : ℝ)) (by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  -- the two pieces of the dominating function, and their sum
  have hA : MeasureTheory.IntegrableOn (fun u : ℝ => Real.exp (-p) * (1 : ℝ))
      (Set.Icc (Real.exp p) (Real.exp q)) MeasureTheory.volume :=
    h2.const_mul (Real.exp (-p))
  have hB : MeasureTheory.IntegrableOn
      (fun u : ℝ => Real.exp (-p) * Work.EllipticEst.Core.ttIntS G u)
      (Set.Icc (Real.exp p) (Real.exp q)) MeasureTheory.volume :=
    h1.const_mul (Real.exp (-p))
  have hdom := hA.add hB
  -- measurability of `u ↦ √(E2s G u)/u` on the `u`-window
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun u : ℝ => Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G u) / u)
      (MeasureTheory.volume.restrict (Set.Icc (Real.exp p) (Real.exp q))) :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable
        (Work.FTS.EllSol.EllPkgAux.MollAux.aesmE2s (G := G) (a := Real.exp p)
          (b := Real.exp q) hT.1 (Real.exp_pos p))).div₀
      measurable_id.aestronglyMeasurable
  -- the pointwise domination on the `u`-window
  have hle : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Icc (Real.exp p) (Real.exp q))),
      ‖Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G u) / u‖
        ≤ Real.exp (-p) * 1 + Real.exp (-p) * Work.EllipticEst.Core.ttIntS G u := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun u hu => ?_)
    have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos p) hu.1
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hu0.le)]
    have h := sqrt_E2s_div_le G hu.1
    have e : Real.exp (-p) * (1 + Work.EllipticEst.Core.ttIntS G u)
        = Real.exp (-p) * 1 + Real.exp (-p) * Work.EllipticEst.Core.ttIntS G u := by ring
    rwa [e] at h
  have hint : MeasureTheory.IntegrableOn
      (fun u : ℝ => Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G u) / u)
      (Set.Icc (Real.exp p) (Real.exp q)) MeasureTheory.volume :=
    MeasureTheory.Integrable.mono' hdom hmeas hle
  -- the change of variables `u = exp t` on `[p,q]`
  have hkey := MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    (F := ℝ) (f := Real.exp) (f' := Real.exp) (s := Set.Icc p q)
    (g := fun u : ℝ => Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G u) / u)
    measurableSet_Icc (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn
  rw [Real.image_exp_Icc] at hkey
  have hout := hkey.mp hint
  -- the `exp`-factors cancel
  refine hout.congr_fun (fun x _ => ?_) measurableSet_Icc
  dsimp only
  rw [abs_of_pos (Real.exp_pos x), smul_eq_mul, div_eq_mul_inv]
  have hx : Real.exp x ≠ 0 := Real.exp_ne_zero x
  calc Real.exp x * (Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G (Real.exp x)) * (Real.exp x)⁻¹)
      = Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G (Real.exp x))
          * (Real.exp x * (Real.exp x)⁻¹) := by ring
    _ = Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G (Real.exp x)) * 1 := by
        rw [mul_inv_cancel₀ hx]
    _ = Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G (Real.exp x)) := by ring

theorem localIntegrable_sqrtE2s (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) :
    MeasureTheory.LocallyIntegrable
      (fun t : ℝ => Real.sqrt (Work.FTS.EllSol.EllPkgAux.E2s G (Real.exp t)))
      MeasureTheory.volume := by
  intro x
  exact ⟨Set.Icc (x - 1) (x + 1),
    mem_of_superset (Ioo_mem_nhds (by linarith) (by linarith)) Ioo_subset_Icc_self,
    integrableOn_sqrt_E2s_exp G hT hF (x - 1) (x + 1)⟩

end Work.FTS.EllSol.EllPkgAux.MollDom
