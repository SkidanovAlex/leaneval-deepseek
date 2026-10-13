import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.window_ttIntS_integrable
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.thSlice_window_aesm
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_deriv2_integrableOn
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_deriv2_weighted_integrableOn
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.interval_sq_le_Itheta
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.pth2_slice_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open MeasureTheory Set Filter
open scoped Real Topology

/-! ## The *unweighted* windowed `ttIntS`

`window_ttIntS_integrable` controls the windowed θ-integral of `(∂_θ²G)²·σθ` (the quantity
`ttIntS` itself, and its weighted angular part).  The present file removes the angular weight
`σθ = sin(2θ)^{-η}` from the *inside* of the θ-integral: on the open interval `(0,π/2)` one has
`σθ ≥ 1`, so the unweighted slice integral is at most the weighted one, and the two differ only
on the null set of the endpoints.  Hence the windowed plain θ-integral is integrable in `t`.

The only non-elementary point is the a.e. strong measurability of
`t ↦ if |log z - t| ≤ δ then ∫_θ (∂_θ²G)(exp t,θ)² else 0`: the *joint* integrand
`(t,θ) ↦ 1_{window}(t)·(∂_θ²G)(exp t,θ)²` is a.e. strongly measurable on the product
(`thSlice_window_aesm`), and the θ-integral of a jointly a.e. strongly measurable function is
a.e. strongly measurable in the remaining variable (`AEStronglyMeasurable.integral_prod_right'`).
Moving the (θ-independent) `if` out of the integral is then pure bookkeeping. -/

/-- **The unweighted angular slice integral is dominated by the weighted one.**  For any datum
`G` and radius `u`, if the `σθ`-weighted square of the second angular derivative is integrable
on `Iθ`, then so is the comparison
`∫_θ (∂_θ²G)² ≤ ∫_θ (∂_θ²G)²·σθ`.  The two sides agree on `(0,π/2)` up to the factor
`σθ ≥ 1`, and the endpoints form a null set. -/
lemma theta_slice_le_weighted (G : ℝ → ℝ → ℝ) (u : ℝ)
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.pth (Work.Spaces.pth G) u θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.pth G) u θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.pth G) u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  -- the closed interval `Iθ` carries the same measure as the open one
  have hIθ : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2))).symm
  rw [hIθ]
  refine MeasureTheory.setIntegral_mono_of_nonneg
    (fun θ _ => sq_nonneg _) (fun θ hθ => ?_)
    (hint.mono_set (fun x hx => ⟨hx.1.le, hx.2.le⟩))
  -- on the open interval `σθ ≥ 1`, so `(∂_θ²G)² ≤ (∂_θ²G)²·σθ`
  have h1 : 1 ≤ Work.FTS.EllipticEst.thEta θ := one_le_thEta_of_mem_Ioo hθ
  have hFnn : (0 : ℝ) ≤ (Work.Spaces.pth (Work.Spaces.pth G) u θ) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hFnn (sub_nonneg.mpr h1)]

theorem window_ttIntS_plain_integrable (G : ℝ → ℝ → ℝ)
    (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G)
    (hF : Work.FTS.EllSol.EllPkgAux.FourInts G) (δ z : ℝ) (hδ : 0 < δ) (hz : 0 < z) :
    MeasureTheory.Integrable (fun t : ℝ => if |Real.log z - t| ≤ δ then
        (∫ s in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0) := by
  -- the honesty of the angular second derivative at every radius
  have hHon : Work.EllipticEst.Core.i0Aux.SliceHonestOpen G := hT.2.2.2.2.2.2.2
  -- the *weighted* windowed θ-integral is integrable
  obtain ⟨-, hw2⟩ :=
    window_ttIntS_integrable G hT hF δ z hδ hz
  -- a.e. strong measurability: the joint windowed square is AESM on the product, hence so is
  -- its θ-integral
  have hJoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => if |Real.log z - p.1| ≤ δ then
        (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp p.1) p.2) ^ 2 else 0)
      (MeasureTheory.volume.prod (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    thSlice_window_aesm G hT δ z
  have hCurried := hJoint.integral_prod_right'
  have hconv : (fun t : ℝ => ∫ θ, (if |Real.log z - t| ≤ δ then
        (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) θ) ^ 2 else 0)
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      = fun t : ℝ => if |Real.log z - t| ≤ δ then
          (∫ s in Work.Spaces.Iθ,
            (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0 := by
    funext t
    by_cases h : |Real.log z - t| ≤ δ
    · rw [ite_eq_left h]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ite_eq_left h)
    · rw [ite_eq_right h]
      simp [h]
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => if |Real.log z - t| ≤ δ then
        (∫ s in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2) else 0)
      MeasureTheory.volume :=
    hCurried.congr (Filter.Eventually.of_forall (fun t => congrFun hconv t))
  -- domination by the weighted windowed θ-integral
  refine MeasureTheory.Integrable.mono' hw2 haesm ?_
  filter_upwards with t
  by_cases h : |Real.log z - t| ≤ δ
  · rw [Real.norm_eq_abs, ite_eq_left h, ite_eq_left h]
    have hInt := pth2_slice_integrable G hHon.1 (Real.exp t) (Real.exp_pos t)
    have hcmp := theta_slice_le_weighted G (Real.exp t) hInt
    have hnn : (0 : ℝ) ≤ ∫ s in Work.Spaces.Iθ,
        (Work.Spaces.pth (Work.Spaces.pth G) (Real.exp t) s) ^ 2 :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun s _ => sq_nonneg _)
    rw [abs_of_nonneg hnn]
    exact hcmp
  · rw [Real.norm_eq_abs, ite_eq_right h, ite_eq_right h]
    simp

end Work.FTS.EllSol.EllPkgAux.MollDom
