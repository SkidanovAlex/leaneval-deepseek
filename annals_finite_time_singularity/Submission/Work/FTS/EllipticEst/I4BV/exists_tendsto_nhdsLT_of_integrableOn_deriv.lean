import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.I4BV

open MeasureTheory Filter Set
open scoped Topology

/-- **A differentiable function with integrable derivative has a limit at the right endpoint.**

If `f` is differentiable on the open interval `(b - δ, b)` with derivative `f'`, and `f'` is
Lebesgue integrable on `(b - δ, b)`, then `f` has a finite limit as `x → b⁻`.

The proof: pick `c = b - δ/2`.  On `(c, b)` the fundamental theorem of calculus gives
`f x = f c + ∫ t in c..x, f' t`, and the primitive `x ↦ ∫ t in c..x, f' t` is continuous on the
closed interval `[c, b]` (it is an antiderivative in the Lebesgue sense of the integrable
function `f'`).  Hence `f x → f c + ∫ t in c..b, f' t` as `x → b⁻`. -/
theorem exists_tendsto_nhdsLT_of_integrableOn_deriv {f f' : ℝ → ℝ} {b δ : ℝ} (hδ : 0 < δ)
    (hderiv : ∀ x ∈ Set.Ioo (b - δ) b, HasDerivAt f (f' x) x)
    (hint : MeasureTheory.IntegrableOn f' (Set.Ioo (b - δ) b)) :
    ∃ L : ℝ, Filter.Tendsto f (nhdsWithin b (Set.Iio b)) (nhds L) := by
  set c : ℝ := b - δ / 2 with hcdef
  have hcb : c < b := by rw [hcdef]; linarith
  have hbc : b - δ < c := by rw [hcdef]; linarith
  -- integrability of `f'` on `(c, b)` and then on the closed interval `[c, b]`
  have hIoo_c : IntegrableOn f' (Set.Ioo c b) volume :=
    hint.mono_set (Set.Ioo_subset_Ioo_left hbc.le)
  have hIcc : IntegrableOn f' (Set.Icc c b) volume :=
    hIoo_c.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc (a := c) (b := b)).symm
  have hIccu : IntegrableOn f' (Set.uIcc c b) volume := by
    rwa [Set.uIcc_of_le hcb.le]
  -- the primitive `x ↦ ∫ t in c..x, f' t` is continuous on `[c, b]`
  have hcont : ContinuousOn (fun x => ∫ t in c..x, f' t) (Set.Icc c b) := by
    have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) hIccu
    rwa [Set.uIcc_of_le hcb.le] at h
  refine ⟨f c + ∫ t in c..b, f' t, ?_⟩
  -- the limit of the primitive
  have hg : Tendsto (fun x => f c + ∫ t in c..x, f' t) (nhdsWithin b (Set.Iio b))
      (nhds (f c + ∫ t in c..b, f' t)) := by
    have hcw : ContinuousWithinAt (fun x => ∫ t in c..x, f' t) (Set.Icc c b) b :=
      hcont.continuousWithinAt (Set.right_mem_Icc.mpr hcb.le)
    have hle : nhdsWithin b (Set.Iio b) ≤ nhdsWithin b (Set.Icc c b) := by
      rw [← nhdsWithin_Ioo_eq_nhdsLT hcb]
      exact nhdsWithin_mono b Set.Ioo_subset_Icc_self
    exact (hcw.mono_left hle).const_add (f c)
  -- on `(c, b)` the fundamental theorem of calculus identifies `f` with the primitive
  refine hg.congr' ?_
  have hmem : Set.Ioo c b ∈ nhdsWithin b (Set.Iio b) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hcb]
    exact self_mem_nhdsWithin
  filter_upwards [hmem] with x hx
  have hxc : c ≤ x := hx.1.le
  have hFTC : ∫ t in c..x, f' t = f x - f c :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y hy => hderiv y (by
        rw [Set.uIcc_of_le hxc] at hy
        exact ⟨lt_of_lt_of_le hbc hy.1, lt_of_le_of_lt hy.2 hx.2⟩))
      ((show IntegrableOn f' (Set.uIcc c x) volume from by
          rw [Set.uIcc_of_le hxc]
          exact hIcc.mono_set (Set.Icc_subset_Icc le_rfl hx.2.le)).intervalIntegrable)
  linarith [hFTC]

end Work.FTS.EllipticEst.I4BV
