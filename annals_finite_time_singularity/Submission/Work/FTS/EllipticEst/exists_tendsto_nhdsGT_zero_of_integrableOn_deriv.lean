import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open MeasureTheory Filter Set
open scoped Topology

/-- **A differentiable function with integrable derivative has a limit at the left endpoint.**

If `f` is differentiable on the open interval `(0, δ)` with derivative `f'`, and `f'` is
Lebesgue integrable on `(0, δ)`, then `f` has a finite limit as `x → 0⁺`.

The proof: pick `c = δ/2`.  On `(0, c)` the fundamental theorem of calculus gives
`f x = f c - ∫ t in x..c, f' t`, and the primitive `x ↦ ∫ t in x..c, f' t` is continuous on
the closed interval `[0, c]` (it is an antiderivative in the Lebesgue sense of the integrable
function `f'`).  Hence `f x → f c - ∫ t in 0..c, f' t` as `x → 0⁺`. -/
theorem exists_tendsto_nhdsGT_zero_of_integrableOn_deriv {f f' : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) δ, HasDerivAt f (f' x) x)
    (hint : MeasureTheory.IntegrableOn f' (Set.Ioo (0 : ℝ) δ)) :
    ∃ L : ℝ, Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L) := by
  set c : ℝ := δ / 2 with hcdef
  have hc0 : 0 < c := by rw [hcdef]; linarith
  have hcδ : c < δ := by rw [hcdef]; linarith
  -- integrability of `f'` on `(0, c)` and then on the closed interval `[0, c]`
  have hIoo_c : IntegrableOn f' (Set.Ioo (0 : ℝ) c) volume :=
    hint.mono_set (Set.Ioo_subset_Ioo_right hcδ.le)
  have hIcc : IntegrableOn f' (Set.Icc (0 : ℝ) c) volume :=
    hIoo_c.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := c)).symm
  -- the primitive `x ↦ ∫ t in x..c, f' t` is continuous on `[0, c]`
  have hcont_u : ContinuousOn (fun x => ∫ t in x..c, f' t) (Set.uIcc (0 : ℝ) c) :=
    intervalIntegral.continuousOn_primitive_interval_left (by
      rw [Set.uIcc_of_le hc0.le]; exact hIcc)
  have hcont : ContinuousOn (fun x => ∫ t in x..c, f' t) (Set.Icc (0 : ℝ) c) := by
    rwa [Set.uIcc_of_le hc0.le] at hcont_u
  refine ⟨f c - ∫ t in (0 : ℝ)..c, f' t, ?_⟩
  -- the limit of the primitive
  have hg : Tendsto (fun x => f c - ∫ t in x..c, f' t) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (f c - ∫ t in (0 : ℝ)..c, f' t)) := by
    have hcw : ContinuousWithinAt (fun x => ∫ t in x..c, f' t) (Set.Icc (0 : ℝ) c) 0 :=
      hcont.continuousWithinAt (Set.left_mem_Icc.mpr hc0.le)
    have hle : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhdsWithin (0 : ℝ) (Set.Icc (0 : ℝ) c) := by
      rw [← nhdsWithin_Ioo_eq_nhdsGT hc0]
      exact nhdsWithin_mono 0 Set.Ioo_subset_Icc_self
    exact (hcw.mono_left hle).const_sub (f c)
  -- on `(0, c)` the fundamental theorem of calculus identifies `f` with the primitive
  refine hg.congr' ?_
  have hmem : Set.Ioo (0 : ℝ) c ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT hc0]
    exact self_mem_nhdsWithin
  filter_upwards [hmem] with x hx
  have hxc : x ≤ c := hx.2.le
  have hFTC : ∫ t in x..c, f' t = f c - f x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y hy => hderiv y (by
        have hy' : y ∈ Set.Icc x c := by rwa [Set.uIcc_of_le hxc] at hy
        exact ⟨lt_of_lt_of_le hx.1 hy'.1, lt_of_le_of_lt hy'.2 hcδ⟩))
      ((show IntegrableOn f' (Set.uIcc x c) volume from by
          rw [Set.uIcc_of_le hxc]
          exact hIcc.mono_set (Set.Icc_subset_Icc hx.1.le le_rfl)).intervalIntegrable)
  linarith [hFTC]

end Work.FTS.EllipticEst
