import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak

open Filter Set MeasureTheory
open scoped Topology

set_option linter.style.haveILetI false

/-- A function on `(0, π/4)` whose derivative is bounded by `M` there has a limit `L` at `0⁺`,
and the limit is approached at least at linear rate: `|u θ - L| ≤ M θ` on `(0, π/8)`.

The existence of `L` is `exists_tendsto_nhdsGT_zero_of_integrableOn_deriv` (the derivative is
bounded, hence integrable on the finite interval); the rate follows by passing to the limit in
the Lipschitz estimate `|u θ - u y| ≤ M |θ - y|` (mean value inequality on the convex set
`(0, π/4)`). -/
theorem sliceLipschitzLeft (u : ℝ → ℝ) (M : ℝ)
    (hder : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), HasDerivAt u (deriv u x) x)
    (hbd : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), |deriv u x| ≤ M) :
    ∃ L : ℝ, Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ∧
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 8), |u θ - L| ≤ M * θ := by
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hpi8 : (0 : ℝ) < Real.pi / 8 := by positivity
  have hpi84 : Real.pi / 8 < Real.pi / 4 := by linarith [Real.pi_pos]
  -- the derivative bound forces `M ≥ 0`
  have hM : 0 ≤ M := by
    have h := hbd (Real.pi / 8) ⟨hpi8, hpi84⟩
    linarith [abs_nonneg (deriv u (Real.pi / 8))]
  -- `deriv u` is integrable on `(0, π/4)`: it is measurable and bounded on a finite interval
  have hint : IntegrableOn (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 4)) := by
    refine IntegrableOn.of_bound (measure_Ioo_lt_top) ?_ M ?_
    · exact (measurable_deriv u).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [Real.norm_eq_abs]
      exact hbd x hx
  -- existence of the limit at `0⁺`
  obtain ⟨L, hL⟩ :=
    Work.FTS.EllipticEst.exists_tendsto_nhdsGT_zero_of_integrableOn_deriv
      (f := u) (f' := deriv u) (δ := Real.pi / 4) hpi4 hder hint
  refine ⟨L, hL, ?_⟩
  -- Lipschitz bound on `(0, π/4)` from the mean value inequality
  have hlip : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 4), ∀ y ∈ Set.Ioo (0 : ℝ) (Real.pi / 4),
      |u x - u y| ≤ M * |x - y| := by
    intro x hx y hy
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := u)
      (s := Set.Ioo (0 : ℝ) (Real.pi / 4)) (C := M)
      (fun t ht => (hder t ht).differentiableAt)
      (fun t ht => by rw [Real.norm_eq_abs]; exact hbd t ht)
      (convex_Ioo (0 : ℝ) (Real.pi / 4)) hx hy
    simpa [Real.norm_eq_abs, abs_sub_comm] using h
  intro θ hθ
  have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 4) := ⟨hθ.1, lt_trans hθ.2 hpi84⟩
  haveI : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot (le_refl (0 : ℝ))
  -- the two sides of the Lipschitz estimate converge as `y → 0⁺`
  have hf1 : Tendsto (fun y : ℝ => |u θ - u y|) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds |u θ - L|) :=
    (hL.const_sub (u θ)).abs
  have hid : Tendsto (fun y : ℝ => y) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hf2 : Tendsto (fun y : ℝ => M * |θ - y|) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (M * θ)) := by
    have h1 : Tendsto (fun y : ℝ => θ - y) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds θ) := by
      simpa using (tendsto_const_nhds.sub hid)
    simpa [abs_of_pos hθ.1] using h1.abs.const_mul M
  have hev : ∀ᶠ y in (nhdsWithin (0 : ℝ) (Set.Ioi 0)), |u θ - u y| ≤ M * |θ - y| := by
    have hmem : Set.Ioo (0 : ℝ) (Real.pi / 8) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
      rw [← nhdsWithin_Ioo_eq_nhdsGT hpi8]
      exact self_mem_nhdsWithin
    filter_upwards [hmem] with y hy
    exact hlip θ hθ' y ⟨hy.1, lt_trans hy.2 hpi84⟩
  exact le_of_tendsto_of_tendsto hf1 hf2 hev

end Work.FTS.EllipticEst.AngAWeak
