import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR

/-- Continuity on `(0,∞)` of the primitive `z ↦ ∫ t in (0)..z, c t · w t`, for `c ∈ L²(0,∞)`
(only `∫ c² < ∞` is assumed, plus a.e. strong measurability of `c`, since the Bochner integral
returns `0` for non-integrable integrands) and `w` continuous on `(0,∞)`, assuming `c · w` is
integrable on `(0,z)` for every `z > 0`.  Route: `∫ t in (0)..z` is `∫_{Ioc 0 z}`
(`intervalIntegral.integral_of_le`); for `z₀ > 0` and `z` with `|z - z₀| ≤ z₀/2`, split the
difference with `setIntegral_union` and bound `|∫_{(z₀,z)} c w| ≤ M·∫_{(z₀,z)} |c| ≤
M·√(∫_{(z₀,z)} c²)·√|z - z₀|`, where `M` bounds `|w|` on the compact `[z₀/2, 3z₀/2]`
(`IsCompact.exists_bound_of_continuousOn`), Cauchy–Schwarz being applied to `√(c t ²)` and the
constant `1`. -/
theorem contOn_primitive_Ioc {c w : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hw : ContinuousOn w (Set.Ioi 0))
    (hint : ∀ z ∈ Set.Ioi 0,
      MeasureTheory.IntegrableOn (fun t => c t * w t) (Set.Ioc 0 z)) :
    ContinuousOn (fun z => ∫ t in (0 : ℝ)..z, c t * w t) (Set.Ioi 0) := by
  intro z₀ hz₀
  -- Pick `z₁ > z₀`.  The primitive is continuous on the compact segment `[0, z₁]`, which
  -- contains `z₀` in its interior, while `Ioi 0` is a neighbourhood of `z₀`.
  obtain ⟨z₁, hz₀z₁⟩ := exists_gt z₀
  have hz₁ : 0 < z₁ := lt_trans hz₀ hz₀z₁
  -- `IntegrableOn` transfers across the null set `{0}`.
  have hInt : MeasureTheory.IntegrableOn (fun t => c t * w t) (Set.Icc 0 z₁) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hint z₁ hz₁
  -- The set-integral primitive is continuous (dominated convergence).
  have hprim : ContinuousOn (fun x : ℝ => (∫ t in Set.Ioc 0 x, c t * w t : ℝ))
      (Set.Icc 0 z₁) :=
    intervalIntegral.continuousOn_primitive (E := ℝ) (f := fun t => c t * w t)
      (a := 0) (b := z₁) (μ := MeasureTheory.volume) hInt
  -- On `[0, z₁]` the interval integral is the set integral over `Ioc 0 x`.
  have hcongr : Set.EqOn (fun x : ℝ => (∫ t in (0 : ℝ)..x, c t * w t : ℝ))
      (fun x : ℝ => (∫ t in Set.Ioc 0 x, c t * w t : ℝ)) (Set.Icc 0 z₁) := by
    intro x hx
    exact intervalIntegral.integral_of_le (E := ℝ) (f := fun t => c t * w t)
      (μ := MeasureTheory.volume) (a := 0) (b := x) hx.1
  have hcont : ContinuousOn (fun x : ℝ => (∫ t in (0 : ℝ)..x, c t * w t : ℝ))
      (Set.Icc 0 z₁) :=
    hprim.congr hcongr
  exact (hcont.continuousAt (Icc_mem_nhds hz₀ hz₀z₁)).continuousWithinAt

end Work.FTS.H2.ModalSolR
