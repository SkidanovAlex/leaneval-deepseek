import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

theorem contDiffOn_one_integral_left {f : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hf : ContinuousOn f (Set.Ioi 0)) :
    ContDiffOn ℝ 1 (fun t => ∫ z in t..b, f z) (Set.Ioi 0) ∧
      ∀ t ∈ Set.Ioi 0, deriv (fun t => ∫ z in t..b, f z) t = - f t := by
  -- `f` is continuous at every point of the open half-line `(0, ∞)`
  have hct : ∀ x ∈ Set.Ioi (0 : ℝ), ContinuousAt f x :=
    fun x hx => (hf.continuousWithinAt hx).continuousAt (Ioi_mem_nhds hx)
  -- the closed interval between `t > 0` and `b > 0` stays inside `(0, ∞)`
  have hsub : ∀ t ∈ Set.Ioi (0 : ℝ), Set.uIcc t b ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht x hx
    rw [Set.mem_Ioi] at ht
    rw [Set.mem_Ioi]
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩
    · linarith
    · linarith
  -- fundamental theorem of calculus: differentiation in the left endpoint
  have hhas : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun u => ∫ z in u..b, f z) (-f t) t := by
    intro t ht
    have hInt : IntervalIntegrable f (MeasureTheory.volume : MeasureTheory.Measure ℝ) t b :=
      (hf.mono (hsub t ht)).intervalIntegrable
    exact intervalIntegral.integral_hasDerivAt_left hInt
      (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi hct t ht) (hct t ht)
  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ), deriv (fun u => ∫ z in u..b, f z) t = -f t :=
    fun t ht => (hhas t ht).deriv
  refine ⟨?_, hderiv⟩
  rw [contDiffOn_one_iff_derivWithin (𝕜 := ℝ) isOpen_Ioi.uniqueDiffOn]
  refine ⟨fun t ht => (hhas t ht).differentiableAt.differentiableWithinAt, ?_⟩
  refine (hf.neg).congr fun t ht => ?_
  rw [derivWithin_of_isOpen isOpen_Ioi ht, hderiv t ht]
  rfl

end Work.FTS.StrongEps.EComparison
