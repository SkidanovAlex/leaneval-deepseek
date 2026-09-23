import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Commons.Analysis.Calculus

theorem contDiffAt_one_of_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f f' : ℝ → F} {x : ℝ} {s : Set ℝ} (hs : s ∈ nhds x)
    (hf : ∀ y ∈ s, HasDerivAt f (f' y) y) (hf' : ContinuousOn f' s) :
    ContDiffAt ℝ 1 f x := by
  obtain ⟨u, hus, hu_open, hxu⟩ := mem_nhds_iff.mp hs
  rw [contDiffAt_one_iff]
  refine ⟨fun y => ContinuousLinearMap.toSpanSingleton ℝ (f' y), u, hu_open.mem_nhds hxu, ?_, ?_⟩
  · exact (ContinuousLinearMap.toSpanSingletonLIE ℝ F).continuous.comp_continuousOn' (hf'.mono hus)
  · intro y hy
    exact (hf y (hus hy)).hasFDerivAt

end Commons.Analysis.Calculus