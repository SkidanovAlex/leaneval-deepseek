import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Normed.Operator

theorem tendsto_inverse_of_tendsto_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {ι : Type*} {l : Filter ι} {f : ι → E →L[ℝ] E}
    (hf : Filter.Tendsto f l (nhds 1)) :
    Filter.Tendsto (fun i => ContinuousLinearMap.inverse (f i)) l (nhds 1) := by
  have hcont : ContinuousAt Ring.inverse (1 : E →L[ℝ] E) :=
    NormedRing.inverse_continuousAt (1 : (E →L[ℝ] E)ˣ)
  have h : Filter.Tendsto (fun i => Ring.inverse (f i)) l (nhds (Ring.inverse 1)) :=
    hcont.tendsto.comp hf
  rw [Ring.inverse_one] at h
  simpa only [ContinuousLinearMap.ringInverse_eq_inverse] using h

end Commons.Analysis.Normed.Operator