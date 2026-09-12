import Mathlib

open Filter
open scoped Topology

namespace Commons.Analysis.Complex

lemma norm_one_sub_smul_inv_tendsto_one (a : ℂ) :
    Tendsto (fun z : ℂ => ‖1 - a * z⁻¹‖) (comap (fun z : ℂ => ‖z‖) atTop) (𝓝 1) := by
  rw [comap_norm_atTop]
  have h_inv₀ : Tendsto (fun z : ℂ => z⁻¹) (Bornology.cobounded ℂ) (𝓝 0) :=
    Filter.tendsto_inv₀_cobounded
  have h_mul : Tendsto (fun z : ℂ => a * z⁻¹) (Bornology.cobounded ℂ) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul h_inv₀)
  have h_sub : Tendsto (fun z : ℂ => 1 - a * z⁻¹) (Bornology.cobounded ℂ) (𝓝 1) := by
    simpa using (tendsto_const_nhds.sub h_mul)
  simpa using h_sub.norm

end Commons.Analysis.Complex
