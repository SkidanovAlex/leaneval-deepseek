import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Continuity

open Filter Topology

namespace Commons.Analysis.Normed

lemma inv_tendsto_zero_comap_norm_atTop {R : Type*} [NormedDivisionRing R] :
    Tendsto (fun z : R => z⁻¹) (comap (fun z : R => ‖z‖) atTop) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hcomp : Tendsto (fun z : R => (‖z‖ : ℝ)⁻¹) (comap (fun z : R => ‖z‖) atTop) (𝓝 (0 : ℝ)) := by
    exact (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp tendsto_comap
  convert hcomp using 1
  funext z
  exact norm_inv z

end Commons.Analysis.Normed