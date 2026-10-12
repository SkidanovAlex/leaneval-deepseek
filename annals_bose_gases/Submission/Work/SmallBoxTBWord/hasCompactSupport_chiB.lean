import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.SmallBoxTBWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxTBWord

open Submission.BoseGases

/-- The sliding cutoff `χ_B = chiB ℓ d u` has compact support for `ℓ > 0`,
`d > 0`: it is supported in the compact centred cube `acube ℓ` — indeed
`chiB ℓ d u x = χ(x/ℓ)·χ(x/(ℓd) − u)`, so `chiB ℓ d u x ≠ 0` forces the first
factor `chiScale ℓ x ≠ 0`, whence `x ∈ acube ℓ` (`chiScale_mem_acube`). -/
theorem hasCompactSupport_chiB {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : EuclideanSpace ℝ (Fin 3)) : HasCompactSupport (Submission.BoseGases.chiB ℓ d u) := by
  refine HasCompactSupport.of_support_subset_isCompact (Submission.BoseGases.acube_compact hℓ) ?_
  intro x hx
  exact Submission.BoseGases.chiScale_mem_acube hℓ
    (fun h => hx (by simp [Submission.BoseGases.chiB, h]))

end Work.SmallBoxTBWord
