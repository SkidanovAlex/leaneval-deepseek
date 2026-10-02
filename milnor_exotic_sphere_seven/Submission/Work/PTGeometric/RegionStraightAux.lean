import Mathlib
import Submission.Work.PTGeometric.RegionStraightChart

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners Classical

namespace Work.PTGeometric

noncomputable section

variable {k : ℕ}

theorem strAux_smoothOn (ψ : Mod k → ℝ) {V : Set (Mod k)} (hV : IsOpen V)
    (hψsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Mod k => ψ (tailVec z)) V) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Mod k => strAux ψ z) V := by
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Mod k => ψ (tailVec z) • (eZero : Mod k)) V := hψsm.smul_const _
  refine (contDiffOn_id.sub h1).congr fun z _ => ?_
  rw [strAux_eq]
  rfl

theorem modelWithCorners_halfSpace_symm_eq {n : ℕ} [NeZero n] {z : EuclideanSpace ℝ (Fin n)}
    (hz : 0 ≤ z.ofLp 0) :
    (𝓡∂ n).symm z = (⟨z, hz⟩ : EuclideanHalfSpace n) := by
  rw [modelWithCornersEuclideanHalfSpace_symm_apply z]
  congr 1
  rw [max_eq_left hz, update_eq_self, WithLp.toLp_ofLp]

theorem modelWithCorners_halfSpace_symm_coe {n : ℕ} [NeZero n] {v : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ Set.range (𝓡∂ n)) :
    (((𝓡∂ n).symm v).1 : EuclideanSpace ℝ (Fin n)) = v := by
  have hv0 : 0 ≤ v.ofLp 0 := by rwa [range_modelWithCornersEuclideanHalfSpace] at hv
  rw [modelWithCorners_halfSpace_symm_eq hv0]

namespace WeakRegion

namespace RegionSetupWeak

variable {k : ℕ} (S : RegionSetupWeak k)

theorem chartAt_extend_apply_of_mem {m : S.Region} {w : S.Region} (hw : w ∈ S.chartSource m) :
    (S.chartAt m).extend (𝓡∂ (8 + k + 1)) w = S.T m (S.domExt m w.1) := by
  rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, S.chartAt_apply_of_mem m hw]
  rfl

theorem extChartAt_self_source (u : Half k) :
    (extChartAt (𝓡∂ (8 + k + 1)) u).source = univ := by
  rw [extChartAt, OpenPartialHomeomorph.extend_source, chartAt_self_eq]
  rfl

theorem extChartAt_self_symm_apply {u : Half k} {v : Mod k} :
    (extChartAt (𝓡∂ (8 + k + 1)) u).symm v = (𝓡∂ (8 + k + 1)).symm v := by
  rw [extChartAt, OpenPartialHomeomorph.extend_coe_symm, chartAt_self_eq]
  rfl

end RegionSetupWeak

end WeakRegion

end

end Work.PTGeometric
