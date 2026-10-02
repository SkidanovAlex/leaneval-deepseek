import Mathlib
import Submission.Work.Tubular.Defs
import Submission.Work.Tubular.Gauss

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Shrinking a tubular neighbourhood chart

`Work.Tubular.TubeChart_mono`: a tubular neighbourhood of radius `ε` restricts to one of any
radius `ε' ≤ ε`.  The new tube is cut out inside the old one by the norm of the normal foot:
`U' = {y ∈ U | ‖C.inv y‖ ≤ ε'}`, and the same inverse `C.inv` is reused, since on `U'` the normal
foot already has norm `≤ ε'`, and the tube map is a left inverse of `C.inv` on the whole of `U`.

The only structural point is that the *open* tube at radius `ε'` is open in the ambient space: it is
`openTubeSet E ε ∩ {y | ‖C.inv y‖ < ε'}` (the old open tube minus the norm-`ε'` zone, and
`‖C.inv y‖ < ε'` already forces `y` to lie in the old open tube), an intersection of the open old
tube with an open condition for the function `C.inv`, which is continuous on the old tube.
-/

namespace Work.Tubular

noncomputable section

open scoped Manifold ContDiff Topology
open Function Topology

variable {V : Work.ThomBordism.Man8} {N : ℕ}
variable {E : Work.ThomBordism.PontryaginThom.EmbeddingData V N} {ε : ℝ}

/-- The open tube is monotone in the radius. -/
theorem openTubeSet_mono (E : Work.ThomBordism.PontryaginThom.EmbeddingData V N) {ε ε' : ℝ}
    (h : ε' ≤ ε) : openTubeSet E ε' ⊆ openTubeSet E ε := by
  rintro y ⟨p, hp, rfl⟩
  exact ⟨p, lt_of_lt_of_le hp h, rfl⟩

/-- The open tube of a `TubeChart` at a radius `ε' ≤ ε`, described by the normal foot of `C`:
a point of the tube is in the open tube of radius `ε'` exactly when its normal foot has norm
`< ε'`. -/
theorem TubeChart.openTubeSet_of_le (C : TubeChart E ε) {ε' : ℝ} (hle : ε' ≤ ε) :
    openTubeSet E ε' = {y : Euc N | y ∈ C.U ∧ normalNorm E (C.inv y) < ε'} := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hpε : normalNorm E p ≤ ε := le_of_lt (lt_of_lt_of_le hp hle)
    exact ⟨C.mem_U p hpε, by rw [C.inv_tubeMap p hpε]; exact hp⟩
  · rintro ⟨hyU, hy⟩
    exact ⟨C.inv y, hy, C.tubeMap_inv y hyU⟩

theorem tubeChart_mono {V : Work.ThomBordism.Man8} {N : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V N} {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) {ε' : ℝ} (hε' : 0 < ε') (hle : ε' ≤ ε) :
    Nonempty (Work.Tubular.TubeChart E ε') := by
  classical
  -- `C.inv` is continuous on the old tube, hence so is `y ↦ ‖C.inv y‖`
  have hsub : openTubeSet E ε ⊆ C.U := fun _ hy => C.openTube_subset_U hy
  have hcontO : ContinuousOn (fun y : Euc N => normalNorm E (C.inv y)) (openTubeSet E ε) :=
    (continuous_normalNorm E).comp_continuousOn (C.continuousOn_inv.mono hsub)
  have hcontU : ContinuousOn (fun y : Euc N => normalNorm E (C.inv y)) C.U :=
    (continuous_normalNorm E).comp_continuousOn C.continuousOn_inv
  -- the open tube of radius `ε'` is the old open tube, cut down by the strict inequality
  have hkey : openTubeSet E ε'
      = openTubeSet E ε ∩ (fun y : Euc N => normalNorm E (C.inv y)) ⁻¹' (Set.Iio ε') := by
    rw [C.openTubeSet_of_le hle]
    ext y
    constructor
    · rintro ⟨hyU, hy⟩
      refine ⟨?_, hy⟩
      show y ∈ C.openTube
      rw [C.openTube_eq]
      exact ⟨hyU, lt_of_lt_of_le hy hle⟩
    · rintro ⟨hy, hy'⟩
      exact ⟨C.openTube_subset_U hy, hy'⟩
  refine ⟨{ eps_pos := hε'
            U := {y : Euc N | y ∈ C.U ∧ normalNorm E (C.inv y) ≤ ε'}
            isClosed_U := ?_
            inv := C.inv
            inv_mem := ?_
            tubeMap_inv := ?_
            mem_U := ?_
            inv_tubeMap := ?_
            continuousOn_inv := ?_
            isOpen_openTube := ?_
            contMDiffOn_inv := ?_ }⟩
  · -- the new (closed) tube is closed: it is `C.U` intersected with a closed level condition
    have hUeq : ({y : Euc N | y ∈ C.U ∧ normalNorm E (C.inv y) ≤ ε'} : Set (Euc N))
        = C.U ∩ (fun y : Euc N => normalNorm E (C.inv y)) ⁻¹' (Set.Iic ε') := rfl
    rw [hUeq]
    exact hcontU.preimage_isClosed_of_isClosed C.isClosed_U isClosed_Iic
  · -- the normal foot of a point of the new tube has norm `≤ ε'`
    intro y hy
    exact hy.2
  · -- the tubular map is a right inverse of `C.inv` on the new tube
    intro y hy
    exact C.tubeMap_inv y hy.1
  · -- the closed `ε'`-disc bundle lands in the new tube
    intro p hp
    have hpε : normalNorm E p ≤ ε := le_trans hp hle
    exact ⟨C.mem_U p hpε, by rw [C.inv_tubeMap p hpε]; exact hp⟩
  · -- `C.inv` is a left inverse of the tubular map on the closed `ε'`-disc bundle
    intro p hp
    exact C.inv_tubeMap p (le_trans hp hle)
  · -- continuity is inherited
    exact C.continuousOn_inv.mono (fun _ hy => hy.1)
  · -- openness of the open tube at radius `ε'`
    rw [hkey]
    exact hcontO.isOpen_inter_preimage C.isOpen_openTube isOpen_Iio
  · -- smoothness of the inverse on the smaller open tube
    exact C.contMDiffOn_inv.mono (openTubeSet_mono E hle)

end

end Work.Tubular
