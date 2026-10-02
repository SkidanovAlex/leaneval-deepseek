import Submission.Work.Stems.Hur2c.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The boundary of a degenerate `2`-cube

`∂` of a degenerate `2`-cube is a difference of two *constant* `1`-cubes: the two faces in the
coordinate direction `1 - i` are literally equal (both are `δ`) and cancel in the alternating sum,
and the two faces in the direction `i` are the constants at the endpoints of `δ`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2c

open Work.Stems.Cubical

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The point of `I¹` with coordinate `b` (there is only one coordinate). -/
def pt (b : unitInterval) : IC 1 := fun _ => b

/-- Coordinates of a face of a `2`-cube. -/
theorem faceCM_two (i j : Fin 2) (b : unitInterval) (t : IC 1) :
    (faceCM j b t) i = if i = j then b else t 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [faceCM_apply, faceFun_apply, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same,
      Fin.insertNth_apply_above, Fin.insertNth_apply_below]

/-- The face of a degenerate cube in the degenerate direction is constant. -/
theorem faceCube_degenCube_frozen (i : Fin 2) (b : unitInterval) (δ : C(IC 1, X)) :
    faceCube i b (degenCube i δ) = ContinuousMap.const (IC 1) (δ (pt b)) := by
  ext t
  show δ (proj i (faceCM i b t)) = δ (pt b)
  congr 1
  funext k
  rw [proj_apply, faceCM_two i i b t, if_pos rfl]
  rfl

/-- The faces of a degenerate cube in the *other* direction are the original `1`-cube. -/
theorem faceCube_degenCube_other_apply (i : Fin 2) (b : unitInterval) (δ : C(IC 1, X)) (t : IC 1) :
    (degenCube i δ) (faceCM (1 - i) b t) = δ t := by
  show δ (proj i (faceCM (1 - i) b t)) = δ t
  congr 1
  fin_cases i
  · show proj (0 : Fin 2) (faceCM (1 : Fin 2) b t) = t
    funext k
    rw [proj_apply, faceCM_two 0 1 b t]
    simp only [Fin.isValue, Fin.reduceEq, if_false]
    exact congrArg t (Subsingleton.elim (0 : Fin 1) k)
  · show proj (1 : Fin 2) (faceCM (0 : Fin 2) b t) = t
    funext k
    rw [proj_apply, faceCM_two 1 0 b t]
    simp only [Fin.isValue, Fin.reduceEq, if_false]
    exact congrArg t (Subsingleton.elim (0 : Fin 1) k)

/-- The face of `degenCube 0 δ` in direction `1` is `δ`. -/
theorem faceCube_one_degenCube_zero (b : unitInterval) (δ : C(IC 1, X)) :
    faceCube (1 : Fin 2) b (degenCube (0 : Fin 2) δ) = δ :=
  ContinuousMap.ext fun t => faceCube_degenCube_other_apply (0 : Fin 2) b δ t

/-- The face of `degenCube 1 δ` in direction `0` is `δ`. -/
theorem faceCube_zero_degenCube_one (b : unitInterval) (δ : C(IC 1, X)) :
    faceCube (0 : Fin 2) b (degenCube (1 : Fin 2) δ) = δ :=
  ContinuousMap.ext fun t => faceCube_degenCube_other_apply (1 : Fin 2) b δ t

/-- **The boundary of a degenerate `2`-cube.** -/
theorem degenCube_boundary (δ : C(IC 1, X)) :
    (cubD 1 X (Finsupp.single (degenCube (0 : Fin 2) δ) 1)
        = Finsupp.single (ContinuousMap.const (IC 1) (δ 0)) 1
          - Finsupp.single (ContinuousMap.const (IC 1) (δ 1)) 1)
      ∧ (cubD 1 X (Finsupp.single (degenCube (1 : Fin 2) δ) 1)
        = Finsupp.single (ContinuousMap.const (IC 1) (δ 1)) 1
          - Finsupp.single (ContinuousMap.const (IC 1) (δ 0)) 1) := by
  constructor
  · rw [cubD_single, Fin.sum_univ_two, faceCube_degenCube_frozen 0 0 δ,
      faceCube_degenCube_frozen 0 1 δ, faceCube_one_degenCube_zero 0 δ,
      faceCube_one_degenCube_zero 1 δ]
    norm_num
    rfl
  · rw [cubD_single, Fin.sum_univ_two, faceCube_degenCube_frozen 1 0 δ,
      faceCube_degenCube_frozen 1 1 δ, faceCube_zero_degenCube_one 0 δ,
      faceCube_zero_degenCube_one 1 δ]
    norm_num
    rfl

end

end Work.Stems.Hur2c
