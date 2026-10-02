import Submission.Work.Stems.Hur2c.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Coordinates of the faces of a `3`-cube (the four instances `T_loop` needs)

`faceCM i b t` is `Fin.insertNth i b t`, so its values at concrete indices are `simp`-computable;
this file records the instances used by the `T_loop` cube `C_k (p) = H (p (1-k), p k)`, where the
*slot* form (an index of the target cube) is what keeps the returned `Fin.castPred`/`Fin.pred` index
from needing a `Fin.ext` bid.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2c

open Work.Stems.Cubical

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The frozen coordinate. -/
theorem faceCM3_frozen (i : Fin 3) (b : unitInterval) (t : IC 2) :
    (faceCM i b t) i = b := faceCM_frozen i b t

/-- The coordinate `1` of the face obtained by freezing coordinate `0`. -/
theorem faceCM3_0_1 (b : unitInterval) (t : IC 2) : (faceCM (0 : Fin 3) b t) 1 = t 0 := by
  simp [faceCM_apply, faceFun_apply, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same,
    Fin.insertNth_apply_above, Fin.insertNth_apply_below]

/-- The coordinate `2` of the face obtained by freezing coordinate `0`. -/
theorem faceCM3_0_2 (b : unitInterval) (t : IC 2) : (faceCM (0 : Fin 3) b t) 2 = t 1 := by
  simp [faceCM_apply, faceFun_apply, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same,
    Fin.insertNth_apply_above, Fin.insertNth_apply_below]

/-- The coordinate `2` of the face obtained by freezing coordinate `1`. -/
theorem faceCM3_1_2 (b : unitInterval) (t : IC 2) : (faceCM (1 : Fin 3) b t) 2 = t 1 := by
  simp [faceCM_apply, faceFun_apply, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same,
    Fin.insertNth_apply_above, Fin.insertNth_apply_below]

/-- The coordinate `0` of the face obtained by freezing coordinate `1`. -/
theorem faceCM3_1_0 (b : unitInterval) (t : IC 2) : (faceCM (1 : Fin 3) b t) 0 = t 0 := by
  simp [faceCM_apply, faceFun_apply, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same,
    Fin.insertNth_apply_above, Fin.insertNth_apply_below]

/-- The coordinate `0` of the face obtained by freezing coordinate `2`. -/
theorem faceCM3_2_0 (b : unitInterval) (t : IC 2) : (faceCM (2 : Fin 3) b t) 0 = t 0 := by
  simp [faceCM_apply, faceFun_apply, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same,
    Fin.insertNth_apply_above, Fin.insertNth_apply_below]

/-- The coordinate `1` of the face obtained by freezing coordinate `2`. -/
theorem faceCM3_2_1 (b : unitInterval) (t : IC 2) : (faceCM (2 : Fin 3) b t) 1 = t 1 := by
  simp [faceCM_apply, faceFun_apply, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same,
    Fin.insertNth_apply_above, Fin.insertNth_apply_below]

end

end Work.Stems.Hur2c
