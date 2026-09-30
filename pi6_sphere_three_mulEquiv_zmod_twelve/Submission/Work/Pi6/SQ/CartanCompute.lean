import Mathlib
import Submission.Work.Pi6.SQ.CartanDefs
import Submission.Work.Cohomology.cup1Identity
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQ

noncomputable section

open Work.Cohomology

variable (X : SSet) (x : Cochain F2 X 2) (τ : X _⦋6⦌)

/-! ## Part 1: the faces of the seven `5`-faces `τ|k` (the outer expansion of `δH`) -/

/-- `F012` of `τ|0` -/
lemma ev_F012_0 :
    genEval F2 X x (X.map F012.op (X.δ (0 : Fin 7) τ)) = Fv X x τ 1 2 3 := by
  have hm : F012 ≫ SimplexCategory.δ (0 : Fin 7) = inc6 1 2 3 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F013` of `τ|0` -/
lemma ev_F013_0 :
    genEval F2 X x (X.map F013.op (X.δ (0 : Fin 7) τ)) = Fv X x τ 1 2 4 := by
  have hm : F013 ≫ SimplexCategory.δ (0 : Fin 7) = inc6 1 2 4 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F023` of `τ|0` -/
lemma ev_F023_0 :
    genEval F2 X x (X.map F023.op (X.δ (0 : Fin 7) τ)) = Fv X x τ 1 3 4 := by
  have hm : F023 ≫ SimplexCategory.δ (0 : Fin 7) = inc6 1 3 4 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F024` of `τ|0` -/
lemma ev_F024_0 :
    genEval F2 X x (X.map F024.op (X.δ (0 : Fin 7) τ)) = Fv X x τ 1 3 5 := by
  have hm : F024 ≫ SimplexCategory.δ (0 : Fin 7) = inc6 1 3 5 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F025` of `τ|0` -/
lemma ev_F025_0 :
    genEval F2 X x (X.map F025.op (X.δ (0 : Fin 7) τ)) = Fv X x τ 1 3 6 := by
  have hm : F025 ≫ SimplexCategory.δ (0 : Fin 7) = inc6 1 3 6 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F034` of `τ|0` -/
lemma ev_F034_0 :
    genEval F2 X x (X.map F034.op (X.δ (0 : Fin 7) τ)) = Fv X x τ 1 4 5 := by
  have hm : F034 ≫ SimplexCategory.δ (0 : Fin 7) = inc6 1 4 5 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F035` of `τ|0` -/
lemma ev_F035_0 :
    genEval F2 X x (X.map F035.op (X.δ (0 : Fin 7) τ)) = Fv X x τ 1 4 6 := by
  have hm : F035 ≫ SimplexCategory.δ (0 : Fin 7) = inc6 1 4 6 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F045` of `τ|0` -/
lemma ev_F045_0 :
    genEval F2 X x (X.map F045.op (X.δ (0 : Fin 7) τ)) = Fv X x τ 1 5 6 := by
  have hm : F045 ≫ SimplexCategory.δ (0 : Fin 7) = inc6 1 5 6 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F012` of `τ|1` -/
lemma ev_F012_1 :
    genEval F2 X x (X.map F012.op (X.δ (1 : Fin 7) τ)) = Fv X x τ 0 2 3 := by
  have hm : F012 ≫ SimplexCategory.δ (1 : Fin 7) = inc6 0 2 3 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F013` of `τ|1` -/
lemma ev_F013_1 :
    genEval F2 X x (X.map F013.op (X.δ (1 : Fin 7) τ)) = Fv X x τ 0 2 4 := by
  have hm : F013 ≫ SimplexCategory.δ (1 : Fin 7) = inc6 0 2 4 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F023` of `τ|1` -/
lemma ev_F023_1 :
    genEval F2 X x (X.map F023.op (X.δ (1 : Fin 7) τ)) = Fv X x τ 0 3 4 := by
  have hm : F023 ≫ SimplexCategory.δ (1 : Fin 7) = inc6 0 3 4 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F024` of `τ|1` -/
lemma ev_F024_1 :
    genEval F2 X x (X.map F024.op (X.δ (1 : Fin 7) τ)) = Fv X x τ 0 3 5 := by
  have hm : F024 ≫ SimplexCategory.δ (1 : Fin 7) = inc6 0 3 5 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F025` of `τ|1` -/
lemma ev_F025_1 :
    genEval F2 X x (X.map F025.op (X.δ (1 : Fin 7) τ)) = Fv X x τ 0 3 6 := by
  have hm : F025 ≫ SimplexCategory.δ (1 : Fin 7) = inc6 0 3 6 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F034` of `τ|1` -/
lemma ev_F034_1 :
    genEval F2 X x (X.map F034.op (X.δ (1 : Fin 7) τ)) = Fv X x τ 0 4 5 := by
  have hm : F034 ≫ SimplexCategory.δ (1 : Fin 7) = inc6 0 4 5 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F035` of `τ|1` -/
lemma ev_F035_1 :
    genEval F2 X x (X.map F035.op (X.δ (1 : Fin 7) τ)) = Fv X x τ 0 4 6 := by
  have hm : F035 ≫ SimplexCategory.δ (1 : Fin 7) = inc6 0 4 6 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F045` of `τ|1` -/
lemma ev_F045_1 :
    genEval F2 X x (X.map F045.op (X.δ (1 : Fin 7) τ)) = Fv X x τ 0 5 6 := by
  have hm : F045 ≫ SimplexCategory.δ (1 : Fin 7) = inc6 0 5 6 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F012` of `τ|2` -/
lemma ev_F012_2 :
    genEval F2 X x (X.map F012.op (X.δ (2 : Fin 7) τ)) = Fv X x τ 0 1 3 := by
  have hm : F012 ≫ SimplexCategory.δ (2 : Fin 7) = inc6 0 1 3 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F013` of `τ|2` -/
lemma ev_F013_2 :
    genEval F2 X x (X.map F013.op (X.δ (2 : Fin 7) τ)) = Fv X x τ 0 1 4 := by
  have hm : F013 ≫ SimplexCategory.δ (2 : Fin 7) = inc6 0 1 4 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F023` of `τ|2` -/
lemma ev_F023_2 :
    genEval F2 X x (X.map F023.op (X.δ (2 : Fin 7) τ)) = Fv X x τ 0 3 4 := by
  have hm : F023 ≫ SimplexCategory.δ (2 : Fin 7) = inc6 0 3 4 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F024` of `τ|2` -/
lemma ev_F024_2 :
    genEval F2 X x (X.map F024.op (X.δ (2 : Fin 7) τ)) = Fv X x τ 0 3 5 := by
  have hm : F024 ≫ SimplexCategory.δ (2 : Fin 7) = inc6 0 3 5 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F025` of `τ|2` -/
lemma ev_F025_2 :
    genEval F2 X x (X.map F025.op (X.δ (2 : Fin 7) τ)) = Fv X x τ 0 3 6 := by
  have hm : F025 ≫ SimplexCategory.δ (2 : Fin 7) = inc6 0 3 6 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F034` of `τ|2` -/
lemma ev_F034_2 :
    genEval F2 X x (X.map F034.op (X.δ (2 : Fin 7) τ)) = Fv X x τ 0 4 5 := by
  have hm : F034 ≫ SimplexCategory.δ (2 : Fin 7) = inc6 0 4 5 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F035` of `τ|2` -/
lemma ev_F035_2 :
    genEval F2 X x (X.map F035.op (X.δ (2 : Fin 7) τ)) = Fv X x τ 0 4 6 := by
  have hm : F035 ≫ SimplexCategory.δ (2 : Fin 7) = inc6 0 4 6 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F045` of `τ|2` -/
lemma ev_F045_2 :
    genEval F2 X x (X.map F045.op (X.δ (2 : Fin 7) τ)) = Fv X x τ 0 5 6 := by
  have hm : F045 ≫ SimplexCategory.δ (2 : Fin 7) = inc6 0 5 6 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F012` of `τ|3` -/
lemma ev_F012_3 :
    genEval F2 X x (X.map F012.op (X.δ (3 : Fin 7) τ)) = Fv X x τ 0 1 2 := by
  have hm : F012 ≫ SimplexCategory.δ (3 : Fin 7) = inc6 0 1 2 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F013` of `τ|3` -/
lemma ev_F013_3 :
    genEval F2 X x (X.map F013.op (X.δ (3 : Fin 7) τ)) = Fv X x τ 0 1 4 := by
  have hm : F013 ≫ SimplexCategory.δ (3 : Fin 7) = inc6 0 1 4 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F023` of `τ|3` -/
lemma ev_F023_3 :
    genEval F2 X x (X.map F023.op (X.δ (3 : Fin 7) τ)) = Fv X x τ 0 2 4 := by
  have hm : F023 ≫ SimplexCategory.δ (3 : Fin 7) = inc6 0 2 4 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F024` of `τ|3` -/
lemma ev_F024_3 :
    genEval F2 X x (X.map F024.op (X.δ (3 : Fin 7) τ)) = Fv X x τ 0 2 5 := by
  have hm : F024 ≫ SimplexCategory.δ (3 : Fin 7) = inc6 0 2 5 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F025` of `τ|3` -/
lemma ev_F025_3 :
    genEval F2 X x (X.map F025.op (X.δ (3 : Fin 7) τ)) = Fv X x τ 0 2 6 := by
  have hm : F025 ≫ SimplexCategory.δ (3 : Fin 7) = inc6 0 2 6 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F034` of `τ|3` -/
lemma ev_F034_3 :
    genEval F2 X x (X.map F034.op (X.δ (3 : Fin 7) τ)) = Fv X x τ 0 4 5 := by
  have hm : F034 ≫ SimplexCategory.δ (3 : Fin 7) = inc6 0 4 5 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F035` of `τ|3` -/
lemma ev_F035_3 :
    genEval F2 X x (X.map F035.op (X.δ (3 : Fin 7) τ)) = Fv X x τ 0 4 6 := by
  have hm : F035 ≫ SimplexCategory.δ (3 : Fin 7) = inc6 0 4 6 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F045` of `τ|3` -/
lemma ev_F045_3 :
    genEval F2 X x (X.map F045.op (X.δ (3 : Fin 7) τ)) = Fv X x τ 0 5 6 := by
  have hm : F045 ≫ SimplexCategory.δ (3 : Fin 7) = inc6 0 5 6 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F012` of `τ|4` -/
lemma ev_F012_4 :
    genEval F2 X x (X.map F012.op (X.δ (4 : Fin 7) τ)) = Fv X x τ 0 1 2 := by
  have hm : F012 ≫ SimplexCategory.δ (4 : Fin 7) = inc6 0 1 2 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F013` of `τ|4` -/
lemma ev_F013_4 :
    genEval F2 X x (X.map F013.op (X.δ (4 : Fin 7) τ)) = Fv X x τ 0 1 3 := by
  have hm : F013 ≫ SimplexCategory.δ (4 : Fin 7) = inc6 0 1 3 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F023` of `τ|4` -/
lemma ev_F023_4 :
    genEval F2 X x (X.map F023.op (X.δ (4 : Fin 7) τ)) = Fv X x τ 0 2 3 := by
  have hm : F023 ≫ SimplexCategory.δ (4 : Fin 7) = inc6 0 2 3 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F024` of `τ|4` -/
lemma ev_F024_4 :
    genEval F2 X x (X.map F024.op (X.δ (4 : Fin 7) τ)) = Fv X x τ 0 2 5 := by
  have hm : F024 ≫ SimplexCategory.δ (4 : Fin 7) = inc6 0 2 5 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F025` of `τ|4` -/
lemma ev_F025_4 :
    genEval F2 X x (X.map F025.op (X.δ (4 : Fin 7) τ)) = Fv X x τ 0 2 6 := by
  have hm : F025 ≫ SimplexCategory.δ (4 : Fin 7) = inc6 0 2 6 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F034` of `τ|4` -/
lemma ev_F034_4 :
    genEval F2 X x (X.map F034.op (X.δ (4 : Fin 7) τ)) = Fv X x τ 0 3 5 := by
  have hm : F034 ≫ SimplexCategory.δ (4 : Fin 7) = inc6 0 3 5 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F035` of `τ|4` -/
lemma ev_F035_4 :
    genEval F2 X x (X.map F035.op (X.δ (4 : Fin 7) τ)) = Fv X x τ 0 3 6 := by
  have hm : F035 ≫ SimplexCategory.δ (4 : Fin 7) = inc6 0 3 6 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F045` of `τ|4` -/
lemma ev_F045_4 :
    genEval F2 X x (X.map F045.op (X.δ (4 : Fin 7) τ)) = Fv X x τ 0 5 6 := by
  have hm : F045 ≫ SimplexCategory.δ (4 : Fin 7) = inc6 0 5 6 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F012` of `τ|5` -/
lemma ev_F012_5 :
    genEval F2 X x (X.map F012.op (X.δ (5 : Fin 7) τ)) = Fv X x τ 0 1 2 := by
  have hm : F012 ≫ SimplexCategory.δ (5 : Fin 7) = inc6 0 1 2 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F013` of `τ|5` -/
lemma ev_F013_5 :
    genEval F2 X x (X.map F013.op (X.δ (5 : Fin 7) τ)) = Fv X x τ 0 1 3 := by
  have hm : F013 ≫ SimplexCategory.δ (5 : Fin 7) = inc6 0 1 3 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F023` of `τ|5` -/
lemma ev_F023_5 :
    genEval F2 X x (X.map F023.op (X.δ (5 : Fin 7) τ)) = Fv X x τ 0 2 3 := by
  have hm : F023 ≫ SimplexCategory.δ (5 : Fin 7) = inc6 0 2 3 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F024` of `τ|5` -/
lemma ev_F024_5 :
    genEval F2 X x (X.map F024.op (X.δ (5 : Fin 7) τ)) = Fv X x τ 0 2 4 := by
  have hm : F024 ≫ SimplexCategory.δ (5 : Fin 7) = inc6 0 2 4 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F025` of `τ|5` -/
lemma ev_F025_5 :
    genEval F2 X x (X.map F025.op (X.δ (5 : Fin 7) τ)) = Fv X x τ 0 2 6 := by
  have hm : F025 ≫ SimplexCategory.δ (5 : Fin 7) = inc6 0 2 6 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F034` of `τ|5` -/
lemma ev_F034_5 :
    genEval F2 X x (X.map F034.op (X.δ (5 : Fin 7) τ)) = Fv X x τ 0 3 4 := by
  have hm : F034 ≫ SimplexCategory.δ (5 : Fin 7) = inc6 0 3 4 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F035` of `τ|5` -/
lemma ev_F035_5 :
    genEval F2 X x (X.map F035.op (X.δ (5 : Fin 7) τ)) = Fv X x τ 0 3 6 := by
  have hm : F035 ≫ SimplexCategory.δ (5 : Fin 7) = inc6 0 3 6 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F045` of `τ|5` -/
lemma ev_F045_5 :
    genEval F2 X x (X.map F045.op (X.δ (5 : Fin 7) τ)) = Fv X x τ 0 4 6 := by
  have hm : F045 ≫ SimplexCategory.δ (5 : Fin 7) = inc6 0 4 6 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F012` of `τ|6` -/
lemma ev_F012_6 :
    genEval F2 X x (X.map F012.op (X.δ (6 : Fin 7) τ)) = Fv X x τ 0 1 2 := by
  have hm : F012 ≫ SimplexCategory.δ (6 : Fin 7) = inc6 0 1 2 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F013` of `τ|6` -/
lemma ev_F013_6 :
    genEval F2 X x (X.map F013.op (X.δ (6 : Fin 7) τ)) = Fv X x τ 0 1 3 := by
  have hm : F013 ≫ SimplexCategory.δ (6 : Fin 7) = inc6 0 1 3 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F023` of `τ|6` -/
lemma ev_F023_6 :
    genEval F2 X x (X.map F023.op (X.δ (6 : Fin 7) τ)) = Fv X x τ 0 2 3 := by
  have hm : F023 ≫ SimplexCategory.δ (6 : Fin 7) = inc6 0 2 3 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F024` of `τ|6` -/
lemma ev_F024_6 :
    genEval F2 X x (X.map F024.op (X.δ (6 : Fin 7) τ)) = Fv X x τ 0 2 4 := by
  have hm : F024 ≫ SimplexCategory.δ (6 : Fin 7) = inc6 0 2 4 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F025` of `τ|6` -/
lemma ev_F025_6 :
    genEval F2 X x (X.map F025.op (X.δ (6 : Fin 7) τ)) = Fv X x τ 0 2 5 := by
  have hm : F025 ≫ SimplexCategory.δ (6 : Fin 7) = inc6 0 2 5 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F034` of `τ|6` -/
lemma ev_F034_6 :
    genEval F2 X x (X.map F034.op (X.δ (6 : Fin 7) τ)) = Fv X x τ 0 3 4 := by
  have hm : F034 ≫ SimplexCategory.δ (6 : Fin 7) = inc6 0 3 4 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F035` of `τ|6` -/
lemma ev_F035_6 :
    genEval F2 X x (X.map F035.op (X.δ (6 : Fin 7) τ)) = Fv X x τ 0 3 5 := by
  have hm : F035 ≫ SimplexCategory.δ (6 : Fin 7) = inc6 0 3 5 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]

/-- `F045` of `τ|6` -/
lemma ev_F045_6 :
    genEval F2 X x (X.map F045.op (X.δ (6 : Fin 7) τ)) = Fv X x τ 0 4 5 := by
  have hm : F045 ≫ SimplexCategory.δ (6 : Fin 7) = inc6 0 4 5 (by decide) (by decide) (by decide) := by
    refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    fin_cases i <;> decide
  rw [SimplicialObject.δ_def, map_op_comp, hm, Fv_eq]


/-! ## Part 2: the value of `x ⌣ x` on the four-simplexes `(cup2U 4 4 a (b+1)) τ` and
`(cup2V 4 4 a (b+1)) τ` -/

/-- The value of `x ⌣ x` on the four-simplex `(cup2U 4 4 0 1) τ` -/
lemma ev_xxU_0_0 :
    genEval F2 X (cup F2 X x x)
        (X.map (cup2U 4 4 ((0 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
      = Fv X x τ 0 1 2 * Fv X x τ 2 3 4 := by
  rw [cup_apply_2_2]
  have h1 : X.map (frontIncl 2 4 (by omega)).op
      (X.map (cup2U 4 4 ((0 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 0 1 2 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : frontIncl 2 4 (by omega) ≫ cup2U 4 4 ((0 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 0 1 2 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h2 : X.map (backIncl 2 2).op
      (X.map (cup2U 4 4 ((0 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 2 3 4 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : backIncl 2 2 ≫ cup2U 4 4 ((0 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 2 3 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  rw [h1, h2, Fv_eq, Fv_eq]

/-- The value of `x ⌣ x` on the four-simplex `(cup2V 4 4 0 1) τ` -/
lemma ev_xxV_0_0 :
    genEval F2 X (cup F2 X x x)
        (X.map (cup2V 4 4 ((0 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
      = Fv X x τ 0 1 4 * Fv X x τ 4 5 6 := by
  rw [cup_apply_2_2]
  have h1 : X.map (frontIncl 2 4 (by omega)).op
      (X.map (cup2V 4 4 ((0 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 0 1 4 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : frontIncl 2 4 (by omega) ≫ cup2V 4 4 ((0 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 0 1 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h2 : X.map (backIncl 2 2).op
      (X.map (cup2V 4 4 ((0 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 4 5 6 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : backIncl 2 2 ≫ cup2V 4 4 ((0 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 4 5 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  rw [h1, h2, Fv_eq, Fv_eq]

/-- The value of `x ⌣ x` on the four-simplex `(cup2U 4 4 0 2) τ` -/
lemma ev_xxU_0_1 :
    genEval F2 X (cup F2 X x x)
        (X.map (cup2U 4 4 ((0 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
      = Fv X x τ 0 2 3 * Fv X x τ 3 4 5 := by
  rw [cup_apply_2_2]
  have h1 : X.map (frontIncl 2 4 (by omega)).op
      (X.map (cup2U 4 4 ((0 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 0 2 3 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : frontIncl 2 4 (by omega) ≫ cup2U 4 4 ((0 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 0 2 3 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h2 : X.map (backIncl 2 2).op
      (X.map (cup2U 4 4 ((0 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 3 4 5 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : backIncl 2 2 ≫ cup2U 4 4 ((0 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 3 4 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  rw [h1, h2, Fv_eq, Fv_eq]

/-- The value of `x ⌣ x` on the four-simplex `(cup2V 4 4 0 2) τ` -/
lemma ev_xxV_0_1 :
    genEval F2 X (cup F2 X x x)
        (X.map (cup2V 4 4 ((0 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
      = Fv X x τ 0 1 2 * Fv X x τ 2 5 6 := by
  rw [cup_apply_2_2]
  have h1 : X.map (frontIncl 2 4 (by omega)).op
      (X.map (cup2V 4 4 ((0 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 0 1 2 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : frontIncl 2 4 (by omega) ≫ cup2V 4 4 ((0 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 0 1 2 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h2 : X.map (backIncl 2 2).op
      (X.map (cup2V 4 4 ((0 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 2 5 6 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : backIncl 2 2 ≫ cup2V 4 4 ((0 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 2 5 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  rw [h1, h2, Fv_eq, Fv_eq]

/-- The value of `x ⌣ x` on the four-simplex `(cup2U 4 4 0 3) τ` -/
lemma ev_xxU_0_2 :
    genEval F2 X (cup F2 X x x)
        (X.map (cup2U 4 4 ((0 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
      = Fv X x τ 0 3 4 * Fv X x τ 4 5 6 := by
  rw [cup_apply_2_2]
  have h1 : X.map (frontIncl 2 4 (by omega)).op
      (X.map (cup2U 4 4 ((0 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 0 3 4 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : frontIncl 2 4 (by omega) ≫ cup2U 4 4 ((0 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 0 3 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h2 : X.map (backIncl 2 2).op
      (X.map (cup2U 4 4 ((0 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 4 5 6 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : backIncl 2 2 ≫ cup2U 4 4 ((0 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 4 5 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  rw [h1, h2, Fv_eq, Fv_eq]

/-- The value of `x ⌣ x` on the four-simplex `(cup2V 4 4 0 3) τ` -/
lemma ev_xxV_0_2 :
    genEval F2 X (cup F2 X x x)
        (X.map (cup2V 4 4 ((0 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
      = Fv X x τ 0 1 2 * Fv X x τ 2 3 6 := by
  rw [cup_apply_2_2]
  have h1 : X.map (frontIncl 2 4 (by omega)).op
      (X.map (cup2V 4 4 ((0 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 0 1 2 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : frontIncl 2 4 (by omega) ≫ cup2V 4 4 ((0 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 0 1 2 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h2 : X.map (backIncl 2 2).op
      (X.map (cup2V 4 4 ((0 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 2 3 6 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : backIncl 2 2 ≫ cup2V 4 4 ((0 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 2 3 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  rw [h1, h2, Fv_eq, Fv_eq]

/-- The value of `x ⌣ x` on the four-simplex `(cup2U 4 4 1 1) τ` -/
lemma ev_xxU_1_0 :
    genEval F2 X (cup F2 X x x)
        (X.map (cup2U 4 4 ((1 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
      = Fv X x τ 0 1 2 * Fv X x τ 2 3 4 := by
  rw [cup_apply_2_2]
  have h1 : X.map (frontIncl 2 4 (by omega)).op
      (X.map (cup2U 4 4 ((1 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 0 1 2 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : frontIncl 2 4 (by omega) ≫ cup2U 4 4 ((1 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 0 1 2 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h2 : X.map (backIncl 2 2).op
      (X.map (cup2U 4 4 ((1 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 2 3 4 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : backIncl 2 2 ≫ cup2U 4 4 ((1 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 2 3 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  rw [h1, h2, Fv_eq, Fv_eq]

/-- The value of `x ⌣ x` on the four-simplex `(cup2V 4 4 1 1) τ` -/
lemma ev_xxV_1_0 :
    genEval F2 X (cup F2 X x x)
        (X.map (cup2V 4 4 ((1 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
      = Fv X x τ 1 2 4 * Fv X x τ 4 5 6 := by
  rw [cup_apply_2_2]
  have h1 : X.map (frontIncl 2 4 (by omega)).op
      (X.map (cup2V 4 4 ((1 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 1 2 4 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : frontIncl 2 4 (by omega) ≫ cup2V 4 4 ((1 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 1 2 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h2 : X.map (backIncl 2 2).op
      (X.map (cup2V 4 4 ((1 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 4 5 6 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : backIncl 2 2 ≫ cup2V 4 4 ((1 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 4 5 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  rw [h1, h2, Fv_eq, Fv_eq]

/-- The value of `x ⌣ x` on the four-simplex `(cup2U 4 4 1 2) τ` -/
lemma ev_xxU_1_1 :
    genEval F2 X (cup F2 X x x)
        (X.map (cup2U 4 4 ((1 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
      = Fv X x τ 0 1 3 * Fv X x τ 3 4 5 := by
  rw [cup_apply_2_2]
  have h1 : X.map (frontIncl 2 4 (by omega)).op
      (X.map (cup2U 4 4 ((1 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 0 1 3 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : frontIncl 2 4 (by omega) ≫ cup2U 4 4 ((1 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 0 1 3 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h2 : X.map (backIncl 2 2).op
      (X.map (cup2U 4 4 ((1 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 3 4 5 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : backIncl 2 2 ≫ cup2U 4 4 ((1 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 3 4 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  rw [h1, h2, Fv_eq, Fv_eq]

/-- The value of `x ⌣ x` on the four-simplex `(cup2V 4 4 1 2) τ` -/
lemma ev_xxV_1_1 :
    genEval F2 X (cup F2 X x x)
        (X.map (cup2V 4 4 ((1 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
      = Fv X x τ 1 2 3 * Fv X x τ 3 5 6 := by
  rw [cup_apply_2_2]
  have h1 : X.map (frontIncl 2 4 (by omega)).op
      (X.map (cup2V 4 4 ((1 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 1 2 3 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : frontIncl 2 4 (by omega) ≫ cup2V 4 4 ((1 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 1 2 3 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h2 : X.map (backIncl 2 2).op
      (X.map (cup2V 4 4 ((1 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 3 5 6 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : backIncl 2 2 ≫ cup2V 4 4 ((1 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 3 5 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  rw [h1, h2, Fv_eq, Fv_eq]

/-- The value of `x ⌣ x` on the four-simplex `(cup2U 4 4 1 3) τ` -/
lemma ev_xxU_1_2 :
    genEval F2 X (cup F2 X x x)
        (X.map (cup2U 4 4 ((1 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
      = Fv X x τ 0 1 4 * Fv X x τ 4 5 6 := by
  rw [cup_apply_2_2]
  have h1 : X.map (frontIncl 2 4 (by omega)).op
      (X.map (cup2U 4 4 ((1 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 0 1 4 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : frontIncl 2 4 (by omega) ≫ cup2U 4 4 ((1 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 0 1 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h2 : X.map (backIncl 2 2).op
      (X.map (cup2U 4 4 ((1 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 4 5 6 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : backIncl 2 2 ≫ cup2U 4 4 ((1 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 4 5 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  rw [h1, h2, Fv_eq, Fv_eq]

/-- The value of `x ⌣ x` on the four-simplex `(cup2V 4 4 1 3) τ` -/
lemma ev_xxV_1_2 :
    genEval F2 X (cup F2 X x x)
        (X.map (cup2V 4 4 ((1 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
      = Fv X x τ 1 2 3 * Fv X x τ 3 4 6 := by
  rw [cup_apply_2_2]
  have h1 : X.map (frontIncl 2 4 (by omega)).op
      (X.map (cup2V 4 4 ((1 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 1 2 3 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : frontIncl 2 4 (by omega) ≫ cup2V 4 4 ((1 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 1 2 3 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h2 : X.map (backIncl 2 2).op
      (X.map (cup2V 4 4 ((1 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 3 4 6 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : backIncl 2 2 ≫ cup2V 4 4 ((1 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 3 4 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  rw [h1, h2, Fv_eq, Fv_eq]

/-- The value of `x ⌣ x` on the four-simplex `(cup2U 4 4 2 1) τ` -/
lemma ev_xxU_2_0 :
    genEval F2 X (cup F2 X x x)
        (X.map (cup2U 4 4 ((2 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
      = Fv X x τ 0 1 2 * Fv X x τ 2 3 4 := by
  rw [cup_apply_2_2]
  have h1 : X.map (frontIncl 2 4 (by omega)).op
      (X.map (cup2U 4 4 ((2 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 0 1 2 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : frontIncl 2 4 (by omega) ≫ cup2U 4 4 ((2 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 0 1 2 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h2 : X.map (backIncl 2 2).op
      (X.map (cup2U 4 4 ((2 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 2 3 4 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : backIncl 2 2 ≫ cup2U 4 4 ((2 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 2 3 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  rw [h1, h2, Fv_eq, Fv_eq]

/-- The value of `x ⌣ x` on the four-simplex `(cup2V 4 4 2 1) τ` -/
lemma ev_xxV_2_0 :
    genEval F2 X (cup F2 X x x)
        (X.map (cup2V 4 4 ((2 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
      = Fv X x τ 2 3 4 * Fv X x τ 4 5 6 := by
  rw [cup_apply_2_2]
  have h1 : X.map (frontIncl 2 4 (by omega)).op
      (X.map (cup2V 4 4 ((2 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 2 3 4 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : frontIncl 2 4 (by omega) ≫ cup2V 4 4 ((2 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 2 3 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h2 : X.map (backIncl 2 2).op
      (X.map (cup2V 4 4 ((2 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 4 5 6 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : backIncl 2 2 ≫ cup2V 4 4 ((2 : Fin 3).val) (((0 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 4 5 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  rw [h1, h2, Fv_eq, Fv_eq]

/-- The value of `x ⌣ x` on the four-simplex `(cup2U 4 4 2 2) τ` -/
lemma ev_xxU_2_1 :
    genEval F2 X (cup F2 X x x)
        (X.map (cup2U 4 4 ((2 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
      = Fv X x τ 0 1 2 * Fv X x τ 2 4 5 := by
  rw [cup_apply_2_2]
  have h1 : X.map (frontIncl 2 4 (by omega)).op
      (X.map (cup2U 4 4 ((2 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 0 1 2 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : frontIncl 2 4 (by omega) ≫ cup2U 4 4 ((2 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 0 1 2 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h2 : X.map (backIncl 2 2).op
      (X.map (cup2U 4 4 ((2 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 2 4 5 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : backIncl 2 2 ≫ cup2U 4 4 ((2 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 2 4 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  rw [h1, h2, Fv_eq, Fv_eq]

/-- The value of `x ⌣ x` on the four-simplex `(cup2V 4 4 2 2) τ` -/
lemma ev_xxV_2_1 :
    genEval F2 X (cup F2 X x x)
        (X.map (cup2V 4 4 ((2 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
      = Fv X x τ 2 3 4 * Fv X x τ 4 5 6 := by
  rw [cup_apply_2_2]
  have h1 : X.map (frontIncl 2 4 (by omega)).op
      (X.map (cup2V 4 4 ((2 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 2 3 4 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : frontIncl 2 4 (by omega) ≫ cup2V 4 4 ((2 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 2 3 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h2 : X.map (backIncl 2 2).op
      (X.map (cup2V 4 4 ((2 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 4 5 6 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : backIncl 2 2 ≫ cup2V 4 4 ((2 : Fin 3).val) (((1 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 4 5 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  rw [h1, h2, Fv_eq, Fv_eq]

/-- The value of `x ⌣ x` on the four-simplex `(cup2U 4 4 2 3) τ` -/
lemma ev_xxU_2_2 :
    genEval F2 X (cup F2 X x x)
        (X.map (cup2U 4 4 ((2 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
      = Fv X x τ 0 1 2 * Fv X x τ 2 5 6 := by
  rw [cup_apply_2_2]
  have h1 : X.map (frontIncl 2 4 (by omega)).op
      (X.map (cup2U 4 4 ((2 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 0 1 2 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : frontIncl 2 4 (by omega) ≫ cup2U 4 4 ((2 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 0 1 2 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h2 : X.map (backIncl 2 2).op
      (X.map (cup2U 4 4 ((2 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 2 5 6 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : backIncl 2 2 ≫ cup2U 4 4 ((2 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 2 5 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  rw [h1, h2, Fv_eq, Fv_eq]

/-- The value of `x ⌣ x` on the four-simplex `(cup2V 4 4 2 3) τ` -/
lemma ev_xxV_2_2 :
    genEval F2 X (cup F2 X x x)
        (X.map (cup2V 4 4 ((2 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
      = Fv X x τ 2 3 4 * Fv X x τ 4 5 6 := by
  rw [cup_apply_2_2]
  have h1 : X.map (frontIncl 2 4 (by omega)).op
      (X.map (cup2V 4 4 ((2 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 2 3 4 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : frontIncl 2 4 (by omega) ≫ cup2V 4 4 ((2 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 2 3 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h2 : X.map (backIncl 2 2).op
      (X.map (cup2V 4 4 ((2 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)).op τ)
        = X.map (inc6 4 5 6 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : backIncl 2 2 ≫ cup2V 4 4 ((2 : Fin 3).val) (((2 : Fin 3).val) + 1) (by omega) (by omega) (by omega)
        = inc6 4 5 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  rw [h1, h2, Fv_eq, Fv_eq]


/-! ## Part 3: the value of `x ∪₁ x` on the front and back `3`-faces of `τ` -/

/-- The value of `x ∪₁ x` on the `front` `3`-face of `τ` -/
lemma ev_x1x_front :
    genEval F2 X (cup1m X 2 2 x x) (X.map (frontIncl 3 6 (by omega)).op τ)
      = (Fv X x τ 0 1 2 * Fv X x τ 0 2 3)
        + (Fv X x τ 1 2 3 * Fv X x τ 0 1 3) := by
  rw [genEval_cup1m_2_2, genEval_cup1_2_2]
  have h1 : X.map (Fface 2 2 0 (by omega)).op
      (X.map (frontIncl 3 6 (by omega)).op τ) = X.map (inc6 0 1 2 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : Fface 2 2 0 (by omega) ≫ frontIncl 3 6 (by omega) = inc6 0 1 2 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h2 : X.map (Gface 2 2 0 (by omega)).op
      (X.map (frontIncl 3 6 (by omega)).op τ) = X.map (inc6 0 2 3 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : Gface 2 2 0 (by omega) ≫ frontIncl 3 6 (by omega) = inc6 0 2 3 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h3 : X.map (Fface 2 2 1 (by omega)).op
      (X.map (frontIncl 3 6 (by omega)).op τ) = X.map (inc6 1 2 3 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : Fface 2 2 1 (by omega) ≫ frontIncl 3 6 (by omega) = inc6 1 2 3 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h4 : X.map (Gface 2 2 1 (by omega)).op
      (X.map (frontIncl 3 6 (by omega)).op τ) = X.map (inc6 0 1 3 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : Gface 2 2 1 (by omega) ≫ frontIncl 3 6 (by omega) = inc6 0 1 3 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  rw [h1, h2, h3, h4, Fv_eq, Fv_eq, Fv_eq, Fv_eq]

/-- The value of `x ∪₁ x` on the `back` `3`-face of `τ` -/
lemma ev_x1x_back :
    genEval F2 X (cup1m X 2 2 x x) (X.map (backIncl 3 3).op τ)
      = (Fv X x τ 3 4 5 * Fv X x τ 3 5 6)
        + (Fv X x τ 4 5 6 * Fv X x τ 3 4 6) := by
  rw [genEval_cup1m_2_2, genEval_cup1_2_2]
  have h1 : X.map (Fface 2 2 0 (by omega)).op
      (X.map (backIncl 3 3).op τ) = X.map (inc6 3 4 5 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : Fface 2 2 0 (by omega) ≫ backIncl 3 3 = inc6 3 4 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h2 : X.map (Gface 2 2 0 (by omega)).op
      (X.map (backIncl 3 3).op τ) = X.map (inc6 3 5 6 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : Gface 2 2 0 (by omega) ≫ backIncl 3 3 = inc6 3 5 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h3 : X.map (Fface 2 2 1 (by omega)).op
      (X.map (backIncl 3 3).op τ) = X.map (inc6 4 5 6 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : Fface 2 2 1 (by omega) ≫ backIncl 3 3 = inc6 4 5 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  have h4 : X.map (Gface 2 2 1 (by omega)).op
      (X.map (backIncl 3 3).op τ) = X.map (inc6 3 4 6 (by decide) (by decide) (by decide)).op τ := by
    rw [map_op_comp]
    have hm : Gface 2 2 1 (by omega) ≫ backIncl 3 3 = inc6 3 4 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm]
  rw [h1, h2, h3, h4, Fv_eq, Fv_eq, Fv_eq, Fv_eq]


/-! ## Part 4: the twenty cocycle relations, expressing `Fv a b c` (`a > 0`) through the
atoms `Fv 0 ⋯` -/

/-- The cocycle relation for the triple `1,2,3` -/
lemma coc_1_2_3 (hx : cochainDiff F2 X x = 0) :
    Fv X x τ 1 2 3 = Fv X x τ 0 2 3 + Fv X x τ 0 1 3 + Fv X x τ 0 1 2 := by
  have h := cocycle_sum x hx
    (X.map (inc7 0 1 2 3 (by decide) (by decide) (by decide) (by decide)).op τ)
  rw [Fin.sum_univ_four] at h
  simp only [neg_one_pow_F2, one_mul] at h

  have e0 : genEval F2 X x (X.δ (0 : Fin 4)
      (X.map (inc7 0 1 2 3 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 1 2 3 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (0 : Fin 4) ≫ inc7 0 1 2 3
        (by decide) (by decide) (by decide) (by decide) = inc6 1 2 3 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e1 : genEval F2 X x (X.δ (1 : Fin 4)
      (X.map (inc7 0 1 2 3 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 2 3 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (1 : Fin 4) ≫ inc7 0 1 2 3
        (by decide) (by decide) (by decide) (by decide) = inc6 0 2 3 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e2 : genEval F2 X x (X.δ (2 : Fin 4)
      (X.map (inc7 0 1 2 3 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 1 3 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (2 : Fin 4) ≫ inc7 0 1 2 3
        (by decide) (by decide) (by decide) (by decide) = inc6 0 1 3 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e3 : genEval F2 X x (X.δ (3 : Fin 4)
      (X.map (inc7 0 1 2 3 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 1 2 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (3 : Fin 4) ≫ inc7 0 1 2 3
        (by decide) (by decide) (by decide) (by decide) = inc6 0 1 2 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  rw [e0, e1, e2, e3] at h
  have h' : Fv X x τ 1 2 3
      + (Fv X x τ 0 2 3 + Fv X x τ 0 1 3 + Fv X x τ 0 1 2) = 0 := by
    rw [← h]; abel
  rwa [CharTwo.add_eq_zero] at h'

/-- The cocycle relation for the triple `1,2,4` -/
lemma coc_1_2_4 (hx : cochainDiff F2 X x = 0) :
    Fv X x τ 1 2 4 = Fv X x τ 0 2 4 + Fv X x τ 0 1 4 + Fv X x τ 0 1 2 := by
  have h := cocycle_sum x hx
    (X.map (inc7 0 1 2 4 (by decide) (by decide) (by decide) (by decide)).op τ)
  rw [Fin.sum_univ_four] at h
  simp only [neg_one_pow_F2, one_mul] at h

  have e0 : genEval F2 X x (X.δ (0 : Fin 4)
      (X.map (inc7 0 1 2 4 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 1 2 4 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (0 : Fin 4) ≫ inc7 0 1 2 4
        (by decide) (by decide) (by decide) (by decide) = inc6 1 2 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e1 : genEval F2 X x (X.δ (1 : Fin 4)
      (X.map (inc7 0 1 2 4 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 2 4 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (1 : Fin 4) ≫ inc7 0 1 2 4
        (by decide) (by decide) (by decide) (by decide) = inc6 0 2 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e2 : genEval F2 X x (X.δ (2 : Fin 4)
      (X.map (inc7 0 1 2 4 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 1 4 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (2 : Fin 4) ≫ inc7 0 1 2 4
        (by decide) (by decide) (by decide) (by decide) = inc6 0 1 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e3 : genEval F2 X x (X.δ (3 : Fin 4)
      (X.map (inc7 0 1 2 4 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 1 2 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (3 : Fin 4) ≫ inc7 0 1 2 4
        (by decide) (by decide) (by decide) (by decide) = inc6 0 1 2 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  rw [e0, e1, e2, e3] at h
  have h' : Fv X x τ 1 2 4
      + (Fv X x τ 0 2 4 + Fv X x τ 0 1 4 + Fv X x τ 0 1 2) = 0 := by
    rw [← h]; abel
  rwa [CharTwo.add_eq_zero] at h'

/-- The cocycle relation for the triple `1,2,5` -/
lemma coc_1_2_5 (hx : cochainDiff F2 X x = 0) :
    Fv X x τ 1 2 5 = Fv X x τ 0 2 5 + Fv X x τ 0 1 5 + Fv X x τ 0 1 2 := by
  have h := cocycle_sum x hx
    (X.map (inc7 0 1 2 5 (by decide) (by decide) (by decide) (by decide)).op τ)
  rw [Fin.sum_univ_four] at h
  simp only [neg_one_pow_F2, one_mul] at h

  have e0 : genEval F2 X x (X.δ (0 : Fin 4)
      (X.map (inc7 0 1 2 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 1 2 5 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (0 : Fin 4) ≫ inc7 0 1 2 5
        (by decide) (by decide) (by decide) (by decide) = inc6 1 2 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e1 : genEval F2 X x (X.δ (1 : Fin 4)
      (X.map (inc7 0 1 2 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 2 5 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (1 : Fin 4) ≫ inc7 0 1 2 5
        (by decide) (by decide) (by decide) (by decide) = inc6 0 2 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e2 : genEval F2 X x (X.δ (2 : Fin 4)
      (X.map (inc7 0 1 2 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 1 5 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (2 : Fin 4) ≫ inc7 0 1 2 5
        (by decide) (by decide) (by decide) (by decide) = inc6 0 1 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e3 : genEval F2 X x (X.δ (3 : Fin 4)
      (X.map (inc7 0 1 2 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 1 2 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (3 : Fin 4) ≫ inc7 0 1 2 5
        (by decide) (by decide) (by decide) (by decide) = inc6 0 1 2 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  rw [e0, e1, e2, e3] at h
  have h' : Fv X x τ 1 2 5
      + (Fv X x τ 0 2 5 + Fv X x τ 0 1 5 + Fv X x τ 0 1 2) = 0 := by
    rw [← h]; abel
  rwa [CharTwo.add_eq_zero] at h'

/-- The cocycle relation for the triple `1,2,6` -/
lemma coc_1_2_6 (hx : cochainDiff F2 X x = 0) :
    Fv X x τ 1 2 6 = Fv X x τ 0 2 6 + Fv X x τ 0 1 6 + Fv X x τ 0 1 2 := by
  have h := cocycle_sum x hx
    (X.map (inc7 0 1 2 6 (by decide) (by decide) (by decide) (by decide)).op τ)
  rw [Fin.sum_univ_four] at h
  simp only [neg_one_pow_F2, one_mul] at h

  have e0 : genEval F2 X x (X.δ (0 : Fin 4)
      (X.map (inc7 0 1 2 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 1 2 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (0 : Fin 4) ≫ inc7 0 1 2 6
        (by decide) (by decide) (by decide) (by decide) = inc6 1 2 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e1 : genEval F2 X x (X.δ (1 : Fin 4)
      (X.map (inc7 0 1 2 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 2 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (1 : Fin 4) ≫ inc7 0 1 2 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 2 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e2 : genEval F2 X x (X.δ (2 : Fin 4)
      (X.map (inc7 0 1 2 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 1 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (2 : Fin 4) ≫ inc7 0 1 2 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 1 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e3 : genEval F2 X x (X.δ (3 : Fin 4)
      (X.map (inc7 0 1 2 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 1 2 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (3 : Fin 4) ≫ inc7 0 1 2 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 1 2 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  rw [e0, e1, e2, e3] at h
  have h' : Fv X x τ 1 2 6
      + (Fv X x τ 0 2 6 + Fv X x τ 0 1 6 + Fv X x τ 0 1 2) = 0 := by
    rw [← h]; abel
  rwa [CharTwo.add_eq_zero] at h'

/-- The cocycle relation for the triple `1,3,4` -/
lemma coc_1_3_4 (hx : cochainDiff F2 X x = 0) :
    Fv X x τ 1 3 4 = Fv X x τ 0 3 4 + Fv X x τ 0 1 4 + Fv X x τ 0 1 3 := by
  have h := cocycle_sum x hx
    (X.map (inc7 0 1 3 4 (by decide) (by decide) (by decide) (by decide)).op τ)
  rw [Fin.sum_univ_four] at h
  simp only [neg_one_pow_F2, one_mul] at h

  have e0 : genEval F2 X x (X.δ (0 : Fin 4)
      (X.map (inc7 0 1 3 4 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 1 3 4 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (0 : Fin 4) ≫ inc7 0 1 3 4
        (by decide) (by decide) (by decide) (by decide) = inc6 1 3 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e1 : genEval F2 X x (X.δ (1 : Fin 4)
      (X.map (inc7 0 1 3 4 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 3 4 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (1 : Fin 4) ≫ inc7 0 1 3 4
        (by decide) (by decide) (by decide) (by decide) = inc6 0 3 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e2 : genEval F2 X x (X.δ (2 : Fin 4)
      (X.map (inc7 0 1 3 4 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 1 4 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (2 : Fin 4) ≫ inc7 0 1 3 4
        (by decide) (by decide) (by decide) (by decide) = inc6 0 1 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e3 : genEval F2 X x (X.δ (3 : Fin 4)
      (X.map (inc7 0 1 3 4 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 1 3 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (3 : Fin 4) ≫ inc7 0 1 3 4
        (by decide) (by decide) (by decide) (by decide) = inc6 0 1 3 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  rw [e0, e1, e2, e3] at h
  have h' : Fv X x τ 1 3 4
      + (Fv X x τ 0 3 4 + Fv X x τ 0 1 4 + Fv X x τ 0 1 3) = 0 := by
    rw [← h]; abel
  rwa [CharTwo.add_eq_zero] at h'

/-- The cocycle relation for the triple `1,3,5` -/
lemma coc_1_3_5 (hx : cochainDiff F2 X x = 0) :
    Fv X x τ 1 3 5 = Fv X x τ 0 3 5 + Fv X x τ 0 1 5 + Fv X x τ 0 1 3 := by
  have h := cocycle_sum x hx
    (X.map (inc7 0 1 3 5 (by decide) (by decide) (by decide) (by decide)).op τ)
  rw [Fin.sum_univ_four] at h
  simp only [neg_one_pow_F2, one_mul] at h

  have e0 : genEval F2 X x (X.δ (0 : Fin 4)
      (X.map (inc7 0 1 3 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 1 3 5 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (0 : Fin 4) ≫ inc7 0 1 3 5
        (by decide) (by decide) (by decide) (by decide) = inc6 1 3 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e1 : genEval F2 X x (X.δ (1 : Fin 4)
      (X.map (inc7 0 1 3 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 3 5 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (1 : Fin 4) ≫ inc7 0 1 3 5
        (by decide) (by decide) (by decide) (by decide) = inc6 0 3 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e2 : genEval F2 X x (X.δ (2 : Fin 4)
      (X.map (inc7 0 1 3 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 1 5 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (2 : Fin 4) ≫ inc7 0 1 3 5
        (by decide) (by decide) (by decide) (by decide) = inc6 0 1 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e3 : genEval F2 X x (X.δ (3 : Fin 4)
      (X.map (inc7 0 1 3 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 1 3 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (3 : Fin 4) ≫ inc7 0 1 3 5
        (by decide) (by decide) (by decide) (by decide) = inc6 0 1 3 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  rw [e0, e1, e2, e3] at h
  have h' : Fv X x τ 1 3 5
      + (Fv X x τ 0 3 5 + Fv X x τ 0 1 5 + Fv X x τ 0 1 3) = 0 := by
    rw [← h]; abel
  rwa [CharTwo.add_eq_zero] at h'

/-- The cocycle relation for the triple `1,3,6` -/
lemma coc_1_3_6 (hx : cochainDiff F2 X x = 0) :
    Fv X x τ 1 3 6 = Fv X x τ 0 3 6 + Fv X x τ 0 1 6 + Fv X x τ 0 1 3 := by
  have h := cocycle_sum x hx
    (X.map (inc7 0 1 3 6 (by decide) (by decide) (by decide) (by decide)).op τ)
  rw [Fin.sum_univ_four] at h
  simp only [neg_one_pow_F2, one_mul] at h

  have e0 : genEval F2 X x (X.δ (0 : Fin 4)
      (X.map (inc7 0 1 3 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 1 3 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (0 : Fin 4) ≫ inc7 0 1 3 6
        (by decide) (by decide) (by decide) (by decide) = inc6 1 3 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e1 : genEval F2 X x (X.δ (1 : Fin 4)
      (X.map (inc7 0 1 3 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 3 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (1 : Fin 4) ≫ inc7 0 1 3 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 3 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e2 : genEval F2 X x (X.δ (2 : Fin 4)
      (X.map (inc7 0 1 3 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 1 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (2 : Fin 4) ≫ inc7 0 1 3 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 1 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e3 : genEval F2 X x (X.δ (3 : Fin 4)
      (X.map (inc7 0 1 3 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 1 3 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (3 : Fin 4) ≫ inc7 0 1 3 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 1 3 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  rw [e0, e1, e2, e3] at h
  have h' : Fv X x τ 1 3 6
      + (Fv X x τ 0 3 6 + Fv X x τ 0 1 6 + Fv X x τ 0 1 3) = 0 := by
    rw [← h]; abel
  rwa [CharTwo.add_eq_zero] at h'

/-- The cocycle relation for the triple `1,4,5` -/
lemma coc_1_4_5 (hx : cochainDiff F2 X x = 0) :
    Fv X x τ 1 4 5 = Fv X x τ 0 4 5 + Fv X x τ 0 1 5 + Fv X x τ 0 1 4 := by
  have h := cocycle_sum x hx
    (X.map (inc7 0 1 4 5 (by decide) (by decide) (by decide) (by decide)).op τ)
  rw [Fin.sum_univ_four] at h
  simp only [neg_one_pow_F2, one_mul] at h

  have e0 : genEval F2 X x (X.δ (0 : Fin 4)
      (X.map (inc7 0 1 4 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 1 4 5 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (0 : Fin 4) ≫ inc7 0 1 4 5
        (by decide) (by decide) (by decide) (by decide) = inc6 1 4 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e1 : genEval F2 X x (X.δ (1 : Fin 4)
      (X.map (inc7 0 1 4 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 4 5 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (1 : Fin 4) ≫ inc7 0 1 4 5
        (by decide) (by decide) (by decide) (by decide) = inc6 0 4 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e2 : genEval F2 X x (X.δ (2 : Fin 4)
      (X.map (inc7 0 1 4 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 1 5 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (2 : Fin 4) ≫ inc7 0 1 4 5
        (by decide) (by decide) (by decide) (by decide) = inc6 0 1 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e3 : genEval F2 X x (X.δ (3 : Fin 4)
      (X.map (inc7 0 1 4 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 1 4 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (3 : Fin 4) ≫ inc7 0 1 4 5
        (by decide) (by decide) (by decide) (by decide) = inc6 0 1 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  rw [e0, e1, e2, e3] at h
  have h' : Fv X x τ 1 4 5
      + (Fv X x τ 0 4 5 + Fv X x τ 0 1 5 + Fv X x τ 0 1 4) = 0 := by
    rw [← h]; abel
  rwa [CharTwo.add_eq_zero] at h'

/-- The cocycle relation for the triple `1,4,6` -/
lemma coc_1_4_6 (hx : cochainDiff F2 X x = 0) :
    Fv X x τ 1 4 6 = Fv X x τ 0 4 6 + Fv X x τ 0 1 6 + Fv X x τ 0 1 4 := by
  have h := cocycle_sum x hx
    (X.map (inc7 0 1 4 6 (by decide) (by decide) (by decide) (by decide)).op τ)
  rw [Fin.sum_univ_four] at h
  simp only [neg_one_pow_F2, one_mul] at h

  have e0 : genEval F2 X x (X.δ (0 : Fin 4)
      (X.map (inc7 0 1 4 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 1 4 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (0 : Fin 4) ≫ inc7 0 1 4 6
        (by decide) (by decide) (by decide) (by decide) = inc6 1 4 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e1 : genEval F2 X x (X.δ (1 : Fin 4)
      (X.map (inc7 0 1 4 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 4 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (1 : Fin 4) ≫ inc7 0 1 4 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 4 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e2 : genEval F2 X x (X.δ (2 : Fin 4)
      (X.map (inc7 0 1 4 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 1 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (2 : Fin 4) ≫ inc7 0 1 4 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 1 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e3 : genEval F2 X x (X.δ (3 : Fin 4)
      (X.map (inc7 0 1 4 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 1 4 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (3 : Fin 4) ≫ inc7 0 1 4 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 1 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  rw [e0, e1, e2, e3] at h
  have h' : Fv X x τ 1 4 6
      + (Fv X x τ 0 4 6 + Fv X x τ 0 1 6 + Fv X x τ 0 1 4) = 0 := by
    rw [← h]; abel
  rwa [CharTwo.add_eq_zero] at h'

/-- The cocycle relation for the triple `1,5,6` -/
lemma coc_1_5_6 (hx : cochainDiff F2 X x = 0) :
    Fv X x τ 1 5 6 = Fv X x τ 0 5 6 + Fv X x τ 0 1 6 + Fv X x τ 0 1 5 := by
  have h := cocycle_sum x hx
    (X.map (inc7 0 1 5 6 (by decide) (by decide) (by decide) (by decide)).op τ)
  rw [Fin.sum_univ_four] at h
  simp only [neg_one_pow_F2, one_mul] at h

  have e0 : genEval F2 X x (X.δ (0 : Fin 4)
      (X.map (inc7 0 1 5 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 1 5 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (0 : Fin 4) ≫ inc7 0 1 5 6
        (by decide) (by decide) (by decide) (by decide) = inc6 1 5 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e1 : genEval F2 X x (X.δ (1 : Fin 4)
      (X.map (inc7 0 1 5 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 5 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (1 : Fin 4) ≫ inc7 0 1 5 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 5 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e2 : genEval F2 X x (X.δ (2 : Fin 4)
      (X.map (inc7 0 1 5 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 1 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (2 : Fin 4) ≫ inc7 0 1 5 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 1 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e3 : genEval F2 X x (X.δ (3 : Fin 4)
      (X.map (inc7 0 1 5 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 1 5 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (3 : Fin 4) ≫ inc7 0 1 5 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 1 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  rw [e0, e1, e2, e3] at h
  have h' : Fv X x τ 1 5 6
      + (Fv X x τ 0 5 6 + Fv X x τ 0 1 6 + Fv X x τ 0 1 5) = 0 := by
    rw [← h]; abel
  rwa [CharTwo.add_eq_zero] at h'

/-- The cocycle relation for the triple `2,3,4` -/
lemma coc_2_3_4 (hx : cochainDiff F2 X x = 0) :
    Fv X x τ 2 3 4 = Fv X x τ 0 3 4 + Fv X x τ 0 2 4 + Fv X x τ 0 2 3 := by
  have h := cocycle_sum x hx
    (X.map (inc7 0 2 3 4 (by decide) (by decide) (by decide) (by decide)).op τ)
  rw [Fin.sum_univ_four] at h
  simp only [neg_one_pow_F2, one_mul] at h

  have e0 : genEval F2 X x (X.δ (0 : Fin 4)
      (X.map (inc7 0 2 3 4 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 2 3 4 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (0 : Fin 4) ≫ inc7 0 2 3 4
        (by decide) (by decide) (by decide) (by decide) = inc6 2 3 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e1 : genEval F2 X x (X.δ (1 : Fin 4)
      (X.map (inc7 0 2 3 4 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 3 4 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (1 : Fin 4) ≫ inc7 0 2 3 4
        (by decide) (by decide) (by decide) (by decide) = inc6 0 3 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e2 : genEval F2 X x (X.δ (2 : Fin 4)
      (X.map (inc7 0 2 3 4 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 2 4 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (2 : Fin 4) ≫ inc7 0 2 3 4
        (by decide) (by decide) (by decide) (by decide) = inc6 0 2 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e3 : genEval F2 X x (X.δ (3 : Fin 4)
      (X.map (inc7 0 2 3 4 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 2 3 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (3 : Fin 4) ≫ inc7 0 2 3 4
        (by decide) (by decide) (by decide) (by decide) = inc6 0 2 3 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  rw [e0, e1, e2, e3] at h
  have h' : Fv X x τ 2 3 4
      + (Fv X x τ 0 3 4 + Fv X x τ 0 2 4 + Fv X x τ 0 2 3) = 0 := by
    rw [← h]; abel
  rwa [CharTwo.add_eq_zero] at h'

/-- The cocycle relation for the triple `2,3,5` -/
lemma coc_2_3_5 (hx : cochainDiff F2 X x = 0) :
    Fv X x τ 2 3 5 = Fv X x τ 0 3 5 + Fv X x τ 0 2 5 + Fv X x τ 0 2 3 := by
  have h := cocycle_sum x hx
    (X.map (inc7 0 2 3 5 (by decide) (by decide) (by decide) (by decide)).op τ)
  rw [Fin.sum_univ_four] at h
  simp only [neg_one_pow_F2, one_mul] at h

  have e0 : genEval F2 X x (X.δ (0 : Fin 4)
      (X.map (inc7 0 2 3 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 2 3 5 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (0 : Fin 4) ≫ inc7 0 2 3 5
        (by decide) (by decide) (by decide) (by decide) = inc6 2 3 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e1 : genEval F2 X x (X.δ (1 : Fin 4)
      (X.map (inc7 0 2 3 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 3 5 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (1 : Fin 4) ≫ inc7 0 2 3 5
        (by decide) (by decide) (by decide) (by decide) = inc6 0 3 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e2 : genEval F2 X x (X.δ (2 : Fin 4)
      (X.map (inc7 0 2 3 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 2 5 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (2 : Fin 4) ≫ inc7 0 2 3 5
        (by decide) (by decide) (by decide) (by decide) = inc6 0 2 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e3 : genEval F2 X x (X.δ (3 : Fin 4)
      (X.map (inc7 0 2 3 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 2 3 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (3 : Fin 4) ≫ inc7 0 2 3 5
        (by decide) (by decide) (by decide) (by decide) = inc6 0 2 3 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  rw [e0, e1, e2, e3] at h
  have h' : Fv X x τ 2 3 5
      + (Fv X x τ 0 3 5 + Fv X x τ 0 2 5 + Fv X x τ 0 2 3) = 0 := by
    rw [← h]; abel
  rwa [CharTwo.add_eq_zero] at h'

/-- The cocycle relation for the triple `2,3,6` -/
lemma coc_2_3_6 (hx : cochainDiff F2 X x = 0) :
    Fv X x τ 2 3 6 = Fv X x τ 0 3 6 + Fv X x τ 0 2 6 + Fv X x τ 0 2 3 := by
  have h := cocycle_sum x hx
    (X.map (inc7 0 2 3 6 (by decide) (by decide) (by decide) (by decide)).op τ)
  rw [Fin.sum_univ_four] at h
  simp only [neg_one_pow_F2, one_mul] at h

  have e0 : genEval F2 X x (X.δ (0 : Fin 4)
      (X.map (inc7 0 2 3 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 2 3 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (0 : Fin 4) ≫ inc7 0 2 3 6
        (by decide) (by decide) (by decide) (by decide) = inc6 2 3 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e1 : genEval F2 X x (X.δ (1 : Fin 4)
      (X.map (inc7 0 2 3 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 3 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (1 : Fin 4) ≫ inc7 0 2 3 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 3 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e2 : genEval F2 X x (X.δ (2 : Fin 4)
      (X.map (inc7 0 2 3 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 2 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (2 : Fin 4) ≫ inc7 0 2 3 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 2 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e3 : genEval F2 X x (X.δ (3 : Fin 4)
      (X.map (inc7 0 2 3 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 2 3 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (3 : Fin 4) ≫ inc7 0 2 3 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 2 3 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  rw [e0, e1, e2, e3] at h
  have h' : Fv X x τ 2 3 6
      + (Fv X x τ 0 3 6 + Fv X x τ 0 2 6 + Fv X x τ 0 2 3) = 0 := by
    rw [← h]; abel
  rwa [CharTwo.add_eq_zero] at h'

/-- The cocycle relation for the triple `2,4,5` -/
lemma coc_2_4_5 (hx : cochainDiff F2 X x = 0) :
    Fv X x τ 2 4 5 = Fv X x τ 0 4 5 + Fv X x τ 0 2 5 + Fv X x τ 0 2 4 := by
  have h := cocycle_sum x hx
    (X.map (inc7 0 2 4 5 (by decide) (by decide) (by decide) (by decide)).op τ)
  rw [Fin.sum_univ_four] at h
  simp only [neg_one_pow_F2, one_mul] at h

  have e0 : genEval F2 X x (X.δ (0 : Fin 4)
      (X.map (inc7 0 2 4 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 2 4 5 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (0 : Fin 4) ≫ inc7 0 2 4 5
        (by decide) (by decide) (by decide) (by decide) = inc6 2 4 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e1 : genEval F2 X x (X.δ (1 : Fin 4)
      (X.map (inc7 0 2 4 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 4 5 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (1 : Fin 4) ≫ inc7 0 2 4 5
        (by decide) (by decide) (by decide) (by decide) = inc6 0 4 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e2 : genEval F2 X x (X.δ (2 : Fin 4)
      (X.map (inc7 0 2 4 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 2 5 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (2 : Fin 4) ≫ inc7 0 2 4 5
        (by decide) (by decide) (by decide) (by decide) = inc6 0 2 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e3 : genEval F2 X x (X.δ (3 : Fin 4)
      (X.map (inc7 0 2 4 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 2 4 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (3 : Fin 4) ≫ inc7 0 2 4 5
        (by decide) (by decide) (by decide) (by decide) = inc6 0 2 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  rw [e0, e1, e2, e3] at h
  have h' : Fv X x τ 2 4 5
      + (Fv X x τ 0 4 5 + Fv X x τ 0 2 5 + Fv X x τ 0 2 4) = 0 := by
    rw [← h]; abel
  rwa [CharTwo.add_eq_zero] at h'

/-- The cocycle relation for the triple `2,4,6` -/
lemma coc_2_4_6 (hx : cochainDiff F2 X x = 0) :
    Fv X x τ 2 4 6 = Fv X x τ 0 4 6 + Fv X x τ 0 2 6 + Fv X x τ 0 2 4 := by
  have h := cocycle_sum x hx
    (X.map (inc7 0 2 4 6 (by decide) (by decide) (by decide) (by decide)).op τ)
  rw [Fin.sum_univ_four] at h
  simp only [neg_one_pow_F2, one_mul] at h

  have e0 : genEval F2 X x (X.δ (0 : Fin 4)
      (X.map (inc7 0 2 4 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 2 4 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (0 : Fin 4) ≫ inc7 0 2 4 6
        (by decide) (by decide) (by decide) (by decide) = inc6 2 4 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e1 : genEval F2 X x (X.δ (1 : Fin 4)
      (X.map (inc7 0 2 4 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 4 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (1 : Fin 4) ≫ inc7 0 2 4 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 4 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e2 : genEval F2 X x (X.δ (2 : Fin 4)
      (X.map (inc7 0 2 4 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 2 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (2 : Fin 4) ≫ inc7 0 2 4 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 2 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e3 : genEval F2 X x (X.δ (3 : Fin 4)
      (X.map (inc7 0 2 4 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 2 4 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (3 : Fin 4) ≫ inc7 0 2 4 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 2 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  rw [e0, e1, e2, e3] at h
  have h' : Fv X x τ 2 4 6
      + (Fv X x τ 0 4 6 + Fv X x τ 0 2 6 + Fv X x τ 0 2 4) = 0 := by
    rw [← h]; abel
  rwa [CharTwo.add_eq_zero] at h'

/-- The cocycle relation for the triple `2,5,6` -/
lemma coc_2_5_6 (hx : cochainDiff F2 X x = 0) :
    Fv X x τ 2 5 6 = Fv X x τ 0 5 6 + Fv X x τ 0 2 6 + Fv X x τ 0 2 5 := by
  have h := cocycle_sum x hx
    (X.map (inc7 0 2 5 6 (by decide) (by decide) (by decide) (by decide)).op τ)
  rw [Fin.sum_univ_four] at h
  simp only [neg_one_pow_F2, one_mul] at h

  have e0 : genEval F2 X x (X.δ (0 : Fin 4)
      (X.map (inc7 0 2 5 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 2 5 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (0 : Fin 4) ≫ inc7 0 2 5 6
        (by decide) (by decide) (by decide) (by decide) = inc6 2 5 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e1 : genEval F2 X x (X.δ (1 : Fin 4)
      (X.map (inc7 0 2 5 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 5 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (1 : Fin 4) ≫ inc7 0 2 5 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 5 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e2 : genEval F2 X x (X.δ (2 : Fin 4)
      (X.map (inc7 0 2 5 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 2 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (2 : Fin 4) ≫ inc7 0 2 5 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 2 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e3 : genEval F2 X x (X.δ (3 : Fin 4)
      (X.map (inc7 0 2 5 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 2 5 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (3 : Fin 4) ≫ inc7 0 2 5 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 2 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  rw [e0, e1, e2, e3] at h
  have h' : Fv X x τ 2 5 6
      + (Fv X x τ 0 5 6 + Fv X x τ 0 2 6 + Fv X x τ 0 2 5) = 0 := by
    rw [← h]; abel
  rwa [CharTwo.add_eq_zero] at h'

/-- The cocycle relation for the triple `3,4,5` -/
lemma coc_3_4_5 (hx : cochainDiff F2 X x = 0) :
    Fv X x τ 3 4 5 = Fv X x τ 0 4 5 + Fv X x τ 0 3 5 + Fv X x τ 0 3 4 := by
  have h := cocycle_sum x hx
    (X.map (inc7 0 3 4 5 (by decide) (by decide) (by decide) (by decide)).op τ)
  rw [Fin.sum_univ_four] at h
  simp only [neg_one_pow_F2, one_mul] at h

  have e0 : genEval F2 X x (X.δ (0 : Fin 4)
      (X.map (inc7 0 3 4 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 3 4 5 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (0 : Fin 4) ≫ inc7 0 3 4 5
        (by decide) (by decide) (by decide) (by decide) = inc6 3 4 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e1 : genEval F2 X x (X.δ (1 : Fin 4)
      (X.map (inc7 0 3 4 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 4 5 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (1 : Fin 4) ≫ inc7 0 3 4 5
        (by decide) (by decide) (by decide) (by decide) = inc6 0 4 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e2 : genEval F2 X x (X.δ (2 : Fin 4)
      (X.map (inc7 0 3 4 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 3 5 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (2 : Fin 4) ≫ inc7 0 3 4 5
        (by decide) (by decide) (by decide) (by decide) = inc6 0 3 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e3 : genEval F2 X x (X.δ (3 : Fin 4)
      (X.map (inc7 0 3 4 5 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 3 4 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (3 : Fin 4) ≫ inc7 0 3 4 5
        (by decide) (by decide) (by decide) (by decide) = inc6 0 3 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  rw [e0, e1, e2, e3] at h
  have h' : Fv X x τ 3 4 5
      + (Fv X x τ 0 4 5 + Fv X x τ 0 3 5 + Fv X x τ 0 3 4) = 0 := by
    rw [← h]; abel
  rwa [CharTwo.add_eq_zero] at h'

/-- The cocycle relation for the triple `3,4,6` -/
lemma coc_3_4_6 (hx : cochainDiff F2 X x = 0) :
    Fv X x τ 3 4 6 = Fv X x τ 0 4 6 + Fv X x τ 0 3 6 + Fv X x τ 0 3 4 := by
  have h := cocycle_sum x hx
    (X.map (inc7 0 3 4 6 (by decide) (by decide) (by decide) (by decide)).op τ)
  rw [Fin.sum_univ_four] at h
  simp only [neg_one_pow_F2, one_mul] at h

  have e0 : genEval F2 X x (X.δ (0 : Fin 4)
      (X.map (inc7 0 3 4 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 3 4 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (0 : Fin 4) ≫ inc7 0 3 4 6
        (by decide) (by decide) (by decide) (by decide) = inc6 3 4 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e1 : genEval F2 X x (X.δ (1 : Fin 4)
      (X.map (inc7 0 3 4 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 4 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (1 : Fin 4) ≫ inc7 0 3 4 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 4 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e2 : genEval F2 X x (X.δ (2 : Fin 4)
      (X.map (inc7 0 3 4 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 3 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (2 : Fin 4) ≫ inc7 0 3 4 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 3 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e3 : genEval F2 X x (X.δ (3 : Fin 4)
      (X.map (inc7 0 3 4 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 3 4 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (3 : Fin 4) ≫ inc7 0 3 4 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 3 4 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  rw [e0, e1, e2, e3] at h
  have h' : Fv X x τ 3 4 6
      + (Fv X x τ 0 4 6 + Fv X x τ 0 3 6 + Fv X x τ 0 3 4) = 0 := by
    rw [← h]; abel
  rwa [CharTwo.add_eq_zero] at h'

/-- The cocycle relation for the triple `3,5,6` -/
lemma coc_3_5_6 (hx : cochainDiff F2 X x = 0) :
    Fv X x τ 3 5 6 = Fv X x τ 0 5 6 + Fv X x τ 0 3 6 + Fv X x τ 0 3 5 := by
  have h := cocycle_sum x hx
    (X.map (inc7 0 3 5 6 (by decide) (by decide) (by decide) (by decide)).op τ)
  rw [Fin.sum_univ_four] at h
  simp only [neg_one_pow_F2, one_mul] at h

  have e0 : genEval F2 X x (X.δ (0 : Fin 4)
      (X.map (inc7 0 3 5 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 3 5 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (0 : Fin 4) ≫ inc7 0 3 5 6
        (by decide) (by decide) (by decide) (by decide) = inc6 3 5 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e1 : genEval F2 X x (X.δ (1 : Fin 4)
      (X.map (inc7 0 3 5 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 5 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (1 : Fin 4) ≫ inc7 0 3 5 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 5 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e2 : genEval F2 X x (X.δ (2 : Fin 4)
      (X.map (inc7 0 3 5 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 3 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (2 : Fin 4) ≫ inc7 0 3 5 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 3 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e3 : genEval F2 X x (X.δ (3 : Fin 4)
      (X.map (inc7 0 3 5 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 3 5 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (3 : Fin 4) ≫ inc7 0 3 5 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 3 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  rw [e0, e1, e2, e3] at h
  have h' : Fv X x τ 3 5 6
      + (Fv X x τ 0 5 6 + Fv X x τ 0 3 6 + Fv X x τ 0 3 5) = 0 := by
    rw [← h]; abel
  rwa [CharTwo.add_eq_zero] at h'

/-- The cocycle relation for the triple `4,5,6` -/
lemma coc_4_5_6 (hx : cochainDiff F2 X x = 0) :
    Fv X x τ 4 5 6 = Fv X x τ 0 5 6 + Fv X x τ 0 4 6 + Fv X x τ 0 4 5 := by
  have h := cocycle_sum x hx
    (X.map (inc7 0 4 5 6 (by decide) (by decide) (by decide) (by decide)).op τ)
  rw [Fin.sum_univ_four] at h
  simp only [neg_one_pow_F2, one_mul] at h

  have e0 : genEval F2 X x (X.δ (0 : Fin 4)
      (X.map (inc7 0 4 5 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 4 5 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (0 : Fin 4) ≫ inc7 0 4 5 6
        (by decide) (by decide) (by decide) (by decide) = inc6 4 5 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e1 : genEval F2 X x (X.δ (1 : Fin 4)
      (X.map (inc7 0 4 5 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 5 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (1 : Fin 4) ≫ inc7 0 4 5 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 5 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e2 : genEval F2 X x (X.δ (2 : Fin 4)
      (X.map (inc7 0 4 5 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 4 6 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (2 : Fin 4) ≫ inc7 0 4 5 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 4 6 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  have e3 : genEval F2 X x (X.δ (3 : Fin 4)
      (X.map (inc7 0 4 5 6 (by decide) (by decide) (by decide) (by decide)).op τ))
      = Fv X x τ 0 4 5 := by
    rw [SimplicialObject.δ_def, map_op_comp]
    have hm : SimplexCategory.δ (3 : Fin 4) ≫ inc7 0 4 5 6
        (by decide) (by decide) (by decide) (by decide) = inc6 0 4 5 (by decide) (by decide) (by decide) := by
      refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
      apply Fin.ext
      fin_cases i <;> decide
    rw [hm, Fv_eq]

  rw [e0, e1, e2, e3] at h
  have h' : Fv X x τ 4 5 6
      + (Fv X x τ 0 5 6 + Fv X x τ 0 4 6 + Fv X x τ 0 4 5) = 0 := by
    rw [← h]; abel
  rwa [CharTwo.add_eq_zero] at h'


end

end Work.Pi6.SQ

