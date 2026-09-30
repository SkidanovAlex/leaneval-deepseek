import Mathlib
import Submission.Work.SymQuot.NormPoint.Basic
import Submission.Work.SymQuot.NormPoint.detT_mul
import Submission.Work.SymQuot.NormPoint.normVal_eq_evalT

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open TensorProduct
open scoped TensorProduct

universe u

namespace Work.SymQuot.NormPoint

/-- The "change of basis" scalar `v'.det v` is inverse to `v.det v'`.  Both are the
determinant of the (mutually inverse) change-of-basis matrices, and the two top alternating
forms `v.det` and `v'.det` are proportional via `detT_mul_aux_eq_smul_det`. -/
theorem normVal_basis_indep_aux {F : Type u} [Field F] {Q : Type u} [CommRing Q]
    [Algebra F Q] {n : ℕ} (v v' : Module.Basis (Fin n) F Q) :
    (v'.det (⇑v)) * (v.det (⇑v')) = 1 := by
  have hgoal : v'.det ⇑v' = ((v'.det ⇑v) * (v.det ⇑v')) * (v'.det ⇑v') := by
    calc v'.det ⇑v' = ((v'.det ⇑v) • v.det) ⇑v' :=
          congrArg (fun f => f ⇑v') (detT_mul_aux_eq_smul_det v v'.det)
      _ = (v'.det ⇑v) * (v.det ⇑v') := by rw [AlternatingMap.smul_apply, smul_eq_mul]
      _ = (v'.det ⇑v) * (((v.det ⇑v') • v'.det) ⇑v') :=
            congrArg (fun g => (v'.det ⇑v) * (g ⇑v')) (detT_mul_aux_eq_smul_det v' v.det)
      _ = (v'.det ⇑v) * ((v.det ⇑v') * (v'.det ⇑v')) := by
            rw [AlternatingMap.smul_apply, smul_eq_mul]
      _ = ((v'.det ⇑v) * (v.det ⇑v')) * (v'.det ⇑v') := by rw [mul_assoc]
  rw [Module.Basis.det_self] at hgoal
  simpa using hgoal.symm

/-- The linear functional `detT v'` is the scalar `v'.det v` times `detT v`: the space of
"alternating" functionals on the tensor power is one dimensional. -/
theorem normVal_basis_indep_aux2 {F : Type u} [Field F] {Q : Type u} [CommRing Q]
    [Algebra F Q] {n : ℕ} (v v' : Module.Basis (Fin n) F Q) :
    detT v' = (v'.det (⇑v)) • detT v := by
  have h2 : (v'.det).toMultilinearMap = (v'.det (⇑v)) • (v.det).toMultilinearMap := by
    have h := congrArg AlternatingMap.toMultilinearMap (detT_mul_aux_eq_smul_det v v'.det)
    rw [h]
    rfl
  show PiTensorProduct.lift (v'.det).toMultilinearMap =
    (v'.det (⇑v)) • PiTensorProduct.lift (v.det).toMultilinearMap
  rw [h2, map_smul]

theorem normVal_basis_indep {F : Type u} [Field F] {Q : Type u} [CommRing Q] [Algebra F Q]
    {n : ℕ} (v v' : Module.Basis (Fin n) F Q) {t : Tens F Q n} (ht : t ∈ symTensors F Q n) :
    normVal v' t = normVal v t := by
  have hcc : (v'.det (⇑v)) * (v.det (⇑v')) = 1 := normVal_basis_indep_aux v v'
  have hlin : detT v' = (v'.det (⇑v)) • detT v := normVal_basis_indep_aux2 v v'
  calc normVal v' t = detT v' (t * PiTensorProduct.tprod F v') := rfl
    _ = (v'.det (⇑v)) * detT v (t * PiTensorProduct.tprod F v') := by
          rw [hlin, LinearMap.smul_apply, smul_eq_mul]
    _ = (v'.det (⇑v)) * (normVal v t * detT v (PiTensorProduct.tprod F v')) := by
          rw [detT_mul v ht]
    _ = (v'.det (⇑v)) * (normVal v t * (v.det (⇑v'))) := by
          rw [detT_tprod]
    _ = normVal v t := by
          have h4 : (v'.det ⇑v) * (normVal v t * (v.det ⇑v'))
              = normVal v t * ((v'.det ⇑v) * (v.det ⇑v')) := by ring
          rw [h4, hcc, mul_one]

end Work.SymQuot.NormPoint
