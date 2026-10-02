import Mathlib
import Submission.Work.Kunneth.TpDual
import Submission.Work.Kunneth.tpD_comp_tpLof

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Compatibility of `tpDualEquiv` with the differentials

The degreewise duality `Work.Kunneth.tpDualEquiv` between `(tpC C (sumShift M))^*` and
`ctens (dualComplex ℤ C) (homDual M)` is a chain map: transposing the Koszul differential
`∂_C ⊗ 1` gives the differential of `ctens` (there is no Koszul sign, since `sumShift M` has
zero differential).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

set_option backward.isDefEq.respectTransparency false

variable (C : ChainComplex (ModuleCat ℤ) ℕ) (M : ℕ → ModuleCat ℤ)
variable [∀ q, Module.Free ℤ ↥(M q)] [∀ q, Module.Finite ℤ ↥(M q)]

/-- **The `pq`-component of the differential square.**  Tensoring the transpose of
`C.d (p+1) p` with `1` is the same as transposing `C.d (p+1) p ⊗ 1` before applying the
degreewise duality. -/
theorem dTensOut_dualDistribEquivRight (n : ℕ) (pq : tpIdx n)
    (u : ↥(C.X pq.1.1) ⊗[ℤ] ↥(M pq.1.2) →ₗ[ℤ] ℤ) :
    dTensOut (Work.Cohomology.dualComplex ℤ C) (homDual M) pq.1.1 pq.1.2
        (dualDistribEquivRight ↥(C.X pq.1.1) ↥(M pq.1.2) u)
      = dualDistribEquivRight ↥(C.X (pq.1.1 + 1)) ↥(M pq.1.2)
          (u.comp (LinearMap.rTensor (↥(M pq.1.2)) ((C.d (pq.1.1 + 1) pq.1.1).hom))) := by
  rw [dTensOut, dualComplex_d_hom]
  apply dualDistrib_injective ↥(C.X (pq.1.1 + 1)) ↥(M pq.1.2)
  ext a n
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply]
  show TensorProduct.dualDistrib ℤ ↥(C.X (pq.1.1 + 1)) ↥(M pq.1.2)
        (LinearMap.rTensor (↥(M pq.1.2) →ₗ[ℤ] ℤ)
          (LinearMap.dualMap ((C.d (pq.1.1 + 1) pq.1.1).hom))
          (dualDistribEquivRight ↥(C.X pq.1.1) ↥(M pq.1.2) u)) (a ⊗ₜ[ℤ] n)
      = TensorProduct.dualDistrib ℤ ↥(C.X (pq.1.1 + 1)) ↥(M pq.1.2)
          (dualDistribEquivRight ↥(C.X (pq.1.1 + 1)) ↥(M pq.1.2)
            (u.comp (LinearMap.rTensor (↥(M pq.1.2)) ((C.d (pq.1.1 + 1) pq.1.1).hom))))
          (a ⊗ₜ[ℤ] n)
  rw [dualDistrib_natural (A := ↥(C.X (pq.1.1 + 1))) (N := ↥(M pq.1.2))
      (A' := ↥(C.X pq.1.1)) (d := (C.d (pq.1.1 + 1) pq.1.1).hom)
      (y := dualDistribEquivRight ↥(C.X pq.1.1) ↥(M pq.1.2) u) a n]
  rw [dualDistrib_dualDistribEquivRight]
  rw [dualDistrib_dualDistribEquivRight, LinearMap.comp_apply, LinearMap.rTensor_tmul]

/-- The `tpStep`-component of the compatibility of `tpDualEquiv` with the differentials. -/
theorem ctensD_tpDualEquiv_tpStep (n : ℕ) (f : tpX C (sumShift M) n →ₗ[ℤ] ℤ) (pq : tpIdx n) :
    ctensD (Work.Cohomology.dualComplex ℤ C) (homDual M) n (tpDualEquiv C M n f) (tpStep n pq)
      = tpDualEquiv C M (n + 1) (f.comp (tpD C (sumShift M) n)) (tpStep n pq) := by
  rw [ctensD_apply_step (Work.Cohomology.dualComplex ℤ C) (homDual M) n
      (tpDualEquiv C M n f) pq, tpDualEquiv_apply_proj, tpDualEquiv_apply_proj]
  rw [LinearMap.comp_assoc, tpD_comp_tpLof, tpDpq_sumShift_tpStep, ← LinearMap.comp_assoc]
  rw [tensorProduct_map_id_eq_rTensor]
  rw [dTensOut_dualDistribEquivRight]
  rfl

/-- The `tpZero`-component of the compatibility of `tpDualEquiv` with the differentials. -/
theorem ctensD_tpDualEquiv_tpZero (n : ℕ) (f : tpX C (sumShift M) n →ₗ[ℤ] ℤ) :
    ctensD (Work.Cohomology.dualComplex ℤ C) (homDual M) n (tpDualEquiv C M n f) (tpZero n)
      = tpDualEquiv C M (n + 1) (f.comp (tpD C (sumShift M) n)) (tpZero n) := by
  rw [ctensD_apply_zero, tpDualEquiv_apply_proj, LinearMap.comp_assoc, tpD_comp_tpLof,
    tpDpq_sumShift_tpZero, LinearMap.comp_zero, map_zero]

/-- **`tpDualEquiv` is compatible with the differentials.** -/
theorem ctensD_tpDualEquiv (n : ℕ) (f : tpX C (sumShift M) n →ₗ[ℤ] ℤ) :
    ctensD (Work.Cohomology.dualComplex ℤ C) (homDual M) n (tpDualEquiv C M n f)
      = tpDualEquiv C M (n + 1) (f.comp (tpD C (sumShift M) n)) := by
  apply DirectSum.ext
  intro r
  by_cases hr : r.1.1 = 0
  · have hrz : r = tpZero n := eq_tpZero_of_fst_eq_zero hr
    subst hrz
    exact ctensD_tpDualEquiv_tpZero C M n f
  · have hpos : 1 ≤ r.1.1 := by omega
    rw [eq_tpStep_of_pos hpos]
    exact ctensD_tpDualEquiv_tpStep C M n f _

/-! ## A bookkeeping lemma for the assembly -/

/-- The `n`-th differential of `ctens A T` as a linear map. -/
theorem ctens_d_hom (A : CochainComplex (ModuleCat ℤ) ℕ) (T : ℕ → ModuleCat ℤ) (n : ℕ) :
    ModuleCat.Hom.hom ((ctens A T).d n (n + 1)) = ctensD A T n := by
  rw [ctens_d, ModuleCat.hom_ofHom]

end

end Work.Kunneth
