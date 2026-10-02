import Mathlib
import Submission.Work.Kunneth.CohKunneth.HomSumStep

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

open Work.Cohomology (dualComplex dualComplexMap Cochain cochainDiff cohomologyClassOf
  cohomologyClassOf_congr)

variable {C : ChainComplex (ModuleCat ℤ) ℕ} {M : ℕ → ModuleCat ℤ}

/-- **The hom–tensor adjunction step**, as an isomorphism of cochain complexes: the dual of
`tpC C (sumShift M)` is `ctens (dualComplex ℤ C) (homDual M)`, with components `tpDualEquiv`. -/
noncomputable def ctensComplexIso [∀ q, Module.Free ℤ ↥(M q)] [∀ q, Module.Finite ℤ ↥(M q)] :
    dualComplex ℤ (tpC C (sumShift M)) ≅ ctens (dualComplex ℤ C) (homDual M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (tpDualEquiv C M n).toModuleIso) (by
      intro n m hnm
      rw [ComplexShape.up_Rel] at hnm
      have hmn : m = n + 1 := hnm.symm
      subst hmn
      apply ModuleCat.hom_ext
      ext f
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ctens_d_hom, dualComplex_d_hom,
        tpC_d, ModuleCat.hom_ofHom, LinearEquiv.toModuleIso_hom]
      show ctensD (dualComplex ℤ C) (homDual M) n (tpDualEquiv C M n f)
        = tpDualEquiv C M (n + 1) (f.comp (tpD C (sumShift M) n))
      exact ctensD_tpDualEquiv C M n f)

/-- The components of the adjunction isomorphism are the degreewise dualities. -/
theorem ctensComplexIso_f [∀ q, Module.Free ℤ ↥(M q)] [∀ q, Module.Finite ℤ ↥(M q)]
    (n : ℕ) :
    (ctensComplexIso (C := C) (M := M)).hom.f n
      = (tpDualEquiv C M n).toModuleIso.hom := rfl

/-- **The value rule of the hom–tensor adjunction step**, on elements of the tensor product. -/
theorem ctensComplexIso_f_apply [∀ q, Module.Free ℤ ↥(M q)] [∀ q, Module.Finite ℤ ↥(M q)]
    (n : ℕ) (γ : tpX C (sumShift M) n →ₗ[ℤ] ℤ) :
    ((ctensComplexIso (C := C) (M := M)).hom.f n).hom
        (show ↥((dualComplex ℤ (tpC C (sumShift M))).X n) from γ)
      = (tpDualEquiv C M n) γ := by
  rw [ctensComplexIso_f, LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom]
  rfl

/-- **The value rule of the hom–tensor adjunction step**: if the `pq`-component of the cochain
`γ` pairs with `u ⊗ h` as `α u * φ h`, then the `pq`-component of `tpDualEquiv γ` is
`α ⊗ φ`. -/
theorem tpDualEquiv_component_value [∀ q, Module.Free ℤ ↥(M q)]
    [∀ q, Module.Finite ℤ ↥(M q)] (n : ℕ) (pq : tpIdx n)
    (α : ↥(C.X pq.1.1) →ₗ[ℤ] ℤ) (φ : ↥(M pq.1.2) →ₗ[ℤ] ℤ)
    (γ : tpX C (sumShift M) n →ₗ[ℤ] ℤ)
    (hγ : ∀ (u : ↥(C.X pq.1.1)) (h : ↥(M pq.1.2)),
        γ (tpLof C (sumShift M) n pq (u ⊗ₜ[ℤ] h)) = α u * φ h) :
    (tpDualEquiv C M n γ) pq = α ⊗ₜ[ℤ] φ := by
  rw [tpDualEquiv_apply_proj]
  apply dualDistrib_injective ↥(C.X pq.1.1) ↥(M pq.1.2)
  ext a h
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply]
  rw [dualDistrib_dualDistribEquivRight, TensorProduct.dualDistrib_apply]
  exact hγ a h

end

end Work.Kunneth
