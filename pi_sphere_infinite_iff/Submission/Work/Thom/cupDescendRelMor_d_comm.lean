import Mathlib
import Submission.Work.Thom.transgressionFleetDefs

set_option autoImplicit false

namespace Work.Thom

open CategoryTheory CategoryTheory.Limits Work.Cohomology
open scoped Simplicial

/-- The `n`-th component of the dual of a chain map, evaluated on a cochain. -/
lemma cupDRM_dualComplexMap_hom_apply (C D : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ D) (n : ℕ)
    (ω : (D.X n) →ₗ[ℤ] ℤ) :
    ModuleCat.Hom.hom ((dualComplexMap ℤ C D f).f n) ω
      = ω.comp (ModuleCat.Hom.hom (f.f n)) :=
  dualComplexMapComp_apply' ℤ C D f n ω

/-- The dual of an epimorphic component of a chain map is injective. -/
lemma cupDRM_dualComplexMap_f_injective (C D : ChainComplex (ModuleCat ℤ) ℕ) (f : C ⟶ D) (n : ℕ)
    (hf : Function.Surjective (ModuleCat.Hom.hom (f.f n))) :
    Function.Injective (ModuleCat.Hom.hom ((dualComplexMap ℤ C D f).f n)) := by
  have hP : ModuleCat.Hom.hom ((dualComplexMap ℤ C D f).f n)
      = LinearMap.dualMap (ModuleCat.Hom.hom (f.f n)) := by
    rw [dualComplexMap_f]; rfl
  rw [hP]
  intro φ ψ h
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := hf y
  exact congrArg (fun g => (g : (C.X n) →ₗ[ℤ] ℤ) x) h

/-- The differential of the dual complex is the simplicial coboundary. -/
lemma cupDRM_dualComplex_d_eq_cochainDiff (X : TopCat) (U V B : Set X) (k : ℕ)
    (φ : (smallInChains U V B).X k →ₗ[ℤ] ℤ) :
    (ModuleCat.Hom.hom ((dualComplex ℤ (smallInChains U V B)).d k (k+1))) φ
      = cochainDiff ℤ (smallInSSet U V B) φ := by
  simp only [dualComplex, CochainComplex.of_d, dualDiff, ModuleCat.hom_ofHom]
  rfl

/-- The inverse transport `XIsoOfEq` cancels a forward cast. -/
lemma cupDRM_XIsoOfEq_inv_hom_cast (K : CochainComplex (ModuleCat ℤ) ℕ) {i j : ℕ} (h : i = j)
    (X : K.X i) : (K.XIsoOfEq h).inv.hom (h ▸ X) = X := by
  cases h; simp

theorem cupDescendRelMor_d_comm (X : TopCat) (U V : Set X) {B C : Set X} (hCB : C ⊆ B)
    (n p : ℕ) (t : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj X) n)
    (ht : t ∈ Work.Cohomology.relKern ℤ X C n)
    (hdt : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) t = 0)
    (ψ : (Work.Cohomology.dualComplex ℤ (Work.Cohomology.smallInChains U V B)).X p) :
    ModuleCat.Hom.hom (Work.Thom.cupDescendRelMor X U V hCB n (p+1) t ht
        (ModuleCat.Hom.hom ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.smallInChains U V B)).d p (p+1)) ψ))
      = ModuleCat.Hom.hom (HomologicalComplex.XIsoOfEq (Work.Cohomology.dualComplex ℤ (Work.Cohomology.relSmallChains U V B C hCB))
            (by omega : (p+1)+n = p+n+1)).inv
          (ModuleCat.Hom.hom ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.relSmallChains U V B C hCB)).d (p+n) (p+n+1))
            (ModuleCat.Hom.hom (Work.Thom.cupDescendRelMor X U V hCB n p t ht ψ))) := by
  have hproof : (by omega : (p+1)+n = p+n+1) = Nat.add_right_comm p 1 n := Subsingleton.elim _ _
  rw [hproof]
  have hepi : Epi ((cokernel.π (subInclChain U V hCB)).f ((p+1)+n)) := by
    have hfac : (cokernel.π (subInclChain U V hCB)).f ((p+1)+n)
        = cokernel.π ((subInclChain U V hCB).f ((p+1)+n))
            ≫ (cokernelComponentIso (subInclChain U V hCB) ((p+1)+n)).inv := by
      rw [← cokernelComponentIso_canon (subInclChain U V hCB) ((p+1)+n), Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    rw [hfac]; infer_instance
  have hsurj : Function.Surjective
      (ModuleCat.Hom.hom ((cokernel.π (subInclChain U V hCB)).f ((p+1)+n))) :=
    (ModuleCat.epi_iff_surjective _).mp hepi
  apply cupDRM_dualComplexMap_f_injective _ _ _ _ hsurj
  let dψ : (smallInChains U V B).X (p+1) →ₗ[ℤ] ℤ :=
    (show (smallInChains U V B).X (p+1) →ₗ[ℤ] ℤ from
      (ModuleCat.Hom.hom ((dualComplex ℤ (smallInChains U V B)).d p (p+1))) ψ)
  have hdψ : cochainDiff ℤ (smallInSSet U V B) ψ = dψ :=
    (cupDRM_dualComplex_d_eq_cochainDiff X U V B p ψ).symm
  have hβ : cochainDiff ℤ (smallInSSet U V B) (restrIn X U V B n t) = 0 :=
    cochainDiff_dualMap_chainComplexMap ℤ (smallInSubcomplex U V B).ι t hdt
  have hL : (ModuleCat.Hom.hom ((dualComplexMap ℤ (smallInChains U V B) (relSmallChains U V B C hCB)
        (cokernel.π (subInclChain U V hCB))).f ((p+1)+n)))
        (ModuleCat.Hom.hom (cupDescendRelMor X U V hCB n (p+1) t ht
          (ModuleCat.Hom.hom ((dualComplex ℤ (smallInChains U V B)).d p (p+1)) ψ)))
      = ModuleCat.Hom.hom (cupHom ℤ (smallInSSet U V B)
          (ModuleCat.Hom.hom ((dualComplex ℤ (smallInChains U V B)).d p (p+1)) ψ)
          (restrIn X U V B n t)) := by
    rw [cupDRM_dualComplexMap_hom_apply, ← ModuleCat.hom_comp, cupDescendRelMor_spec]
  have hLp : (ModuleCat.Hom.hom ((dualComplexMap ℤ (smallInChains U V B) (relSmallChains U V B C hCB)
        (cokernel.π (subInclChain U V hCB))).f (p+n)))
        (ModuleCat.Hom.hom (cupDescendRelMor X U V hCB n p t ht ψ))
      = ModuleCat.Hom.hom (cupHom ℤ (smallInSSet U V B) ψ (restrIn X U V B n t)) := by
    rw [cupDRM_dualComplexMap_hom_apply, ← ModuleCat.hom_comp, cupDescendRelMor_spec]
  have hR_A : (ModuleCat.Hom.hom ((dualComplexMap ℤ (smallInChains U V B) (relSmallChains U V B C hCB)
        (cokernel.π (subInclChain U V hCB))).f ((p+1)+n)))
        ((ModuleCat.Hom.hom (HomologicalComplex.XIsoOfEq
          (dualComplex ℤ (relSmallChains U V B C hCB)) (Nat.add_right_comm p 1 n)).inv)
          ((ModuleCat.Hom.hom ((dualComplex ℤ (relSmallChains U V B C hCB)).d (p+n) (p+n+1)))
            (ModuleCat.Hom.hom (cupDescendRelMor X U V hCB n p t ht ψ))))
      = (ModuleCat.Hom.hom (HomologicalComplex.XIsoOfEq
          (dualComplex ℤ (smallInChains U V B)) (Nat.add_right_comm p 1 n)).inv)
          ((ModuleCat.Hom.hom ((dualComplexMap ℤ (smallInChains U V B) (relSmallChains U V B C hCB)
            (cokernel.π (subInclChain U V hCB))).f (p+n+1)))
            ((ModuleCat.Hom.hom ((dualComplex ℤ (relSmallChains U V B C hCB)).d (p+n) (p+n+1)))
              (ModuleCat.Hom.hom (cupDescendRelMor X U V hCB n p t ht ψ)))) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
    rw [← HomologicalComplex.XIsoOfEq_inv_naturality
        (dualComplexMap ℤ (smallInChains U V B) (relSmallChains U V B C hCB)
          (cokernel.π (subInclChain U V hCB))) (Nat.add_right_comm p 1 n)]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  have hR_B : (ModuleCat.Hom.hom ((dualComplexMap ℤ (smallInChains U V B) (relSmallChains U V B C hCB)
        (cokernel.π (subInclChain U V hCB))).f (p+n+1)))
        ((ModuleCat.Hom.hom ((dualComplex ℤ (relSmallChains U V B C hCB)).d (p+n) (p+n+1)))
          (ModuleCat.Hom.hom (cupDescendRelMor X U V hCB n p t ht ψ)))
      = (ModuleCat.Hom.hom ((dualComplex ℤ (smallInChains U V B)).d (p+n) (p+n+1)))
          ((ModuleCat.Hom.hom ((dualComplexMap ℤ (smallInChains U V B) (relSmallChains U V B C hCB)
            (cokernel.π (subInclChain U V hCB))).f (p+n)))
            (ModuleCat.Hom.hom (cupDescendRelMor X U V hCB n p t ht ψ))) := by
    let Φp : (dualComplex ℤ (relSmallChains U V B C hCB)).X (p+n) :=
      show (dualComplex ℤ (relSmallChains U V B C hCB)).X (p+n) from
        ModuleCat.Hom.hom (cupDescendRelMor X U V hCB n p t ht ψ)
    change (ModuleCat.Hom.hom ((dualComplexMap ℤ (smallInChains U V B) (relSmallChains U V B C hCB)
          (cokernel.π (subInclChain U V hCB))).f (p+n+1)))
          ((ModuleCat.Hom.hom ((dualComplex ℤ (relSmallChains U V B C hCB)).d (p+n) (p+n+1))) Φp)
        = (ModuleCat.Hom.hom ((dualComplex ℤ (smallInChains U V B)).d (p+n) (p+n+1)))
          ((ModuleCat.Hom.hom ((dualComplexMap ℤ (smallInChains U V B) (relSmallChains U V B C hCB)
            (cokernel.π (subInclChain U V hCB))).f (p+n))) Φp)
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
    rw [← HomologicalComplex.Hom.comm
        (dualComplexMap ℤ (smallInChains U V B) (relSmallChains U V B C hCB)
          (cokernel.π (subInclChain U V hCB))) (p+n) (p+n+1)]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  have hLeib : (ModuleCat.Hom.hom ((dualComplex ℤ (smallInChains U V B)).d (p+n) (p+n+1)))
        (ModuleCat.Hom.hom (cupHom ℤ (smallInSSet U V B) ψ (restrIn X U V B n t)))
      = (Nat.add_right_comm p 1 n ▸
          (ModuleCat.Hom.hom (cupHom ℤ (smallInSSet U V B) dψ (restrIn X U V B n t)))) := by
    rw [cupDRM_dualComplex_d_eq_cochainDiff]
    have hleib := cupLeibniz ℤ (smallInSSet U V B) ψ (restrIn X U V B n t)
    rw [show (ModuleCat.Hom.hom (cupHom ℤ (smallInSSet U V B) ψ (restrIn X U V B n t)))
        = cup ℤ (smallInSSet U V B) ψ (restrIn X U V B n t) from rfl]
    rw [hleib, hdψ, hβ]
    have hcup0 : cup ℤ (smallInSSet U V B) ψ
        (0 : (smallInChains U V B).X (n+1) →ₗ[ℤ] ℤ) = 0 := by
      have h := (cupBilinear ℤ (smallInSSet U V B) p (n+1)).2.2.2 (0 : ℤ) ψ
        (0 : (smallInChains U V B).X (n+1) →ₗ[ℤ] ℤ)
      simpa using h
    rw [hcup0, smul_zero, add_zero]
    rfl
  have hCast : (ModuleCat.Hom.hom
        ((dualComplex ℤ (smallInChains U V B)).XIsoOfEq (Nat.add_right_comm p 1 n)).inv)
        (Nat.add_right_comm p 1 n ▸
          (ModuleCat.Hom.hom (cupHom ℤ (smallInSSet U V B) dψ (restrIn X U V B n t))))
      = ModuleCat.Hom.hom (cupHom ℤ (smallInSSet U V B) dψ (restrIn X U V B n t)) :=
    cupDRM_XIsoOfEq_inv_hom_cast (dualComplex ℤ (smallInChains U V B)) (Nat.add_right_comm p 1 n)
      (ModuleCat.Hom.hom (cupHom ℤ (smallInSSet U V B) dψ (restrIn X U V B n t)))
  rw [hL, hR_A, hR_B, hLp, hLeib, hCast]

end Work.Thom
