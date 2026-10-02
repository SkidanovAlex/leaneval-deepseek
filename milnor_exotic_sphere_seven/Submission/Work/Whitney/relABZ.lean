import Mathlib
import Submission.Work.Whitney.relABQuasiIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `A+B` cochain complex as the `ℤ`-dual of `C_*(X)/(C_*(A)+C_*(B))`

For open `A, B ⊆ X` and a commutative ring `R`, this file identifies the `A+B` cochain complex
`C^*(X, A+B;R) = C^*(X,A;R) ∩ C^*(X,B;R)` with the `ℤ`-dual of `C_*(X)/(C_*(A)+C_*(B))`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Simplicial
open scoped Simplicial

namespace Work.Whitney

open Work.Cohomology

noncomputable section

section E2

variable {M : TopCat} (A B : Set M)

noncomputable def abZEquiv (R : Type) [CommRing R] (n : ℕ) :
    (((cokernel (smallToSing A B)).X n) →ₗ[ℤ] R) ≃ₗ[R] (pdABKernR (R := R) M A B n) :=
  LinearEquiv.ofBijective (abZLM (A := A) (B := B) (R := R) n)
    ⟨abZLM_injective (A := A) (B := B) (R := R) n,
     abZLM_surjective (A := A) (B := B) (R := R) n⟩

lemma abZEquiv_apply_coe (R : Type) [CommRing R] (n : ℕ)
    (φ : ((cokernel (smallToSing A B)).X n) →ₗ[ℤ] R) :
    (abZEquiv (A := A) (B := B) (R := R) n φ).1
      = cochCoeffEquiv R M n (φ.comp ((cokernel.π (smallToSing A B)).f n).hom) := by
  rw [show (abZEquiv (A := A) (B := B) (R := R) n φ : ↥(pdABKernR (R := R) M A B n))
      = abZLM (A := A) (B := B) (R := R) n φ from
        LinearEquiv.ofBijective_apply _ φ, abZLM_apply]

set_option maxHeartbeats 4000000 in
/-- The differential of the `A+B` complex, evaluated on chains. -/
lemma pdABDiffLMR_cochainLM (R : Type) [CommRing R] (n : ℕ)
    (Θ : ↥(pdABKernR (R := R) M A B n)) (x : (singularChains R M).X (n+1)) :
    cochainLM R M (n+1) (pdABDiffLMR (R := R) M A B n Θ).1 x
      = cochainLM R M n Θ.1 (((singularChains R M).d (n+1) n).hom x) := by
  rw [pdABDiffLMR_coe]
  rw [show (singularCochainComplex R M).d n (n+1) = dualDifferential R M n from
    CochainComplex.of_d (dualChains R M) (dualDifferential R M) n]
  rfl

set_option maxHeartbeats 4000000 in
lemma abZEquiv_comm_apply (R : Type) [CommRing R] (n : ℕ)
    (φ : ((cokernel (smallToSing A B)).X n) →ₗ[ℤ] R) :
    abZEquiv (A := A) (B := B) (R := R) (n+1) ((dualZDiffCompat R (cokernel (smallToSing A B)) n) φ)
      = (pdABDiffLMR (R := R) M A B n) (abZEquiv (A := A) (B := B) (R := R) n φ) := by
  have hcomm : (((cokernel (smallToSing A B)).d (n+1) n).hom.comp
        ((cokernel.π (smallToSing A B)).f (n+1)).hom)
      = (((cokernel.π (smallToSing A B)).f n).hom.comp
        ((singularChains ℤ M).d (n+1) n).hom) := by
    have h := congrArg ModuleCat.Hom.hom ((cokernel.π (smallToSing A B)).comm (n+1) n)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
    exact h
  apply Subtype.ext
  show cochainLM R M (n+1) ((abZEquiv (A := A) (B := B) (R := R) (n+1)
        ((dualZDiffCompat R (cokernel (smallToSing A B)) n) φ)).1)
      = cochainLM R M (n+1) ((pdABDiffLMR (R := R) M A B n
        (abZEquiv (A := A) (B := B) (R := R) n φ)).1)
  apply singularFunc_ext_R
  intro σ
  have hL : cochainLM R M (n+1) ((abZEquiv (A := A) (B := B) (R := R) (n+1)
        ((dualZDiffCompat R (cokernel (smallToSing A B)) n) φ)).1) (genR R M (n+1) σ)
      = φ (((cokernel (smallToSing A B)).d (n+1) n).hom
          (((cokernel.π (smallToSing A B)).f (n+1)).hom (genZ M (n+1) σ))) := by
    simp only [cochainLM, abZEquiv_apply_coe, cochCoeffEquiv_apply_gen, LinearMap.comp_apply]
    exact dualZDiffCompat_apply R (cokernel (smallToSing A B)) n φ
      (((cokernel.π (smallToSing A B)).f (n+1)).hom (genZ M (n+1) σ))
  have hR : cochainLM R M (n+1) ((pdABDiffLMR (R := R) M A B n
        (abZEquiv (A := A) (B := B) (R := R) n φ)).1) (genR R M (n+1) σ)
      = φ (((cokernel (smallToSing A B)).d (n+1) n).hom
          (((cokernel.π (smallToSing A B)).f (n+1)).hom (genZ M (n+1) σ))) := by
    have hkey : (((cokernel (smallToSing A B)).d (n+1) n).hom
          (((cokernel.π (smallToSing A B)).f (n+1)).hom (genZ M (n+1) σ)))
        = ((cokernel.π (smallToSing A B)).f n).hom
          (((singularChains ℤ M).d (n+1) n).hom (genZ M (n+1) σ)) :=
      LinearMap.congr_fun hcomm (genZ M (n+1) σ)
    rw [pdABDiffLMR_cochainLM, abZEquiv_apply_coe]
    simp only [cochainLM]
    rw [← LinearMap.comp_apply,
      ← cochCoeffEquiv_comm_d R M n (φ.comp ((cokernel.π (smallToSing A B)).f n).hom),
      cochCoeffEquiv_apply_gen, LinearMap.comp_apply, LinearMap.comp_apply, ← hkey]
  rw [hL, hR]

end E2

section E2Iso

variable {M : TopCat} (A B : Set M)

/-- The degreewise isomorphism `Hom_ℤ(C_n(X)/(C_n(A)+C_n(B)), R) ≅ C^n(X,A+B;R)`. -/
def abZIso (R : Type) [CommRing R] (n : ℕ) :
    (dualZCompat R (cokernel (smallToSing A B))).X n ≅ (pdABCohR (R := R) M A B).X n :=
  LinearEquiv.toModuleIso (abZEquiv (A := A) (B := B) (R := R) n)

/-- The forward map of `abZIso` is `abZEquiv`. -/
@[simp]
lemma abZIso_hom (R : Type) [CommRing R] (n : ℕ) :
    (abZIso (A := A) (B := B) (R := R) n).hom = ModuleCat.ofHom
      ((abZEquiv (A := A) (B := B) (R := R) n) :
        (((cokernel (smallToSing A B)).X n) →ₗ[ℤ] R) →ₗ[R] (pdABKernR (R := R) M A B n)) :=
  rfl

/-- **The degreewise isomorphisms commute with the differentials.** -/
lemma abZIso_comm (R : Type) [CommRing R] (n : ℕ) :
    (abZIso (A := A) (B := B) (R := R) n).hom ≫ (pdABCohR (R := R) M A B).d n (n+1)
      = (dualZCompat R (cokernel (smallToSing A B))).d n (n+1)
        ≫ (abZIso (A := A) (B := B) (R := R) (n+1)).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, abZIso_hom, ModuleCat.hom_ofHom,
    pdABCohR_d, dualZCompat_d, pdABDiffR]
  exact (abZEquiv_comm_apply (A := A) (B := B) (R := R) n φ).symm

/-- **The `A+B` cochain complex with coefficients in `R` is the `ℤ`-dual of
`C_*(X)/(C_*(A)+C_*(B))`.** -/
noncomputable def pdABCohIsoDualZ (R : Type) [CommRing R] :
    pdABCohR (R := R) M A B ≅ dualZCompat R (cokernel (smallToSing A B)) :=
  (HomologicalComplex.Hom.isoOfComponents (fun n => abZIso (A := A) (B := B) (R := R) n)
    (fun i j hij => by
      rw [← hij]
      exact abZIso_comm (A := A) (B := B) (R := R) i)).symm

/-- The `n`-th component of `pdABCohIsoDualZ`. -/
lemma pdABCohIsoDualZ_hom_f (R : Type) [CommRing R] (n : ℕ) :
    (pdABCohIsoDualZ (A := A) (B := B) (R := R)).hom.f n
      = (abZIso (A := A) (B := B) (R := R) n).inv := rfl

end E2Iso

section Square

variable {M : TopCat} (A B : Set M)

/-- The canonical isomorphism `C^*(X,A;R) ≅ Hom_ℤ(C_*(X,A), R)`, built from the degreewise
isomorphisms `relZIso`. -/
noncomputable def relCohIsoDualZ (R : Type) [CommRing R] (X : TopCat) (A : Set X) :
    relComplex R X A ≅ dualZCompat R (relChains X A) :=
  (HomologicalComplex.Hom.isoOfComponents (fun n => relZIso R X A n)
    (fun i j hij => by
      rw [← hij]
      exact relZIso_comm R X A i)).symm

/-- The `n`-th component of `relCohIsoDualZ` is the inverse of `relZIso`. -/
lemma relCohIsoDualZ_hom_f (R : Type) [CommRing R] (X : TopCat) (A : Set X) (n : ℕ) :
    (relCohIsoDualZ R X A).hom.f n = (relZIso R X A n).inv := rfl

/-- The inverse of `relZIso` is the inverse of `relZEquiv`. -/
lemma relZIso_inv (R : Type) [CommRing R] (X : TopCat) (A : Set X) (n : ℕ) :
    (relZIso R X A n).inv = ModuleCat.ofHom ((relZEquiv R X A n).symm :
      ↥(relKern R X A n) →ₗ[R] (((relChains X A).X n) →ₗ[ℤ] R)) := rfl

/-- The inverse of `abZIso` is the inverse of `abZEquiv`. -/
lemma abZIso_inv (R : Type) [CommRing R] (n : ℕ) :
    (abZIso (A := A) (B := B) (R := R) n).inv = ModuleCat.ofHom
      (((abZEquiv (A := A) (B := B) (R := R) n).symm) :
        ↥(pdABKernR (R := R) M A B n) →ₗ[R] (((cokernel (smallToSing A B)).X n) →ₗ[ℤ] R)) :=
  rfl

/-- The composite of `relABq` with the projection to the cokernel is the projection to
`C_*(X)/C_*(A∪B)`. -/
lemma relABq_comp_proj (n : ℕ) :
    ((relABq A B).f n).hom.comp ((cokernel.π (smallToSing A B)).f n).hom
      = (relDualProj M (A ∪ B) n).hom := by
  have h : ((cokernel.π (smallToSing A B)).f n ≫ (relABq A B).f n)
      = relDualProj M (A ∪ B) n := by
    rw [← HomologicalComplex.comp_f]
    show (cokernel.π (smallToSing A B) ≫ relABq A B).f n
      = (cokernel.π (inclChains M (A ∪ B))).f n
    rw [show relABq A B = cokernel.desc (smallToSing A B)
        (cokernel.π (inclChains M (A ∪ B))) _ from rfl, cokernel.π_desc]
  have h2 := congrArg ModuleCat.Hom.hom h
  rwa [ModuleCat.hom_comp] at h2

/-- The `A+B` inclusion does not change the underlying cochain. -/
lemma pdABInclRelR_f_apply_coe (R : Type) [CommRing R] (n : ℕ)
    (ψ : (relComplex R M (A ∪ B)).X n) :
    ((pdABInclRelR (R := R) M A B).f n ψ).1 = ψ.1 := rfl

/-- The inverse of `relZEquiv` is characterised by composing with the projection. -/
lemma relZEquiv_symm_comp (R : Type) [CommRing R] (X : TopCat) (A : Set X) (n : ℕ)
    (Θ : ↥(relKern R X A n)) :
    ((relZEquiv R X A n).symm Θ).comp (relDualProj X A n).hom
      = (cochCoeffEquiv R X n).symm Θ.1 := by
  have h2 := relZEquiv_apply_coe R X A n ((relZEquiv R X A n).symm Θ)
  rw [LinearEquiv.apply_symm_apply] at h2
  refine (cochCoeffEquiv R X n).injective ?_
  rw [LinearEquiv.apply_symm_apply]
  exact h2.symm

/-- The inverse of `abZEquiv` is characterised by composing with the projection. -/
lemma abZEquiv_symm_comp (R : Type) [CommRing R] (n : ℕ)
    (Θ : ↥(pdABKernR (R := R) M A B n)) :
    ((abZEquiv (A := A) (B := B) (R := R) n).symm Θ).comp
        ((cokernel.π (smallToSing A B)).f n).hom
      = (cochCoeffEquiv R M n).symm Θ.1 := by
  have h2 := abZEquiv_apply_coe (A := A) (B := B) (R := R) n
    ((abZEquiv (A := A) (B := B) (R := R) n).symm Θ)
  rw [LinearEquiv.apply_symm_apply] at h2
  refine (cochCoeffEquiv R M n).injective ?_
  rw [LinearEquiv.apply_symm_apply]
  exact h2.symm

set_option maxHeartbeats 8000000 in
/-- **The square** relating the inclusion `C^*(X,A∪B) ⟶ C^*(X,A+B)` to the quotient map
`C_*(X)/(C_*(A)+C_*(B)) ⟶ C_*(X)/C_*(A∪B)`. -/
theorem pdABInclRelR_square (R : Type) [CommRing R] {M : TopCat} (A B : Set M) :
    pdABInclRelR (R := R) M A B ≫ (pdABCohIsoDualZ (A := A) (B := B) (R := R)).hom
      = (relCohIsoDualZ R M (A ∪ B)).hom
        ≫ dualZMapCompat R (cokernel (smallToSing A B)) (relChains M (A ∪ B)) (relABq A B) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  rw [pdABCohIsoDualZ_hom_f, relCohIsoDualZ_hom_f, dualZMapCompat_f, abZIso_inv, relZIso_inv]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ψ
  show (abZEquiv (A := A) (B := B) (R := R) n).symm ((pdABInclRelR (R := R) M A B).f n ψ)
      = ((relZEquiv R M (A ∪ B) n).symm ψ).comp ((relABq A B).f n).hom
  exact LinearMap.lcomp_injective_of_surjective (S := R) (N := R)
    ((cokernel.π (smallToSing A B)).f n).hom (cokerSmall_surjective A B n) (by
      rw [LinearMap.lcomp_apply', LinearMap.lcomp_apply', LinearMap.comp_assoc,
        abZEquiv_symm_comp, relABq_comp_proj, relZEquiv_symm_comp,
        pdABInclRelR_f_apply_coe])

end Square

section QuasiIso

variable {M : TopCat} (A B : Set M)

set_option maxHeartbeats 8000000 in
/-- **The inclusion `C^*(X,A∪B;R) ⟶ C^*(X,A+B;R)` is a quasi-isomorphism.** -/
theorem pdABInclRelR_quasiIso (R : Type) [CommRing R] (hA : IsOpen A) (hB : IsOpen B)
    (n : ℕ) : IsIso (HomologicalComplex.homologyMap (pdABInclRelR (R := R) M A B) n) := by
  let f := HomologicalComplex.homologyMap (pdABInclRelR (R := R) M A B) n
  let g := HomologicalComplex.homologyMap
    (pdABCohIsoDualZ (A := A) (B := B) (R := R)).hom n
  haveI hg : IsIso g :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n)
      (pdABCohIsoDualZ (A := A) (B := B) (R := R)).hom
  haveI hE : IsIso (HomologicalComplex.homologyMap (relCohIsoDualZ R M (A ∪ B)).hom n) :=
    Functor.map_isIso (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) n)
      (relCohIsoDualZ R M (A ∪ B)).hom
  haveI hBq : IsIso (HomologicalComplex.homologyMap (dualZMapCompat R (cokernel (smallToSing A B))
      (relChains M (A ∪ B)) (relABq A B)) n) :=
    relABq_dualZ_quasiIso R hA hB n
  have hsq := congrArg (fun k => HomologicalComplex.homologyMap k n)
    (pdABInclRelR_square (R := R) A B)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq
  haveI hfg : IsIso (f ≫ g) := hsq.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_right f g

end QuasiIso

end
end Work.Whitney
