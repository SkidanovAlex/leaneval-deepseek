import Mathlib
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Cohomology.DualComplexMap
import Submission.Work.Cohomology.relCochain_shortExact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative cochains are the duals of the relative chains, over any coefficient ring

`Submission/Work/Cohomology/relCochainDual.lean` proves `C^*(X,A) ≅ Hom_ℤ(C_*(X,A), ℤ)` for the
`ℤ`-coefficient relative chain complex.  This file is the coefficient-generic version:

  `relComplexIsoDualR : relComplex R X A ≅ dualComplex R (relChainsR R X A)`.

The argument is the same as in the integral case: `C^*(X,A)` is the kernel of the restriction
`C^*(X) ⟶ C^*(A)`, `C_*(X,A)` is the cokernel of the inclusion `C_*(A) ⟶ C_*(X)`, and
`Hom_R(-,R)` carries cokernels of `R`-modules to kernels.  Over a field this is the missing half of
the universal coefficient theorem `H^n(X,A;F) ≅ Hom_F(H_n(X,A;F), F)` (the other half being
`Work.StemsB.fieldDualUCT`); together they turn *homological* computations into *cohomological*
ones, which is what subproject SERRE's `C2` odd step needs at `ℚ`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open Work.Cohomology

namespace Work.StemsB

noncomputable section

variable (R : Type) [CommRing R]
variable (X : TopCat) (A : Set X)

/-! ## The quotient map `C_*(X) ⟶ C_*(X,A)` -/

/-- The `n`-th component of the quotient map `C_*(X;R) ⟶ C_*(X,A;R)`. -/
abbrev rdRProj (n : ℕ) :
    (Work.Cohomology.singularChains R X).X n ⟶ (relChainsR R X A).X n :=
  (cokernel.π (relChainsRIncl R X A)).f n

/-- The quotient map is surjective in every degree. -/
lemma rdRProj_surjective (n : ℕ) : Function.Surjective (rdRProj R X A n).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- The composite `C_*(A) ⟶ C_*(X) ⟶ C_*(X,A)` vanishes. -/
lemma rdRProj_incl_apply (n : ℕ) (y : ↥((Work.Cohomology.singularChains R (TopCat.of A)).X n)) :
    (rdRProj R X A n) ((relChainsRIncl R X A).f n y) = 0 := by
  have h3 : (0 : Work.Cohomology.singularChains R (TopCat.of A) ⟶
      cokernel (relChainsRIncl R X A)).f n
      = (relChainsRIncl R X A).f n ≫ rdRProj R X A n := by
    rw [rdRProj, ← HomologicalComplex.comp_f, cokernel.condition]
  have h4 := congrArg (fun (k : (Work.Cohomology.singularChains R (TopCat.of A)).X n ⟶
      (cokernel (relChainsRIncl R X A)).X n) => k y) h3
  exact h4.symm

/-- **The kernel of the quotient map is the image of the chains of `A`.** -/
lemma rdRProj_ker (n : ℕ) :
    LinearMap.ker (rdRProj R X A n).hom
      = LinearMap.range ((relChainsRIncl R X A).f n).hom := by
  let S : ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
    ShortComplex.mk (relChainsRIncl R X A) (cokernel.π (relChainsRIncl R X A))
      (cokernel.condition _)
  have hex : S.Exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
  have hd : (S.map (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n)).Exact :=
    (HomologicalComplex.exact_iff_degreewise_exact S).1 hex n
  have h := (ShortComplex.moduleCat_exact_iff
    (S.map (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n))).1 hd
  have hg : (S.map (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n)).g
      = (cokernel.π (relChainsRIncl R X A)).f n := by
    rw [ShortComplex.map_g]; rfl
  have hf : (S.map (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n)).f
      = (relChainsRIncl R X A).f n := by
    rw [ShortComplex.map_f]; rfl
  rw [hg, hf] at h
  refine le_antisymm ?_ ?_
  · rintro z hz
    exact h z hz
  · rintro z ⟨y, rfl⟩
    show (rdRProj R X A n) ((relChainsRIncl R X A).f n y) = 0
    exact rdRProj_incl_apply R X A n y

/-- Exactness of the pair in degree `n`, in the form of `Function.Exact`. -/
lemma rdRProj_exact (n : ℕ) :
    Function.Exact (⇑((relChainsRIncl R X A).f n).hom) (⇑(rdRProj R X A n).hom) := by
  intro y
  rw [Set.mem_range]
  constructor
  · intro hy
    have hy' : y ∈ LinearMap.ker (rdRProj R X A n).hom := hy
    rw [rdRProj_ker] at hy'
    exact hy'
  · rintro ⟨x, rfl⟩
    exact rdRProj_incl_apply R X A n x

/-- Naturality of the quotient map with respect to the differentials. -/
lemma rdRProj_comm (n : ℕ) :
    rdRProj R X A (n + 1) ≫ (relChainsR R X A).d (n + 1) n
      = (Work.Cohomology.singularChains R X).d (n + 1) n ≫ rdRProj R X A n :=
  (cokernel.π (relChainsRIncl R X A)).comm (n + 1) n

/-- Naturality of the quotient map, as linear maps. -/
lemma rdRProj_comm_lm (n : ℕ) :
    ((relChainsR R X A).d (n + 1) n).hom.comp (rdRProj R X A (n + 1)).hom
      = (rdRProj R X A n).hom.comp ((Work.Cohomology.singularChains R X).d (n + 1) n).hom := by
  have h := congrArg ModuleCat.Hom.hom (rdRProj_comm R X A n)
  rwa [ModuleCat.hom_comp, ModuleCat.hom_comp] at h

/-! ## The relative cochains as functionals on chains -/

/-- An element of the cochain module of `X`, viewed as a functional on chains. -/
def rdRLM (n : ℕ) (φ : ↥((singularCochainComplex R X).X n)) :
    ↥((Work.Cohomology.singularChains R X).X n) →ₗ[R] R :=
  show ↥((Work.Cohomology.singularChains R X).X n) →ₗ[R] R from φ

/-- **Membership criterion for the relative cochains**. -/
lemma rdRKern_iff (n : ℕ) (φ : ↥((singularCochainComplex R X).X n)) :
    φ ∈ relKern R X A n ↔ ∀ y : ↥((Work.Cohomology.singularChains R (TopCat.of A)).X n),
      rdRLM R X n φ ((relChainsRIncl R X A).f n y) = 0 := by
  have key : ∀ y : ↥((Work.Cohomology.singularChains R (TopCat.of A)).X n),
      (show ↥((Work.Cohomology.singularChains R (TopCat.of A)).X n) →ₗ[R] R
        from ((restr R X A).f n).hom φ) y
        = rdRLM R X n φ ((relChainsRIncl R X A).f n y) :=
    fun y => LinearMap.dualMap_apply _ _ y
  constructor
  · intro h y
    have h1 : (show ↥((Work.Cohomology.singularChains R (TopCat.of A)).X n) →ₗ[R] R
        from ((restr R X A).f n).hom φ) = 0 := h
    rw [← key y, h1]
    rfl
  · intro h
    have h1 : (show ↥((Work.Cohomology.singularChains R (TopCat.of A)).X n) →ₗ[R] R
        from ((restr R X A).f n).hom φ) = 0 := by
      ext y
      rw [key y]
      simpa using h y
    exact h1

/-- The membership criterion in the form in which it will be used. -/
lemma rdRKern_iff' (n : ℕ) (φ : ↥((Work.Cohomology.singularChains R X).X n) →ₗ[R] R) :
    (φ : ↥((singularCochainComplex R X).X n)) ∈ relKern R X A n ↔
      ∀ y : ↥((Work.Cohomology.singularChains R (TopCat.of A)).X n),
        φ ((relChainsRIncl R X A).f n y) = 0 :=
  rdRKern_iff R X A n φ

/-- The value of the differential of the relative cochains on a chain. -/
lemma rdRDiff_apply (n : ℕ) (φ : relKern R X A n)
    (x : ↥((Work.Cohomology.singularChains R X).X (n + 1))) :
    rdRLM R X (n + 1) (relDiff R X A n φ).1 x
      = rdRLM R X n φ.1 ((Work.Cohomology.singularChains R X).d (n + 1) n x) := by
  rw [show (relDiff R X A n φ).1 = (relDiffLM R X A n φ).1 from rfl, relDiffLM_coe]
  rw [show ((singularCochainComplex R X).d n (n + 1)) = dualDifferential R X n from
    CochainComplex.of_d (dualChains R X) (dualDifferential R X) n]
  rfl

/-- The differential of the relative cochains, as a linear map. -/
lemma rdRDiff_apply_coe (n : ℕ) (ψ : relKern R X A n) :
    rdRLM R X (n + 1) (relDiff R X A n ψ).1
      = (rdRLM R X n ψ.1).comp ((Work.Cohomology.singularChains R X).d (n + 1) n).hom := by
  ext x
  rw [rdRDiff_apply, LinearMap.comp_apply]

/-! ## `Hom_R(C_*(X,A), R)` as the relative cochains -/

/-- **The dual of the quotient map**: a functional on the relative `n`-chains pulls back along
`p_n` to a relative `n`-cochain. -/
def rdRMap (n : ℕ) :
    (↥((relChainsR R X A).X n) →ₗ[R] R) →ₗ[R] (relKern R X A n) :=
  ((rdRProj R X A n).hom.dualMap).codRestrict (relKern R X A n) (fun f => by
    rw [rdRKern_iff]
    intro y
    show f ((rdRProj R X A n) ((relChainsRIncl R X A).f n y)) = 0
    rw [rdRProj_incl_apply R X A n y]
    simp)

/-- The value of `rdRMap`. -/
lemma rdRMap_apply (n : ℕ) (f : ↥((relChainsR R X A).X n) →ₗ[R] R)
    (x : ↥((Work.Cohomology.singularChains R X).X n)) :
    rdRLM R X n (rdRMap R X A n f).1 x = f ((rdRProj R X A n) x) := by
  simp only [rdRMap, LinearMap.codRestrict_apply, rdRLM]
  exact LinearMap.dualMap_apply _ _ x

/-- `rdRMap` is composition with `p_n`. -/
lemma rdRMap_apply_coe (n : ℕ) (f : ↥((relChainsR R X A).X n) →ₗ[R] R) :
    rdRLM R X n (rdRMap R X A n f).1 = f.comp (rdRProj R X A n).hom := by
  ext x
  rw [rdRMap_apply, LinearMap.comp_apply]

/-- `rdRMap` is injective, since `p_n` is surjective. -/
lemma rdRMap_injective (n : ℕ) : Function.Injective (rdRMap R X A n) := by
  have hinj := LinearMap.lcomp_injective_of_surjective (S := R) (N := R)
    (rdRProj R X A n).hom (rdRProj_surjective R X A n)
  intro f g h
  have h2 : (rdRMap R X A n f).1 = (rdRMap R X A n g).1 := congrArg Subtype.val h
  have h3 : rdRLM R X n (rdRMap R X A n f).1 = rdRLM R X n (rdRMap R X A n g).1 := h2
  rw [rdRMap_apply_coe, rdRMap_apply_coe] at h3
  refine hinj ?_
  rw [LinearMap.lcomp_apply' (S := R) (N := R), LinearMap.lcomp_apply' (S := R) (N := R)]
  exact h3

/-- `rdRMap` is surjective: a cochain vanishing on the chains of `A` factors through `p_n`.
This is the left exactness of `Hom_R(-, R)`. -/
lemma rdRMap_surjective (n : ℕ) : Function.Surjective (rdRMap R X A n) := by
  intro φ
  have hex := LinearMap.exact_lcomp_of_exact_of_surjective (N := R) (rdRProj_exact R X A n)
    (rdRProj_surjective R X A n)
  have hφ : (LinearMap.lcomp (S := R) (N := R) ((relChainsRIncl R X A).f n).hom)
      (rdRLM R X n φ.1) = 0 := by
    ext x
    rw [LinearMap.lcomp_apply, LinearMap.zero_apply]
    exact (rdRKern_iff R X A n φ.1).1 φ.2 x
  obtain ⟨h, hh⟩ := (hex (rdRLM R X n φ.1)).1 hφ
  have hh' : h.comp (rdRProj R X A n).hom = rdRLM R X n φ.1 := by
    rw [← LinearMap.lcomp_apply' (S := R) (N := R)]; exact hh
  refine ⟨h, ?_⟩
  apply Subtype.ext
  show rdRLM R X n (rdRMap R X A n h).1 = rdRLM R X n φ.1
  rw [rdRMap_apply_coe]
  exact hh'

/-- **The degreewise isomorphism** `Hom_R(C_n(X,A;R), R) ≃ C^n(X,A;R)`. -/
def rdREquiv (n : ℕ) :
    (↥((relChainsR R X A).X n) →ₗ[R] R) ≃ₗ[R] (relKern R X A n) :=
  LinearEquiv.ofBijective _ ⟨rdRMap_injective R X A n, rdRMap_surjective R X A n⟩

/-- The underlying linear map of `rdREquiv` is `rdRMap`. -/
lemma rdREquiv_apply (n : ℕ) (f : ↥((relChainsR R X A).X n) →ₗ[R] R) :
    (rdREquiv R X A n f : relKern R X A n) = rdRMap R X A n f :=
  LinearEquiv.ofBijective_apply _ f

/-- The value of `rdREquiv`. -/
lemma rdREquiv_apply_coe (n : ℕ) (f : ↥((relChainsR R X A).X n) →ₗ[R] R) :
    rdRLM R X n (rdREquiv R X A n f).1 = f.comp (rdRProj R X A n).hom := by
  rw [show rdRLM R X n (rdREquiv R X A n f).1
      = rdRLM R X n (rdRMap R X A n f).1 from by rw [rdREquiv_apply]]
  exact rdRMap_apply_coe R X A n f

/-- The key property of the inverse of `rdREquiv`. -/
lemma rdREquiv_symm_comp (n : ℕ) (φ : relKern R X A n) :
    ((rdREquiv R X A n).symm φ).comp (rdRProj R X A n).hom = rdRLM R X n φ.1 := by
  ext x
  have h : rdRMap R X A n ((rdREquiv R X A n).symm φ) = φ := by
    rw [← rdREquiv_apply, LinearEquiv.apply_symm_apply]
  have h2 := congrArg (fun (k : relKern R X A n) => rdRLM R X n k.1 x) h
  simpa only [rdRMap_apply R X A, LinearMap.comp_apply] using h2

/-! ## The isomorphism of cochain complexes -/

/-- The differential of the dual complex of `relChainsR R X A`. -/
lemma rdR_dualComplex_d (n : ℕ) :
    (dualComplex R (relChainsR R X A)).d n (n + 1)
      = dualDiff R (relChainsR R X A) n :=
  CochainComplex.of_d (dualObj R (relChainsR R X A)) (dualDiff R (relChainsR R X A)) n

/-- Evaluation of the differential of the dual complex. -/
lemma rdR_dualDiff_apply (n : ℕ) (ψ : ↥((relChainsR R X A).X n) →ₗ[R] R) :
    (show ↥((relChainsR R X A).X (n + 1)) →ₗ[R] R
        from ((dualComplex R (relChainsR R X A)).d n (n + 1)).hom
          (show ↥((dualComplex R (relChainsR R X A)).X n) from ψ))
      = ψ.comp ((relChainsR R X A).d (n + 1) n).hom := by
  rw [rdR_dualComplex_d]
  rfl

/-- The composite of `rdRMap` with the inclusion of the relative cochains is the corresponding
component of `dualComplexMap`. -/
lemma rdRMap_comp_relIncl (n : ℕ) :
    ModuleCat.ofHom (rdRMap R X A n) ≫ (relIncl R X A).f n
      = dualComplexMapComp R (Work.Cohomology.singularChains R X) (relChainsR R X A)
          (cokernel.π (relChainsRIncl R X A)) n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  show rdRLM R X n ((rdRMap R X A n) f).1 = f.comp (rdRProj R X A n).hom
  exact rdRMap_apply_coe R X A n f

/-- The degreewise isomorphism `Hom_R(C_n(X,A;R), R) ≅ C^n(X,A;R)`. -/
def rdRIso (n : ℕ) :
    (dualComplex R (relChainsR R X A)).X n ≅ (relComplex R X A).X n :=
  LinearEquiv.toModuleIso (rdREquiv R X A n)

/-- The forward map of `rdRIso` is `rdRMap`. -/
@[simp]
lemma rdRIso_hom (n : ℕ) :
    (rdRIso R X A n).hom = ModuleCat.ofHom (rdRMap R X A n) := rfl

/-- **The degreewise isomorphisms commute with the differentials.** -/
lemma rdRIso_comm (n : ℕ) :
    (rdRIso R X A n).hom ≫ (relComplex R X A).d n (n + 1)
      = (dualComplex R (relChainsR R X A)).d n (n + 1) ≫ (rdRIso R X A (n + 1)).hom := by
  rw [rdRIso_hom, rdRIso_hom]
  haveI : Mono ((relIncl R X A).f (n + 1)) := by
    rw [ModuleCat.mono_iff_injective]
    intro a b h
    exact Subtype.ext h
  rw [← cancel_mono ((relIncl R X A).f (n + 1))]
  rw [Category.assoc, Category.assoc]
  rw [← (relIncl R X A).comm n (n + 1)]
  rw [← Category.assoc, rdRMap_comp_relIncl R X A n, rdRMap_comp_relIncl R X A (n + 1)]
  exact (dualComplexMap R (Work.Cohomology.singularChains R X) (relChainsR R X A)
    (cokernel.π (relChainsRIncl R X A))).comm n (n + 1)

/-- **The relative cochains are the duals of the relative chains**, over any coefficient ring. -/
theorem relCochainDualR (X : TopCat) (A : Set X) :
    Nonempty (relComplex R X A ≅ dualComplex R (relChainsR R X A)) :=
  ⟨(HomologicalComplex.Hom.isoOfComponents (fun n => rdRIso R X A n)
    (fun i j hij => by
      rw [← hij]
      exact rdRIso_comm R X A i)).symm⟩

end

/-- The requested interface, under the name used by the ℚ-coefficient plan: relative cohomology is
the dual of the relative chains. -/
theorem relComplexIsoDualR (R : Type) [CommRing R] (X : TopCat) (A : Set X) :
    Nonempty (Work.Cohomology.relComplex R X A ≅
      Work.Cohomology.dualComplex R (relChainsR R X A)) :=
  relCochainDualR R X A

end Work.StemsB
