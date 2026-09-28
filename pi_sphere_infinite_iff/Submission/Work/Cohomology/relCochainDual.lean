import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.DualComplexMap

/-!
# The relative cochains are the duals of the relative chains

For a topological space `X` and a subset `A ⊆ X`, the relative singular cochains `C^*(X,A)` are
defined (`Submission/Work/Cohomology/relCochain_shortExact.lean`) as the **kernel** of the
restriction `C^*(X) ⟶ C^*(A)`, while the relative singular chains `C_*(X,A)` are the **cokernel**
of the inclusion `C_*(A) ⟶ C_*(X)`.  Since `Hom_ℤ(-, ℤ)` carries cokernels of `ℤ`-modules to
kernels, the two complexes agree:

`C^*(X,A) ≅ Hom_ℤ(C_*(X,A), ℤ) = dualComplex ℤ (relChains X A)`.

The isomorphism is proved degreewise.  With `p_n : C_n(X) ⟶ C_n(X,A)` the quotient map, a
functional `g` on `C_n(X,A)` pulls back to the cochain `g ∘ p_n`, which vanishes on the image of
`C_n(A)`; conversely every cochain vanishing on `C_n(A)` factors uniquely through `p_n` because
`ker p_n = range (C_n(A) ⟶ C_n(X))` (proved by exactness of the short complex of the pair).  The
factorisation is an instance of the left exactness of `Hom` (`LinearMap.exact_lcomp_of_exact_of_surjective`).
Since `p_•` is a chain map, the identification is compatible with the differentials.

## Main result

* `Work.Cohomology.relCochainDual` — `C^*(X,A) ≅ dualComplex ℤ (relChains X A)`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

variable (X : TopCat) (A : Set X)

/-! ## The quotient map `C_*(X) ⟶ C_*(X,A)` -/

/-- The `n`-th component of the quotient map `C_*(X) ⟶ C_*(X,A)` (the projection to the cokernel
of the inclusion of the chains of `A`). -/
abbrev relDualProj (n : ℕ) : (singularChains ℤ X).X n ⟶ (relChains X A).X n :=
  (cokernel.π (inclChains X A)).f n

/-- `relChains X A` is the cokernel of the inclusion of the chains of `A`. -/
lemma relDualChains_X (n : ℕ) :
    (relChains X A).X n = (cokernel (inclChains X A)).X n := rfl

/-- The quotient map is surjective in every degree. -/
lemma relDualProj_surjective (n : ℕ) : Function.Surjective (relDualProj X A n).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- The composite `C_*(A) ⟶ C_*(X) ⟶ C_*(X,A)` vanishes. -/
lemma relDualProj_incl_apply (n : ℕ) (y : ↥((singularChains ℤ (TopCat.of A)).X n)) :
    (relDualProj X A n) ((inclChains X A).f n y) = 0 := by
  have h3 : (0 : singularChains ℤ (TopCat.of A) ⟶ cokernel (inclChains X A)).f n
      = (inclChains X A).f n ≫ relDualProj X A n := by
    rw [relDualProj, ← HomologicalComplex.comp_f, cokernel.condition]
  have h4 := congrArg (fun (k : (singularChains ℤ (TopCat.of A)).X n ⟶
      (cokernel (inclChains X A)).X n) => k y) h3
  exact h4.symm

/-- **The kernel of the quotient map is the image of the chains of `A`.**  This is the exactness of
the short complex of the pair in degree `n`, read off from `ShortComplex.exact_of_g_is_cokernel`. -/
lemma relDualProj_ker (n : ℕ) :
    LinearMap.ker (relDualProj X A n).hom = LinearMap.range ((inclChains X A).f n).hom := by
  let S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    ShortComplex.mk (inclChains X A) (cokernel.π (inclChains X A)) (cokernel.condition _)
  have hex : S.Exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
  have hd : (S.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).Exact :=
    (HomologicalComplex.exact_iff_degreewise_exact S).1 hex n
  have h := (ShortComplex.moduleCat_exact_iff
    (S.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n))).1 hd
  have hg : (S.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).g
      = (cokernel.π (inclChains X A)).f n := by
    rw [ShortComplex.map_g]; rfl
  have hf : (S.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)).f
      = (inclChains X A).f n := by
    rw [ShortComplex.map_f]; rfl
  rw [hg, hf] at h
  refine le_antisymm ?_ ?_
  · rintro z hz
    exact h z hz
  · rintro z ⟨y, rfl⟩
    show (relDualProj X A n) ((inclChains X A).f n y) = 0
    exact relDualProj_incl_apply X A n y

/-- Exactness of the pair in degree `n`, in the form of `Function.Exact`. -/
lemma relDualProj_exact (n : ℕ) :
    Function.Exact (⇑((inclChains X A).f n).hom) (⇑(relDualProj X A n).hom) := by
  intro y
  rw [Set.mem_range]
  constructor
  · intro hy
    have hy' : y ∈ LinearMap.ker (relDualProj X A n).hom := hy
    rw [relDualProj_ker] at hy'
    exact hy'
  · rintro ⟨x, rfl⟩
    exact relDualProj_incl_apply X A n x

/-- Naturality of the quotient map with respect to the differentials. -/
lemma relDualProj_comm (n : ℕ) :
    relDualProj X A (n + 1) ≫ (relChains X A).d (n + 1) n
      = (singularChains ℤ X).d (n + 1) n ≫ relDualProj X A n :=
  (cokernel.π (inclChains X A)).comm (n + 1) n

/-- Naturality of the quotient map, as linear maps. -/
lemma relDualProj_comm_lm (n : ℕ) :
    ((relChains X A).d (n + 1) n).hom.comp (relDualProj X A (n + 1)).hom
      = (relDualProj X A n).hom.comp ((singularChains ℤ X).d (n + 1) n).hom := by
  have h := congrArg ModuleCat.Hom.hom (relDualProj_comm X A n)
  rwa [ModuleCat.hom_comp, ModuleCat.hom_comp] at h

/-! ## The relative cochains as functionals on chains -/

/-- An element of the cochain module of `X`, viewed as a functional on chains. -/
def relDualLM (n : ℕ) (φ : ↥((singularCochainComplex ℤ X).X n)) : ↥((singularChains ℤ X).X n) →ₗ[ℤ] ℤ :=
  show ↥((singularChains ℤ X).X n) →ₗ[ℤ] ℤ from φ

/-- **Membership criterion for the relative cochains**: a cochain lies in `C^n(X,A)` iff it
vanishes on all chains coming from `A`. -/
lemma relDualKern_iff (n : ℕ) (φ : ↥((singularCochainComplex ℤ X).X n)) :
    φ ∈ relKern ℤ X A n ↔ ∀ y : ↥((singularChains ℤ (TopCat.of A)).X n),
      relDualLM X n φ ((inclChains X A).f n y) = 0 := by
  have key : ∀ y : ↥((singularChains ℤ (TopCat.of A)).X n),
      (show ↥((singularChains ℤ (TopCat.of A)).X n) →ₗ[ℤ] ℤ
        from ((restr ℤ X A).f n).hom φ) y = relDualLM X n φ ((inclChains X A).f n y) :=
    fun y => LinearMap.dualMap_apply _ _ y
  constructor
  · intro h y
    have h1 : (show ↥((singularChains ℤ (TopCat.of A)).X n) →ₗ[ℤ] ℤ
        from ((restr ℤ X A).f n).hom φ) = 0 := h
    rw [← key y, h1]
    rfl
  · intro h
    have h1 : (show ↥((singularChains ℤ (TopCat.of A)).X n) →ₗ[ℤ] ℤ
        from ((restr ℤ X A).f n).hom φ) = 0 := by
      ext y
      rw [key y]
      simpa using h y
    exact h1

/-- The membership criterion in the form in which it will be used. -/
lemma relDualKern_iff' (n : ℕ) (φ : ↥((singularChains ℤ X).X n) →ₗ[ℤ] ℤ) :
    (φ : ↥((singularCochainComplex ℤ X).X n)) ∈ relKern ℤ X A n ↔
      ∀ y : ↥((singularChains ℤ (TopCat.of A)).X n), φ ((inclChains X A).f n y) = 0 :=
  relDualKern_iff X A n φ

/-- The value of the differential of the relative cochains on a chain. -/
lemma relDualDiff_apply (n : ℕ) (φ : relKern ℤ X A n)
    (x : ↥((singularChains ℤ X).X (n + 1))) :
    relDualLM X (n + 1) (relDiff ℤ X A n φ).1 x
      = relDualLM X n φ.1 ((singularChains ℤ X).d (n + 1) n x) := by
  rw [show (relDiff ℤ X A n φ).1 = (relDiffLM ℤ X A n φ).1 from rfl, relDiffLM_coe]
  rw [show ((singularCochainComplex ℤ X).d n (n + 1)) = dualDifferential ℤ X n from
    CochainComplex.of_d (dualChains ℤ X) (dualDifferential ℤ X) n]
  rfl

/-- The differential of the relative cochains, as a linear map. -/
lemma relDualDiff_apply_coe (n : ℕ) (ψ : relKern ℤ X A n) :
    relDualLM X (n + 1) (relDiff ℤ X A n ψ).1
      = (relDualLM X n ψ.1).comp ((singularChains ℤ X).d (n + 1) n).hom := by
  ext x
  rw [relDualDiff_apply, LinearMap.comp_apply]

/-! ## `Hom_ℤ(C_*(X,A), ℤ)` as the relative cochains -/

/-- **The dual of the quotient map**: a functional on the relative `n`-chains pulls back along
`p_n` to a relative `n`-cochain. -/
def relDualMap (n : ℕ) :
    (↥((relChains X A).X n) →ₗ[ℤ] ℤ) →ₗ[ℤ] (relKern ℤ X A n) :=
  ((relDualProj X A n).hom.dualMap).codRestrict (relKern ℤ X A n) (fun f => by
    rw [relDualKern_iff]
    intro y
    show f ((relDualProj X A n) ((inclChains X A).f n y)) = 0
    rw [relDualProj_incl_apply X A n y]
    simp)

/-- The value of `relDualMap`. -/
lemma relDualMap_apply (n : ℕ) (f : ↥((relChains X A).X n) →ₗ[ℤ] ℤ)
    (x : ↥((singularChains ℤ X).X n)) :
    relDualLM X n (relDualMap X A n f).1 x = f ((relDualProj X A n) x) := by
  simp only [relDualMap, LinearMap.codRestrict_apply, relDualLM]
  exact LinearMap.dualMap_apply _ _ x

/-- `relDualMap` is composition with `p_n`. -/
lemma relDualMap_apply_coe (n : ℕ) (f : ↥((relChains X A).X n) →ₗ[ℤ] ℤ) :
    relDualLM X n (relDualMap X A n f).1 = f.comp (relDualProj X A n).hom := by
  ext x
  rw [relDualMap_apply, LinearMap.comp_apply]

/-- `relDualMap` is injective, since `p_n` is surjective. -/
lemma relDualMap_injective (n : ℕ) : Function.Injective (relDualMap X A n) := by
  have hinj := LinearMap.lcomp_injective_of_surjective (S := ℤ) (N := ℤ)
    (relDualProj X A n).hom (relDualProj_surjective X A n)
  intro f g h
  have h2 : (relDualMap X A n f).1 = (relDualMap X A n g).1 := congrArg Subtype.val h
  have h3 : relDualLM X n (relDualMap X A n f).1 = relDualLM X n (relDualMap X A n g).1 := h2
  rw [relDualMap_apply_coe, relDualMap_apply_coe] at h3
  refine hinj ?_
  rw [LinearMap.lcomp_apply' (S := ℤ) (N := ℤ), LinearMap.lcomp_apply' (S := ℤ) (N := ℤ)]
  exact h3

/-- `relDualMap` is surjective: a cochain vanishing on the chains of `A` factors through `p_n`.
This is the left exactness of `Hom_ℤ(-, ℤ)`. -/
lemma relDualMap_surjective (n : ℕ) : Function.Surjective (relDualMap X A n) := by
  intro φ
  have hex := LinearMap.exact_lcomp_of_exact_of_surjective (N := ℤ) (relDualProj_exact X A n)
    (relDualProj_surjective X A n)
  have hφ : (LinearMap.lcomp (S := ℤ) (N := ℤ) ((inclChains X A).f n).hom)
      (relDualLM X n φ.1) = 0 := by
    ext x
    rw [LinearMap.lcomp_apply, LinearMap.zero_apply]
    exact (relDualKern_iff X A n φ.1).1 φ.2 x
  obtain ⟨h, hh⟩ := (hex (relDualLM X n φ.1)).1 hφ
  have hh' : h.comp (relDualProj X A n).hom = relDualLM X n φ.1 := by
    rw [← LinearMap.lcomp_apply' (S := ℤ) (N := ℤ)]; exact hh
  refine ⟨h, ?_⟩
  apply Subtype.ext
  show relDualLM X n (relDualMap X A n h).1 = relDualLM X n φ.1
  rw [relDualMap_apply_coe]
  exact hh'

/-- **The degreewise isomorphism** `Hom_ℤ(C_n(X,A), ℤ) ≃ C^n(X,A)`. -/
def relDualEquiv (n : ℕ) :
    (↥((relChains X A).X n) →ₗ[ℤ] ℤ) ≃ₗ[ℤ] (relKern ℤ X A n) :=
  LinearEquiv.ofBijective _ ⟨relDualMap_injective X A n, relDualMap_surjective X A n⟩

/-- The underlying linear map of `relDualEquiv` is `relDualMap`. -/
lemma relDualEquiv_apply (n : ℕ) (f : ↥((relChains X A).X n) →ₗ[ℤ] ℤ) :
    (relDualEquiv X A n f : relKern ℤ X A n) = relDualMap X A n f :=
  LinearEquiv.ofBijective_apply _ f

/-- The value of `relDualEquiv`. -/
lemma relDualEquiv_apply_coe (n : ℕ) (f : ↥((relChains X A).X n) →ₗ[ℤ] ℤ) :
    relDualLM X n (relDualEquiv X A n f).1 = f.comp (relDualProj X A n).hom := by
  rw [show relDualLM X n (relDualEquiv X A n f).1
      = relDualLM X n (relDualMap X A n f).1 from by rw [relDualEquiv_apply]]
  exact relDualMap_apply_coe X A n f

/-- **The key property of the inverse of `relDualEquiv`**: the cochain corresponding to a relative
cochain `φ` restricts along `p_n` back to `φ`. -/
lemma relDualEquiv_symm_comp (n : ℕ) (φ : relKern ℤ X A n) :
    ((relDualEquiv X A n).symm φ).comp (relDualProj X A n).hom = relDualLM X n φ.1 := by
  ext x
  have h : relDualMap X A n ((relDualEquiv X A n).symm φ) = φ := by
    rw [← relDualEquiv_apply, LinearEquiv.apply_symm_apply]
  have h2 := congrArg (fun (k : relKern ℤ X A n) => relDualLM X n k.1 x) h
  simpa only [relDualMap_apply X A, LinearMap.comp_apply] using h2

/-! ## The isomorphism of cochain complexes -/

/-- The differential of the dual complex of `relChains X A`. -/
lemma relDual_dualComplex_d (n : ℕ) :
    (dualComplex ℤ (relChains X A)).d n (n + 1) = dualDiff ℤ (relChains X A) n :=
  CochainComplex.of_d (dualObj ℤ (relChains X A)) (dualDiff ℤ (relChains X A)) n

/-- Evaluation of the differential of the dual complex. -/
lemma relDual_dualDiff_apply (n : ℕ) (ψ : ↥((relChains X A).X n) →ₗ[ℤ] ℤ) :
    (show ↥((relChains X A).X (n + 1)) →ₗ[ℤ] ℤ
        from ((dualComplex ℤ (relChains X A)).d n (n + 1)).hom
          (show ↥((dualComplex ℤ (relChains X A)).X n) from ψ))
      = ψ.comp ((relChains X A).d (n + 1) n).hom := by
  rw [relDual_dualComplex_d]
  rfl

/-- The composite of `relDualMap` with the inclusion of the relative cochains into the cochains
of `X` is the corresponding component of `dualComplexMap`. -/
lemma relDualMap_comp_relIncl (n : ℕ) :
    ModuleCat.ofHom (relDualMap X A n) ≫ (relIncl ℤ X A).f n
      = dualComplexMapComp ℤ (singularChains ℤ X) (relChains X A)
          (cokernel.π (inclChains X A)) n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  show relDualLM X n ((relDualMap X A n) f).1 = f.comp (relDualProj X A n).hom
  exact relDualMap_apply_coe X A n f

/-- The degreewise isomorphism `Hom_ℤ(C_n(X,A), ℤ) ≅ C^n(X,A)`. -/
def relDualIso (n : ℕ) :
    (dualComplex ℤ (relChains X A)).X n ≅ (relComplex ℤ X A).X n :=
  LinearEquiv.toModuleIso (relDualEquiv X A n)

/-- The forward map of `relDualIso` is `relDualMap`. -/
@[simp]
lemma relDualIso_hom (n : ℕ) :
    (relDualIso X A n).hom = ModuleCat.ofHom (relDualMap X A n) := rfl

/-- **The degreewise isomorphisms commute with the differentials.**

Both composites are equal after composition with the mono `C^{n+1}(X,A) ⟶ C^{n+1}(X)`: this reduces
to the functoriality of `dualComplexMap`, applied to the chain map `cokernel.π (inclChains X A)`. -/
lemma relDualIso_comm (n : ℕ) :
    (relDualIso X A n).hom ≫ (relComplex ℤ X A).d n (n + 1)
      = (dualComplex ℤ (relChains X A)).d n (n + 1) ≫ (relDualIso X A (n + 1)).hom := by
  rw [relDualIso_hom, relDualIso_hom]
  haveI : Mono ((relIncl ℤ X A).f (n + 1)) := by
    rw [ModuleCat.mono_iff_injective]
    intro a b h
    exact Subtype.ext h
  rw [← cancel_mono ((relIncl ℤ X A).f (n + 1))]
  rw [Category.assoc, Category.assoc]
  rw [← (relIncl ℤ X A).comm n (n + 1)]
  rw [← Category.assoc, relDualMap_comp_relIncl X A n, relDualMap_comp_relIncl X A (n + 1)]
  exact (dualComplexMap ℤ (singularChains ℤ X) (relChains X A)
    (cokernel.π (inclChains X A))).comm n (n + 1)

/-- **The relative cochains are the duals of the relative chains.** -/
theorem relCochainDual (X : TopCat) (A : Set X) :
    Nonempty (relComplex ℤ X A ≅ dualComplex ℤ (relChains X A)) :=
  ⟨(HomologicalComplex.Hom.isoOfComponents (fun n => relDualIso X A n)
    (fun i j hij => by
      rw [← hij]
      exact relDualIso_comm X A i)).symm⟩

end

end Work.Cohomology
