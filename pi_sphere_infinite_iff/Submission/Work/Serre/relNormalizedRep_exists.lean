import Mathlib
import Submission.Work.Cohomology.RelCup
import Submission.Work.Cohomology.DualComplexMap
import Submission.Work.Cohomology.homotopyEquivDual
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.relCupHNatural
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Serre.quasiIso_tau1

/-!
# Normalized representatives of relative cohomology classes

This file proves `Work.Serre.relNormalizedRep_exists`: every class in the relative cohomology
`Hⁿ(X,A;ℚ)` is represented by a relative cocycle which annihilates the generators of all
degenerate `n`-simplices (a "normalized" representative).

The proof follows the author's plan.  Let `PInfty` be the Dold–Kan projection on the simplicial
chain complex (`DoldKan.PInfty`), which is homotopic to the identity and kills the generators of
degenerate simplices, and let `normCochainMap X` be its transpose on the singular cochain complex
`C^*(X;ℚ)`.  Then

* `normCochainMap X` is homotopic to the identity (`dualHomotopy` applied to
  `SSet.homotopyEquivNormalizedChainComplex`), hence a quasi-isomorphism;
* `normCochainMap` is natural with respect to the inclusion `A ↪ X`
  (`SSet.chainComplexMap_PInfty`), hence induces a cochain map `relNorm X A` of the relative
  complex, and a morphism of the short exact sequence of the pair;
* by the five lemma for the first term (`Work.Serre.quasiIso_tau1`) `relNorm X A` is a
  quasi-isomorphism, so `homologyMap (relNorm X A) n` is surjective.  Lifting a class `β` along it
  gives a cycle whose underlying cochain still annihilates degenerate simplices, because
  `PInfty` does.
-/

set_option maxHeartbeats 800000

open CategoryTheory HomologicalComplex AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Serre

noncomputable section

/-! ## The Dold–Kan projection and its transpose -/

/-- `PInfty` as an endomorphism of the simplicial chain complex of `X` with coefficients in `ℚ`. -/
abbrev pInfty (X : SSet) :
    X.chainComplex (ModuleCat.of ℚ ℚ) ⟶ X.chainComplex (ModuleCat.of ℚ ℚ) :=
  DoldKan.PInfty

/-- The `n`-th component of `PInfty` as a linear endomorphism. -/
abbrev pInftyLM (X : SSet) (n : ℕ) :
    ((X.chainComplex (ModuleCat.of ℚ ℚ)).X n) →ₗ[ℚ] ((X.chainComplex (ModuleCat.of ℚ ℚ)).X n) :=
  ((pInfty X).f n).hom

/-- `PInfty` in component form: it is the composite of the projection to the normalized chain
complex with the inclusion of the latter. -/
theorem pInfty_f_eq (X : SSet) (n : ℕ) :
    (pInfty X).f n = (SSet.toNormalizedChainComplex X (ModuleCat.of ℚ ℚ)).f n ≫
      (SSet.fromNormalizedChainComplex X (ModuleCat.of ℚ ℚ)).f n :=
  (SSet.toNormalizedChainComplex_f_fromNormalizedChainComplex_f X (ModuleCat.of ℚ ℚ) n).symm

/-- **`PInfty` kills the generator of a degenerate simplex.** -/
theorem pInftyLM_generator_degenerate (X : SSet) (n : ℕ) (x : X _⦋n⦌)
    (hx : x ∈ X.degenerate n) :
    pInftyLM X n ((ModuleCat.Hom.hom (X.ιChainComplex (R := ModuleCat.of ℚ ℚ) x)) 1) = 0 := by
  show ((pInfty X).f n).hom _ = 0
  rw [pInfty_f_eq, ModuleCat.hom_comp]
  have h2 : (ModuleCat.Hom.hom ((SSet.toNormalizedChainComplex X (ModuleCat.of ℚ ℚ)).f n))
      ((ModuleCat.Hom.hom (X.ιChainComplex (R := ModuleCat.of ℚ ℚ) x)) 1) = 0 := by
    have h := congrArg (fun (g : ModuleCat.of ℚ ℚ ⟶
        (X.normalizedChainComplex (ModuleCat.of ℚ ℚ)).X n) => g.hom 1)
      (SSet.ιChainComplex_toNormalizedChainComplex_f X (R := ModuleCat.of ℚ ℚ) x)
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [h, SSet.ιNormalizedChainComplex_eq_zero X (R := ModuleCat.of ℚ ℚ) x hx]
    simp
  rw [LinearMap.comp_apply, h2, map_zero]

/-! ## The normalization map on the absolute cochain complex -/

/-- The cochain map `C^*(X;ℚ) → C^*(X;ℚ)` induced by `PInfty`. -/
def normCochainMap (X : TopCat) :
    Work.Cohomology.singularCochainComplex ℚ X ⟶ Work.Cohomology.singularCochainComplex ℚ X :=
  Work.Cohomology.dualComplexMap ℚ ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ))
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)) (pInfty (TopCat.toSSet.obj X))

/-- The `n`-th component of `normCochainMap`, as the linear transpose of `PInfty`. -/
abbrev normLM (X : TopCat) (n : ℕ) :
    (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).X n →ₗ[ℚ] ℚ) →ₗ[ℚ]
      (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).X n →ₗ[ℚ] ℚ) :=
  (pInftyLM (TopCat.toSSet.obj X) n).dualMap

theorem normLM_apply (X : TopCat) (n : ℕ)
    (γ : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).X n →ₗ[ℚ] ℚ)
    (y : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).X n) :
    normLM X n γ y = γ (pInftyLM (TopCat.toSSet.obj X) n y) :=
  LinearMap.dualMap_apply _ _ _

theorem normCochainMap_f_LM (X : TopCat) (n : ℕ) :
    (normCochainMap X).f n = ModuleCat.ofHom (normLM X n) := rfl

/-- The `n`-th component of `normCochainMap` evaluated on a cochain. -/
theorem normCochainMap_f_apply (X : TopCat) (n : ℕ)
    (γ : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).X n →ₗ[ℚ] ℚ) :
    ((normCochainMap X).f n).hom γ = normLM X n γ := rfl

/-- **The normalized cochains annihilate degenerate simplices.** -/
theorem normLM_genEval_degenerate (X : TopCat) (n : ℕ)
    (γ : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).X n →ₗ[ℚ] ℚ)
    (x : (TopCat.toSSet.obj X) _⦋n⦌) (hx : x ∈ (TopCat.toSSet.obj X).degenerate n) :
    Work.Cohomology.genEval ℚ (TopCat.toSSet.obj X) (normLM X n γ) x = 0 := by
  rw [show Work.Cohomology.genEval ℚ (TopCat.toSSet.obj X) (normLM X n γ) x
      = normLM X n γ ((ModuleCat.Hom.hom
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) x)) 1) from rfl]
  rw [normLM_apply, pInftyLM_generator_degenerate (TopCat.toSSet.obj X) n x hx, map_zero]

/-- **`normCochainMap` is homotopic to the identity**: it is the dual of `PInfty`, which is
homotopic to the identity by Dold–Kan. -/
def homotopy_normCochainMap (X : TopCat) :
    Homotopy (normCochainMap X) (𝟙 _) := by
  have h := Work.Cohomology.dualHomotopy ℚ
    ((TopCat.toSSet.obj X).homotopyEquivNormalizedChainComplex (ModuleCat.of ℚ ℚ)).homotopyHomInvId
  rw [SSet.homotopyEquivNormalizedChainComplex_hom,
    SSet.homotopyEquivNormalizedChainComplex_inv] at h
  rw [SSet.toNormalizedChainComplex_fromNormalizedChainComplex (TopCat.toSSet.obj X)
    (ModuleCat.of ℚ ℚ)] at h
  rw [Work.Cohomology.dualComplexMap_id] at h
  exact h.symm

/-- **`normCochainMap` is a quasi-isomorphism.** -/
theorem quasiIso_normCochainMap (X : TopCat) : QuasiIso (normCochainMap X) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  rw [Homotopy.homologyMap_eq (homotopy_normCochainMap X) i]
  infer_instance

/-! ## Naturality with respect to the inclusion `A ⊆ X` -/

/-- `restr` is the dual of the chain map induced by the inclusion `A ⊆ X`. -/
theorem restr_eq_dualComplexMap (X : TopCat) (A : Set X) :
    Work.Cohomology.restr ℚ X A
      = Work.Cohomology.dualComplexMap ℚ
          ((TopCat.toSSet.obj (TopCat.of A)).chainComplex (ModuleCat.of ℚ ℚ))
          ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ))
          (SSet.chainComplexMap (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A))
            (ModuleCat.of ℚ ℚ)) := by
  apply HomologicalComplex.hom_ext
  intro n
  rfl

/-- **Naturality of `normCochainMap`**: it commutes with the restriction along the inclusion
`A ⊆ X` (this is the naturality of `PInfty` in the simplicial set). -/
theorem normCochainMap_naturality (X : TopCat) (A : Set X) :
    normCochainMap X ≫ Work.Cohomology.restr ℚ X A
      = Work.Cohomology.restr ℚ X A ≫ normCochainMap (TopCat.of A) := by
  show Work.Cohomology.dualComplexMap ℚ
        ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ))
        ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)) (pInfty (TopCat.toSSet.obj X)) ≫ _
      = _ ≫ Work.Cohomology.dualComplexMap ℚ
        ((TopCat.toSSet.obj (TopCat.of A)).chainComplex (ModuleCat.of ℚ ℚ))
        ((TopCat.toSSet.obj (TopCat.of A)).chainComplex (ModuleCat.of ℚ ℚ))
        (pInfty (TopCat.toSSet.obj (TopCat.of A)))
  rw [restr_eq_dualComplexMap X A, ← Work.Cohomology.dualComplexMap_comp,
    ← Work.Cohomology.dualComplexMap_comp]
  congr 1
  exact SSet.chainComplexMap_PInfty (TopCat.toSSet.map (Work.Cohomology.subtypeIncl X A))
    (ModuleCat.of ℚ ℚ)

/-- `normCochainMap` preserves the relative cochains (the kernel of the restriction). -/
theorem normCochainMap_relKern_mem (X : TopCat) (A : Set X) (n : ℕ)
    (x : Work.Cohomology.relKern ℚ X A n) :
    ((normCochainMap X).f n).hom x.1 ∈ Work.Cohomology.relKern ℚ X A n := by
  have h := congrArg (fun (g : Work.Cohomology.singularCochainComplex ℚ X ⟶
      Work.Cohomology.singularCochainComplex ℚ (TopCat.of A)) => (g.f n).hom x.1)
    (normCochainMap_naturality X A)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  have hx : ((Work.Cohomology.restr ℚ X A).f n).hom x.1 = 0 := x.2
  rw [hx, map_zero] at h
  show ((Work.Cohomology.restr ℚ X A).f n).hom
    (((normCochainMap X).f n).hom x.1) = 0
  exact h

/-! ## The normalization map of the relative cochain complex -/

/-- The `n`-th component of the normalization map of the relative cochain complex: the restriction
of `normCochainMap` to the kernel of the restriction. -/
def relNormLM (X : TopCat) (A : Set X) (n : ℕ) :
    Work.Cohomology.relKern ℚ X A n →ₗ[ℚ] Work.Cohomology.relKern ℚ X A n :=
  LinearMap.codRestrict (Work.Cohomology.relKern ℚ X A n)
    (((normCochainMap X).f n).hom.comp
      (Submodule.subtype (Work.Cohomology.relKern ℚ X A n)))
    (fun x => normCochainMap_relKern_mem X A n x)

/-- The underlying cochain of `relNormLM`. -/
theorem relNormLM_coe (X : TopCat) (A : Set X) (n : ℕ) (x : Work.Cohomology.relKern ℚ X A n) :
    (relNormLM X A n x).1 = ((normCochainMap X).f n).hom x.1 := rfl

/-- **The normalization map of the relative cochain complex `C^*(X,A;ℚ)`.** -/
def relNorm (X : TopCat) (A : Set X) :
    Work.Cohomology.relComplex ℚ X A ⟶ Work.Cohomology.relComplex ℚ X A :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (relNormLM X A n)) (fun n => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [Work.Cohomology.relComplex_d]
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      ((normCochainMap X).comm n (n+1))) x.1)

/-- The `n`-th component of `relNorm`. -/
theorem relNorm_f (X : TopCat) (A : Set X) (n : ℕ) :
    (relNorm X A).f n = ModuleCat.ofHom (relNormLM X A n) := rfl

/-- The `n`-th component of `relNorm` evaluated on a relative cochain. -/
theorem relNorm_f_apply (X : TopCat) (A : Set X) (n : ℕ)
    (y : (Work.Cohomology.relComplex ℚ X A).X n) :
    ((relNorm X A).f n).hom y = relNormLM X A n y := rfl

/-- The normalization map of the relative complex is compatible with the inclusion into the
absolute complex. -/
theorem relNorm_relIncl (X : TopCat) (A : Set X) :
    relNorm X A ≫ Work.Cohomology.relIncl ℚ X A
      = Work.Cohomology.relIncl ℚ X A ≫ normCochainMap X := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, relNorm_f,
    Work.Cohomology.relIncl_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact relNormLM_coe X A n x

/-! ## Auxiliary computations on cycles -/

/-- The inclusion of the cycles is the inverse of the projection: the image of a cycle under
`iCycles ≫ f` is the image of its underlying element under `f`. -/
theorem cyclesMap_iCycles {K L : CochainComplex (ModuleCat ℚ) ℕ} (φ : K ⟶ L) (n : ℕ)
    (z : K.cycles n) :
    (L.iCycles n).hom ((HomologicalComplex.cyclesMap φ n).hom z)
      = (φ.f n).hom ((K.iCycles n).hom z) := by
  have h := congrArg (fun (g : K.cycles n ⟶ L.X n) => g.hom z)
    (HomologicalComplex.cyclesMap_i φ n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- The underlying cochain of the image of a cycle of the relative complex under `relNorm`. -/
theorem cyclesMap_relNorm_coe (X : TopCat) (A : Set X) (n : ℕ)
    (z : (Work.Cohomology.relComplex ℚ X A).cycles n) :
    (((Work.Cohomology.relComplex ℚ X A).iCycles n).hom
        ((HomologicalComplex.cyclesMap (relNorm X A) n).hom z)).1
      = normLM X n ((((Work.Cohomology.relComplex ℚ X A).iCycles n).hom z :
          ↥(Work.Cohomology.relKern ℚ X A n))).1 := by
  refine (congrArg (fun w : ↥(Work.Cohomology.relKern ℚ X A n) => w.1)
    (cyclesMap_iCycles (relNorm X A) n z)).trans ?_
  refine (congrArg (fun w : ↥(Work.Cohomology.relKern ℚ X A n) => w.1)
    (relNorm_f_apply X A n _)).trans ?_
  exact (relNormLM_coe X A n _).trans (normCochainMap_f_apply X n _)

/-! ## The main theorem -/

/-- **Existence of a normalized representative of a relative cohomology class.**

Every class `β ∈ Hⁿ(X,A;ℚ)` of the relative cohomology of a pair is the class of a relative
`n`-cocycle `φ` which annihilates the generators of all degenerate `n`-simplices. -/
theorem relNormalizedRep_exists (X : TopCat) (A : Set X) (n : ℕ)
    (β : ↥((Work.Cohomology.relComplex ℚ X A).homology n)) :
    ∃ (φ : Work.Cohomology.relKern ℚ X A n)
      (hφ : Work.Cohomology.relDiffLM ℚ X A n φ = 0),
      (∀ x ∈ (TopCat.toSSet.obj X).degenerate n,
        Work.Cohomology.genEval ℚ (TopCat.toSSet.obj X) φ.1 x = 0)
      ∧ Work.Cohomology.relClassOf ℚ X A φ hφ = β := by
  classical
  -- the short exact sequence of the pair and the morphism induced by `normCochainMap`
  let S : ShortComplex (CochainComplex (ModuleCat ℚ) ℕ) := Work.Cohomology.pairShort ℚ X A
  have hS : S.ShortExact := Work.Cohomology.pairShort_shortExact ℚ X A
  let τ₁ : Work.Cohomology.relComplex ℚ X A ⟶ Work.Cohomology.relComplex ℚ X A := relNorm X A
  let τ₂ : Work.Cohomology.singularCochainComplex ℚ X ⟶
      Work.Cohomology.singularCochainComplex ℚ X := normCochainMap X
  let τ₃ : Work.Cohomology.singularCochainComplex ℚ (TopCat.of A) ⟶
      Work.Cohomology.singularCochainComplex ℚ (TopCat.of A) := normCochainMap (TopCat.of A)
  have hcomm₁₂ : τ₁ ≫ S.f = S.f ≫ τ₂ := relNorm_relIncl X A
  have hcomm₂₃ : τ₂ ≫ S.g = S.g ≫ τ₃ := normCochainMap_naturality X A
  let φc : S ⟶ S :=
    { τ₁ := τ₁, τ₂ := τ₂, τ₃ := τ₃, comm₁₂ := hcomm₁₂, comm₂₃ := hcomm₂₃ }
  have hq : QuasiIso φc.τ₁ :=
    quasiIso_tau1 φc hS hS (quasiIso_normCochainMap X) (quasiIso_normCochainMap (TopCat.of A))
  -- `homologyMap τ₁ n` is an isomorphism, hence surjective
  have hIso : IsIso (HomologicalComplex.homologyMap τ₁ n) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    exact hq.quasiIsoAt n
  have hsurj : Function.Surjective ((HomologicalComplex.homologyMap τ₁ n).hom) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨x, hx⟩ := hsurj β
  -- lift the class `x` to a cycle
  have hπ : Function.Surjective (((Work.Cohomology.relComplex ℚ X A).homologyπ n).hom) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨z, hz⟩ := hπ x
  -- the class of `cyclesMap τ₁ n z` is `β`
  have hβ : ((Work.Cohomology.relComplex ℚ X A).homologyπ n).hom
      ((HomologicalComplex.cyclesMap τ₁ n).hom z) = β := by
    rw [← Work.Cohomology.homologyMap_homologyπ ℚ τ₁ n z, hz, hx]
  -- the candidate cochain
  set φ : Work.Cohomology.relKern ℚ X A n :=
    ((Work.Cohomology.relComplex ℚ X A).iCycles n).hom
      ((HomologicalComplex.cyclesMap τ₁ n).hom z) with hφdef
  have hφ : Work.Cohomology.relDiffLM ℚ X A n φ = 0 := by
    rw [hφdef, ← Work.Cohomology.relComplex_d_apply ℚ X A
      (((Work.Cohomology.relComplex ℚ X A).iCycles n).hom
        ((HomologicalComplex.cyclesMap τ₁ n).hom z))]
    exact Work.Cohomology.iCycles_d_apply_K (Work.Cohomology.relComplex ℚ X A) n
      ((HomologicalComplex.cyclesMap τ₁ n).hom z)
  -- the underlying cochain is a normalized one
  have hcoe : (φ : Work.Cohomology.relKern ℚ X A n).1
      = normLM X n ((((Work.Cohomology.relComplex ℚ X A).iCycles n).hom z :
          ↥(Work.Cohomology.relKern ℚ X A n))).1 := by
    rw [hφdef]
    exact cyclesMap_relNorm_coe X A n z
  -- hence it annihilates the generators of degenerate simplices
  have hdegen : ∀ x ∈ (TopCat.toSSet.obj X).degenerate n,
      Work.Cohomology.genEval ℚ (TopCat.toSSet.obj X) φ.1 x = 0 := by
    intro x hx'
    rw [hcoe]
    exact normLM_genEval_degenerate X n _ x hx'
  -- the class of `φ` is `β`
  have hcyc : Work.Cohomology.relCocycleOf ℚ X A φ hφ
      = (HomologicalComplex.cyclesMap τ₁ n).hom z := by
    refine Work.Cohomology.iCycles_injective_K (Work.Cohomology.relComplex ℚ X A) n ?_
    rw [Work.Cohomology.iCycles_relCocycleOf, hφdef]
  have hclass : Work.Cohomology.relClassOf ℚ X A φ hφ = β := by
    show ((Work.Cohomology.relComplex ℚ X A).homologyπ n).hom
      (Work.Cohomology.relCocycleOf ℚ X A φ hφ) = β
    rw [hcyc]
    exact hβ
  exact ⟨φ, hφ, hdegen, hclass⟩

end

end Work.Serre
