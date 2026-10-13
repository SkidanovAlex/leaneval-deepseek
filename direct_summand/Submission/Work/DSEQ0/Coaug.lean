import Mathlib
import ChallengeDeps
import Submission.Work.DSMap.Map
import Submission.Work.DSEQ0.CechModel
import Submission.Work.DSEQ0.chainMap_retraction_of_differential

/-!
# DSEQ0: the coaugmentation functional

This module isolates the *sharpest* form of the remaining input of area `EQ0`.

## The reduction

Given the Čech model data produced by the frozen area `DSMap.area_F1_cech` (a chain map
`cc : A[0] ⟶ Ĉ(U;𝒪)` whose degree-`0` component is the Čech coaugmentation, and an isomorphism
`e : ι(RΓ(X,𝒪)) ≅ Q(Ĉ(U;𝒪))` carrying the challenge unit `rgUnit` to `Q(cc)`), the challenge
unit is a split monomorphism **as soon as** there is an `A`-linear functional
`φ₀ : Ĉ(U;𝒪)⁰ ⟶ A` with `φ₀ (cc.f 0 1) = 1`.

Indeed, `A[0]` is concentrated in degree `0`, so *every* linear map `φ₀` on the degree-`0` term
of `Ĉ(U;𝒪)` is a chain map `φ : Ĉ(U;𝒪) ⟶ A[0]` (the only chain condition is at `-1 ⟶ 0`, and
`Ĉ(U;𝒪)` vanishes in negative degrees, so `d⁻¹ = 0`), and the identity `φ₀ (cc.f 0 1) = 1`
says exactly `cc ≫ φ = 𝟙`.  The chain-model criterion `Work.DSEQ0.isSplitMono_of_cechModel`
then applies.

## Why this is the sharpest possible form

Conversely, if the challenge unit is a split monomorphism then applying `H⁰` to a retraction
produces a functional on `H⁰(Ĉ(U;𝒪))` with value `1` on the coaugmentation class.  The
difference between the two statements is only the passage from `H⁰ = Z⁰/B⁰` to `Ĉ⁰`, i.e. an
extension problem along `H⁰(Ĉ) ↪ Ĉ⁰/B⁰`; equivalently one may take a *finite free model* of the
Čech complex and ask for a functional on its degree-`0` term killing the boundaries
(`DSMap.Mix.ModSplit P ε (RingHom.id A) ⊥ 1`, the interface used by the bridge
`DSMap.Mix2.area_MX0bU`).

This is the point at which the trace of the equal-characteristic-zero argument enters: the
functional is the trace of the finite `A`-algebra `H⁰(X,𝒪_X) = Γ(X,𝒪_X)` (which is a finitely
generated `A`-module by the frozen area `DSMap.area_COH`), and the trace argument requires that
`A` be integrally closed in its fraction field.  See `DESIGN.md`.

## Contents

* `Work.DSEQ0.isZero_cechZ_X_of_neg`, `Work.DSEQ0.cechZ_d_negOne_zero`: the Čech complex
  vanishes (and hence has zero differential) in negative degrees.
* `Work.DSEQ0.isSplitMono_of_coaugFunctional`: the reduction for a fixed cover.
* `Work.DSEQ0.area_EQ0_of_coaugFunctional`: the reduction of the frozen area statement
  `DSMap.area_EQ0` to the existence of the functional, uniformly over the derived-category
  instances.
-/

open CategoryTheory AlgebraicGeometry Limits

namespace Work.DSEQ0

universe u w₁ w₂

variable (A : Type u) [CommRing A]

/-- The Čech complex of a family of opens vanishes in negative degrees. -/
lemma isZero_cechZ_X_of_neg (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u}
    (U : ι → X.Opens) {i : ℤ} (hi : i < 0) : IsZero ((DSMap.cechZ A X f U).X i) := by
  refine HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat i (fun n hn => ?_)
  rw [ComplexShape.embeddingUpNat_f] at hn
  omega

/-- The differential `d^{-1} : Ĉ⁻¹ ⟶ Ĉ⁰` of the Čech complex is zero. -/
lemma cechZ_d_negOne_zero (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u}
    (U : ι → X.Opens) : (DSMap.cechZ A X f U).d (-1) 0 = 0 :=
  Limits.IsZero.eq_of_src (isZero_cechZ_X_of_neg A X f U (by norm_num)) _ _

variable {A}

/-- **The coaugmentation functional.**  A functional on the degree-`0` term of the Čech complex
taking the value `1` on the coaugmentation class `cc.f 0 1`. -/
def CoaugFunctional (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} (U : ι → X.Opens)
    (cc : singleZ A ⟶ DSMap.cechZ A X f U) : Prop :=
  ∃ φ₀ : (DSMap.cechZ A X f U).X 0 ⟶ ModuleCat.of A A, φ₀ (cc.f 0 (1 : A)) = (1 : A)

/-- **The reduction, for a fixed cover.**  Given the Čech model data of the frozen area `F1`
and a functional on the degree-`0` term of the Čech complex with value `1` on the coaugmentation
class, the challenge unit is a split monomorphism. -/
theorem isSplitMono_of_coaugFunctional [HasDerivedCategory.{w₁} (ModuleCat.{u} A)]
    [IsLocalRing A] [CharZero (IsLocalRing.ResidueField A)]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [HasDerivedCategory.{w₂} (SheafOfModules X.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X.ringCatSheaf)]
    {ι : Type u} (U : ι → X.Opens)
    (cc : singleZ A ⟶ DSMap.cechZ A X f U)
    (e : DerivedCategory.Plus.ι.obj (DSMap.RG A X f) ≅
      DerivedCategory.Q.obj (DSMap.cechZ A X f U))
    (he : DerivedCategory.Plus.ι.map (DSMap.rgUnit A X f) ≫ e.hom =
      (singleIsoCompQ A).hom ≫ DerivedCategory.Q.map cc)
    (h : CoaugFunctional X f U cc) :
    IsSplitMono (DSMap.rgUnit A X f) := by
  obtain ⟨φ₀, hφ₀⟩ := h
  obtain ⟨φ, hφ⟩ := chainMap_retraction_of_differential (DSMap.cechZ A X f U) cc φ₀ 1
    (by norm_num) (by simpa using hφ₀) (by rw [cechZ_d_negOne_zero A X f U, Limits.zero_comp])
  refine isSplitMono_of_cechModel A X f U cc e he (DSMap.cechZ A X f U) (𝟙 _)
    (by infer_instance) cc ?_ φ hφ
  rw [DerivedCategory.Q.map_id, Category.comp_id]

/-- **Area `EQ0`, reduced to the coaugmentation functional.**  For a regular local ring `A`,
complete with algebraically closed residue field of characteristic zero, and `X` integral,
proper, surjective, generically finite and projective over `Spec A`, the challenge unit splits
as soon as, for every choice of the derived-category instances, there is a finite affine cover
of `X` whose Čech coaugmentation carries a functional with value `1`.

This is the reduction of the frozen statement `DSMap.area_EQ0` to the trace of the finite
`A`-algebra `H⁰(X,𝒪_X)`. -/
theorem area_EQ0_of_coaugFunctional.{a, b, c} (A : Type a) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [IsAlgClosed (IsLocalRing.ResidueField A)]
    [CharZero (IsLocalRing.ResidueField A)] (X : Scheme.{a}) [IsIntegral X]
    (f : X ⟶ Spec (.of A)) [IsProper f] (hs : Function.Surjective f)
    (hg : DSMap.IsGenFinite A f) (hp : DSMap.IsProjOver A f)
    (h : ∀ (_ : HasDerivedCategory.{b} (ModuleCat.{a} A))
      (_ : HasDerivedCategory.{c} (SheafOfModules X.ringCatSheaf))
      (_ : EnoughInjectives (SheafOfModules X.ringCatSheaf)),
      ∃ (J : Type a) (_ : Finite J) (U : J → X.Opens) (_ : ∀ i, IsAffineOpen (U i))
        (_ : ⨆ i, U i = ⊤) (cc : singleZ A ⟶ DSMap.cechZ A X f U)
        (e : DerivedCategory.Plus.ι.obj (DSMap.RG A X f) ≅
          DerivedCategory.Q.obj (DSMap.cechZ A X f U)),
        (DerivedCategory.Plus.ι.map (DSMap.rgUnit A X f) ≫ e.hom =
          (singleIsoCompQ A).hom ≫ DerivedCategory.Q.map cc) ∧
          CoaugFunctional X f U cc) :
    DSMap.DSplit.{a, b, c} A X f := by
  intro h₁ h₂ h₃
  obtain ⟨J, hJ, U, hU, hcov, cc, e, he, hcf⟩ := h h₁ h₂ h₃
  exact isSplitMono_of_coaugFunctional X f U cc e he hcf

end Work.DSEQ0
