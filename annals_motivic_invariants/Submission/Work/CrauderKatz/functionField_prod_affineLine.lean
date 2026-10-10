import Mathlib
import Submission.Work.CrauderKatz.Defs
import Submission.Work.CrauderKatz.functionField_iso
import Submission.Work.CrauderKatz.ratFunc_equiv_fractionRing_polynomial
import Submission.Work.CrauderKatz.sections_preimage_fst_pullback_affineOpen
import Submission.Work.CrauderKatz.exists_section_pullback_affineLine

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.CrauderKatz

noncomputable section

open CategoryTheory AlgebraicGeometry

/-! ## The model of the `𝔸¹`-cylinder

We record the (abbreviation-level) names of the objects appearing in the main statement:
`affineLine 𝕜 = Spec 𝕜[t]`, its structure morphism `affineLineStruct 𝕜 : Spec 𝕜[t] ⟶ Spec 𝕜`, and
the cylinder `cylinder 𝕜 X f = X ×_{Spec 𝕜} Spec 𝕜[t]`. -/

/-- The affine line `𝔸¹_𝕜 = Spec 𝕜[t]`. -/
abbrev affineLine (𝕜 : Type) [Field 𝕜] : Scheme.{0} := Spec (CommRingCat.of (Polynomial 𝕜))

/-- The structure morphism `𝔸¹_𝕜 ⟶ Spec 𝕜`. -/
abbrev affineLineStruct (𝕜 : Type) [Field 𝕜] : affineLine 𝕜 ⟶ Spec (CommRingCat.of 𝕜) :=
  Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))

/-- The `𝔸¹`-cylinder `X ×_{Spec 𝕜} 𝔸¹_𝕜` over an `𝕜`-scheme `X`. -/
abbrev cylinder (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of 𝕜)) :
    Scheme.{0} :=
  Limits.pullback f (affineLineStruct 𝕜)

/-- The `𝕜`-algebra structure on the sections `Γ(X, U)`, induced by the structure morphism
`f : X ⟶ Spec 𝕜`. -/
noncomputable def sectionAlgebra (𝕜 : Type) [Field 𝕜] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of 𝕜)) (U : X.Opens) :
    Algebra 𝕜 ((X.presheaf.obj (Opposite.op U) : Type)) :=
  RingHom.toAlgebra ((Scheme.ΓSpecIso (CommRingCat.of 𝕜)).inv ≫ f.appTop ≫
    (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)).hom

variable (𝕜 : Type) [Field 𝕜]

/-- **The function field of the `𝔸¹`-cylinder is `RatFunc κ(X)`.**

Let `X` be an integral `𝕜`-scheme and `P = X ×_{Spec 𝕜} Spec 𝕜[t]` the cylinder; then the function
field of `P` is the rational function field `κ(X)(t)` in one variable over the function field of
`X`. -/
theorem ratFunc_functionField_cylinder (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of 𝕜))
    [IrreducibleSpace X] [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral (cylinder 𝕜 X f)] :
    Nonempty (RatFunc (X.functionField : Type) ≃+* ((cylinder 𝕜 X f).functionField : Type)) := by
  classical
  -- the first projection `p : X × 𝔸¹ ⟶ X`
  let p : cylinder 𝕜 X f ⟶ X := Limits.pullback.fst f (affineLineStruct 𝕜)
  -- a nonempty affine open `U ⊆ X`
  obtain ⟨_, ⟨U, hUmem, rfl⟩, hηU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (a := genericPoint X) (u := (⊤ : Set X)) trivial isOpen_univ
  haveI : Nonempty U := ⟨genericPoint X, hηU⟩
  have hUaff : IsAffineOpen U := hUmem
  -- the projection is an affine morphism, so `p ⁻¹ᵁ U` is affine
  haveI hpAff : IsAffineHom p := by
    haveI hsb : MorphismProperty.IsStableUnderBaseChange @IsAffineHom := inferInstance
    haveI : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) f :=
      ⟨fun pb hg => hsb.of_isPullback pb hg⟩
    exact MorphismProperty.pullback_fst _ _ (inferInstance : IsAffineHom _)
  let V : (cylinder 𝕜 X f).Opens := p ⁻¹ᵁ U
  have hVaff : IsAffineOpen V := hUaff.preimage p
  -- `V` is nonempty: use the section `q` of `p` given by `t ↦ 0`
  have hVne : Nonempty V := by
    obtain ⟨q, hq⟩ := exists_section_pullback_affineLine 𝕜 X f
    refine ⟨⟨q (genericPoint X), ?_⟩⟩
    show p (q (genericPoint X)) ∈ U
    have : p (q (genericPoint X)) = genericPoint X := by
      rw [← Scheme.Hom.comp_apply, hq]
      rfl
    rw [this]
    exact hηU
  -- `κ(P)` is the fraction field of `Γ(P, V)`
  haveI hVn : Nonempty ↥V := hVne
  have hFracV : IsFractionRing ((cylinder 𝕜 X f).presheaf.obj (Opposite.op V) : Type)
      ((cylinder 𝕜 X f).functionField : Type) :=
    functionField_isFractionRing_of_isAffineOpen _ V hVaff
  -- `κ(X)` is the fraction field of `Γ(X, U)`
  have hFracX : IsFractionRing ((X.presheaf.obj (Opposite.op U) : Type)) (X.functionField : Type) :=
    functionField_isFractionRing_of_isAffineOpen X U hUaff
  -- the ring of sections of the chart `V` is `Γ(X, U)[t]`
  obtain ⟨eRV⟩ := sections_preimage_fst_pullback_affineOpen 𝕜 X f U hUaff
  -- transport the fraction-ring structure to `Γ(X, U)[t]`
  letI : Algebra (Polynomial ((X.presheaf.obj (Opposite.op U) : Type)))
      ((cylinder 𝕜 X f).functionField : Type) :=
    RingHom.toAlgebra ((algebraMap
      ((cylinder 𝕜 X f).presheaf.obj (Opposite.op V) : Type)
      ((cylinder 𝕜 X f).functionField : Type)).comp eRV.symm.toRingHom)
  have hFrac2 : IsFractionRing (Polynomial ((X.presheaf.obj (Opposite.op U) : Type)))
      ((cylinder 𝕜 X f).functionField : Type) :=
    IsFractionRing.of_ringEquiv_left eRV.symm
      (fun x => by rw [RingHom.algebraMap_toAlgebra]; rfl)
  -- and `RatFunc κ(X)` is a fraction ring of `Γ(X, U)[t]`
  obtain ⟨hRat⟩ := ratFunc_equiv_fractionRing_polynomial
    ((X.presheaf.obj (Opposite.op U) : Type)) (X.functionField : Type)
  -- compare the two fraction rings of `Γ(X, U)[t]`
  have hAlg : ((cylinder 𝕜 X f).functionField : Type) ≃+*
      FractionRing (Polynomial ((X.presheaf.obj (Opposite.op U) : Type))) :=
    (IsLocalization.algEquiv (nonZeroDivisors (Polynomial ((X.presheaf.obj (Opposite.op U) : Type))))
      ((cylinder 𝕜 X f).functionField : Type)
      (FractionRing (Polynomial ((X.presheaf.obj (Opposite.op U) : Type))))).toRingEquiv
  exact ⟨hRat.trans hAlg.symm⟩

end

/-- **The function field of `X × 𝔸¹` is `RatFunc κ(X)`.**  Let `X` be an integral scheme over `𝕜`
(structure map `f : X ⟶ Spec 𝕜`) and let `W` be any model of the fibre product of `X` with the affine
line `Spec 𝕜[t]` over `𝕜`.  Then the function field of `W` is the rational function field in one
variable over the function field of `X`.

This is the second of the two computations needed for the (F1) inputs of the Crauder–Katz link: the
two exceptional divisors of the link are birational to `ℙ¹ × C` and `ℙ¹ × C'`, equivalently to
`𝔸¹ × C` and `𝔸¹ × C'`, so their function fields are `κ(C)(t)` and `κ(C')(t)`, and the model
`Work.CrauderKatz.cylinderField 𝕜 X = RatFunc κ(C)` of this area is exactly the right-hand side.  The
conclusion here is a ring equivalence (not yet the `𝕜`-linear form `ResAlgEquiv` used by the (F1)
fields of `Work.CrauderKatz.CrauderKatzLink`).

Mathlib has no function field of a fibre product, so this fills a genuine gap in the library; the route
is to reduce to a dense affine open `Spec A ⊆ X`, where `Scheme.functionField` is a fraction ring of
`A`, then compute `A ⊗_𝕜 𝕜[t] = A[t]` and use that `RatFunc` is a fraction ring of the one-variable
polynomial ring over the fraction field of `A`. -/
theorem functionField_prod_affineLine (𝕜 : Type) [Field 𝕜]
    (X : AlgebraicGeometry.Scheme.{0}) (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of 𝕜))
    [IrreducibleSpace X] [AlgebraicGeometry.IsIntegral X]
    (W : AlgebraicGeometry.Scheme.{0}) [IrreducibleSpace W] [AlgebraicGeometry.IsIntegral W]
    (hW : Nonempty (W ≅ CategoryTheory.Limits.pullback f
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap 𝕜 (Polynomial 𝕜)))))) :
    Nonempty (RatFunc (AlgebraicGeometry.Scheme.functionField X : Type) ≃+*
      (AlgebraicGeometry.Scheme.functionField W : Type)) := by
  obtain ⟨e⟩ := hW
  haveI : AlgebraicGeometry.IsIntegral (cylinder 𝕜 X f) :=
    AlgebraicGeometry.IsIntegral.of_isIso e.hom
  obtain ⟨h1⟩ := ratFunc_functionField_cylinder 𝕜 X f
  obtain ⟨h2⟩ := functionField_iso e
  exact ⟨h1.trans h2.symm⟩

end Work.CrauderKatz
