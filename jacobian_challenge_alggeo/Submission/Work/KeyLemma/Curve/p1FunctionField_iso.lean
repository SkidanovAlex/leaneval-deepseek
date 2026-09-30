import Mathlib
import Submission.Work.KeyLemma.Curve.p1FunctionField
import Submission.Work.AbVar.P1Chart.ChartK

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.KeyLemma.Curve

universe u

set_option synthInstance.maxHeartbeats 800000
open CategoryTheory AlgebraicGeometry Limits
open scoped Classical

noncomputable section

variable {k : Type u} [Field k]

/-- The `⊤` open of an irreducible scheme is nonempty. -/
instance instNonemptyTopOpens (X : Scheme.{u}) [IrreducibleSpace X] :
    Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

/-- **The structure map `k ⟶ K(X)`** of the function field of a scheme `X` over `Spec k`,
obtained from the structure morphism by taking the germ at the generic point. -/
abbrev functionFieldStruct (X : Scheme.{u}) [IrreducibleSpace X]
    (f : X ⟶ Spec (CommRingCat.of k)) : CommRingCat.of k ⟶ X.functionField :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫ X.germToFunctionField ⊤

/-- The canonical morphism `Spec K(X) ⟶ X` at the generic point is `Spec` of the structure map
`k ⟶ K(X)`. -/
theorem fromSpecStalk_comp_hom (X : Scheme.{u}) [IrreducibleSpace X]
    (f : X ⟶ Spec (CommRingCat.of k)) :
    X.fromSpecStalk (genericPoint X) ≫ f = Spec.map (functionFieldStruct X f) := by
  have hL : (X.fromSpecStalk (genericPoint X)).appTop =
      X.germToFunctionField ⊤ ≫
        (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).inv := by
    rw [Scheme.fromSpecStalk_appTop]; simp
  have hR : (Scheme.ΓSpecIso (CommRingCat.of k)).inv
        ≫ (Spec.map (functionFieldStruct X f)).appTop =
      functionFieldStruct X f
        ≫ (Scheme.ΓSpecIso (CommRingCat.of X.functionField)).inv := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of X.functionField)).hom]
    simp only [Category.assoc]
    erw [Scheme.ΓSpecIso_naturality (functionFieldStruct X f),
      Iso.inv_hom_id_assoc (Scheme.ΓSpecIso (CommRingCat.of k)),
      Iso.inv_hom_id (Scheme.ΓSpecIso (CommRingCat.of X.functionField)), Category.comp_id]
  apply AlgebraicGeometry.ext_to_Spec
  rw [Scheme.Γ_map_op, Scheme.Γ_map_op, Scheme.Hom.comp_appTop, hL]
  erw [hR]
  rfl

/-- A morphism `k ⟶ K(X)` whose `Spec` is the canonical morphism `Spec K(X) ⟶ Spec k` is the
structure map: the `k`-algebra structure on the function field is determined by the structural
morphism. -/
theorem eq_functionFieldStruct_of_specMap_eq (X : Scheme.{u}) [IrreducibleSpace X]
    (f : X ⟶ Spec (CommRingCat.of k)) (θ : CommRingCat.of k ⟶ X.functionField)
    (h : Spec.map θ = X.fromSpecStalk (genericPoint X) ≫ f) :
    θ = functionFieldStruct X f := by
  rw [fromSpecStalk_comp_hom X f] at h
  exact Spec.map_injective h

/-- The ring isomorphism underlying an isomorphism in the category of commutative rings. -/
def isoToRingEquiv {R S : CommRingCat.{u}} (e : R ≅ S) : R ≃+* S where
  toFun := e.hom.hom
  invFun := e.inv.hom
  left_inv x := RingHom.congr_fun (congrArg CommRingCat.Hom.hom e.hom_inv_id) x
  right_inv x := RingHom.congr_fun (congrArg CommRingCat.Hom.hom e.inv_hom_id) x
  map_mul' := map_mul _
  map_add' := map_add _

@[simp] lemma isoToRingEquiv_toRingHom {R S : CommRingCat.{u}} (e : R ≅ S) :
    (isoToRingEquiv e).toRingHom = e.hom.hom := rfl

@[simp] lemma isoToRingEquiv_symm_toRingHom {R S : CommRingCat.{u}} (e : R ≅ S) :
    (isoToRingEquiv e).symm.toRingHom = e.inv.hom := rfl

/-- In a domain, an isomorphism of rings carries the non-zero divisors to the non-zero
divisors. -/
lemma submonoid_map_nonZeroDivisors {R S : Type*} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] (e : R ≃+* S) :
    (nonZeroDivisors R).map e = nonZeroDivisors S := by
  ext x
  rw [Submonoid.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero] at hy ⊢
    simpa using hy
  · intro hx
    rw [mem_nonZeroDivisors_iff_ne_zero] at hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    simpa [RingEquiv.map_eq_zero_iff] using hx

section Main

variable (k : Type u) [Field k]

/-- `p1BaseEquiv` agrees with the chart construction's `constToZero`. -/
lemma p1BaseEquiv_eq_constToZero :
    (Work.AbVar.p1BaseEquiv k).toRingHom = Work.AbVar.ProjectiveLine.constToZero (R := k) := by
  ext r
  rfl

/-- **The chart `D₊(X₁) ⟶ ℙ¹` is a morphism over `Spec k`.** -/
theorem awayι_comp_hom :
    Proj.awayι (Work.AbVar.P1Grading k) (MvPolynomial.X 1)
        (Work.AbVar.P1Chart.X_mem k 1) Nat.one_pos ≫ (Work.AbVar.P1 k).hom
      = Spec.map (CommRingCat.ofHom (algebraMap k
          (HomogeneousLocalization.Away (Work.AbVar.P1Grading k) (MvPolynomial.X 1)))) := by
  rw [Work.AbVar.p1_hom, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The identification of the global sections of an open subscheme with the sections over the
open set, on top sections. -/
lemma ΓSpecIso_inv_toSpecΓ_appTop {X : Scheme.{u}} (U : X.Opens) [Nonempty U] :
    (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (U.toSpecΓ).appTop = U.topIso.inv := by
  rw [Scheme.Opens.toSpecΓ_appTop]
  simp

/-- **The germ of the structure sheaf at the generic point of an affine open**, read through the
isomorphism `Spec Γ(X,U) ≅ U`: it is the composite of the germ with the inverse of the
`ΓSpecIso` of the function field. -/
lemma topIso_inv_fromSpecStalkOfMem_appTop {X : Scheme.{u}} [IrreducibleSpace X]
    (U : X.Opens) [Nonempty U] (hη : genericPoint X ∈ U) :
    U.topIso.inv ≫ (U.fromSpecStalkOfMem (genericPoint X) hη).appTop
      = X.germToFunctionField U ≫ (Scheme.ΓSpecIso (X.functionField)).inv := by
  have h1 : U.topIso.inv = (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (U.toSpecΓ).appTop :=
    (ΓSpecIso_inv_toSpecΓ_appTop U).symm
  rw [h1, Category.assoc]
  rw [← Scheme.Hom.comp_appTop, Scheme.Opens.fromSpecStalkOfMem_toSpecΓ,
    ← Scheme.ΓSpecIso_inv_naturality]

/-- The chart `D₊(f) ⟶ Proj 𝒜` composed with the chart inclusion: `Spec` of the section
isomorphism followed by the chart map is the canonical map through the affine open. -/
lemma specMap_awayToSection_comp_awayι {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (f : A) {m : ℕ} (hf : f ∈ 𝒜 m)
    (hm : 0 < m) (hU : IsAffineOpen (Proj.basicOpen 𝒜 f)) :
    Spec.map (Proj.awayToSection 𝒜 f) ≫ Proj.awayι 𝒜 f hf hm
      = hU.isoSpec.inv ≫ (Proj.basicOpen 𝒜 f).ι := by
  have hcancel : Spec.map (Proj.awayToSection 𝒜 f)
      ≫ (Proj.basicOpenIsoSpec 𝒜 f hf hm).inv = hU.isoSpec.inv := by
    haveI : IsIso (Proj.basicOpenToSpec 𝒜 f) := by
      rw [← Proj.basicOpenIsoSpec_hom 𝒜 f hf hm]
      infer_instance
    rw [show (Proj.basicOpenIsoSpec 𝒜 f hf hm).inv = inv (Proj.basicOpenToSpec 𝒜 f) from rfl,
      IsIso.comp_inv_eq (Proj.basicOpenToSpec 𝒜 f)]
    rw [show Proj.basicOpenToSpec 𝒜 f
        = (Proj.basicOpen 𝒜 f).toSpecΓ ≫ Spec.map (Proj.awayToSection 𝒜 f) from rfl]
    rw [← Category.assoc, hU.isoSpec_inv_toSpecΓ, Category.id_comp]
  rw [show Proj.awayι 𝒜 f hf hm
      = (Proj.basicOpenIsoSpec 𝒜 f hf hm).inv ≫ (Proj.basicOpen 𝒜 f).ι from rfl]
  rw [← Category.assoc, hcancel]

/-- The germ of the structure sheaf at the generic point of an affine open, as a morphism into the
open subscheme. -/
lemma specMap_germToFunctionField_isoSpec_inv {X : Scheme.{u}} [IrreducibleSpace X]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) :
    Spec.map (X.germToFunctionField U) ≫ hU.isoSpec.inv
      = U.fromSpecStalkOfMem (genericPoint X)
          (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)) := by
  rw [← Scheme.Opens.fromSpecStalkOfMem_toSpecΓ, Category.assoc, hU.toSpecΓ_isoSpec_inv,
    Category.comp_id]

/-- **The function field of `ℙ¹` is the rational function field `k(T)`.** -/
theorem p1FunctionField_ratFunc (k : Type u) [Field k] :
    Nonempty (↥((Work.AbVar.P1 k).left.functionField) ≃ₐ[k] RatFunc k) := by
  haveI hInt : IsIntegral (Proj (Work.AbVar.P1Grading k)) :=
    Work.AbVar.ProjectiveLine.isIntegral_P1 k
  haveI hneU : Nonempty (Proj.basicOpen (Work.AbVar.P1Grading k) (MvPolynomial.X 1)) :=
    ⟨Work.AbVar.ProjectiveLine.zeroPt k,
      Work.AbVar.ProjectiveLine.zeroPt_mem_basicOpen k (MvPolynomial.X_ne_zero 1)⟩
  have hη : genericPoint (Proj (Work.AbVar.P1Grading k)) ∈
      Proj.basicOpen (Work.AbVar.P1Grading k) (MvPolynomial.X 1) :=
    ((genericPoint_spec _).mem_open_set_iff
      (Proj.basicOpen (Work.AbVar.P1Grading k) (MvPolynomial.X 1)).isOpen).mpr
      (by simpa using hneU)
  have hUaff : IsAffineOpen (Proj.basicOpen (Work.AbVar.P1Grading k) (MvPolynomial.X 1)) :=
    Proj.isAffineOpen_basicOpen _ _ (Work.AbVar.P1Chart.X_mem k 1) Nat.one_pos
  haveI hFRΓ : IsFractionRing
      ↥Γ(Proj (Work.AbVar.P1Grading k), Proj.basicOpen (Work.AbVar.P1Grading k) (MvPolynomial.X 1))
      ↥(Proj (Work.AbVar.P1Grading k)).functionField :=
    functionField_isFractionRing_of_isAffineOpen _
      (Proj.basicOpen (Work.AbVar.P1Grading k) (MvPolynomial.X 1)) hUaff
  haveI hdomΓ : IsDomain
      ↥Γ(Proj (Work.AbVar.P1Grading k),
        Proj.basicOpen (Work.AbVar.P1Grading k) (MvPolynomial.X 1)) :=
    Function.Injective.isDomain
      ((Proj (Work.AbVar.P1Grading k)).germToFunctionField
        (Proj.basicOpen (Work.AbVar.P1Grading k) (MvPolynomial.X 1))).hom
      (Scheme.germToFunctionField_injective (Proj (Work.AbVar.P1Grading k))
        (Proj.basicOpen (Work.AbVar.P1Grading k) (MvPolynomial.X 1)))
  haveI hdomO : IsDomain
      (HomogeneousLocalization.Away (Work.AbVar.P1Grading k) (MvPolynomial.X 1)) :=
    MulEquiv.isDomain (Polynomial k) (Work.AbVar.P1Chart.awayXAlgEquiv k 1).toMulEquiv
  -- the chart `D₊(X₁)` as a fraction-field structure on `K(ℙ¹)`
  let γ : ↧(HomogeneousLocalization.Away (Work.AbVar.P1Grading k) (MvPolynomial.X 1)) ⟶
      (Proj (Work.AbVar.P1Grading k)).functionField :=
    Proj.awayToSection (Work.AbVar.P1Grading k) (MvPolynomial.X 1) ≫
      (Proj (Work.AbVar.P1Grading k)).germToFunctionField
        (Proj.basicOpen (Work.AbVar.P1Grading k) (MvPolynomial.X 1))
  have hγ : γ = Proj.awayToSection (Work.AbVar.P1Grading k) (MvPolynomial.X 1) ≫
      (Proj (Work.AbVar.P1Grading k)).germToFunctionField
        (Proj.basicOpen (Work.AbVar.P1Grading k) (MvPolynomial.X 1)) := rfl
  letI hγalg : Algebra (HomogeneousLocalization.Away (Work.AbVar.P1Grading k) (MvPolynomial.X 1))
      ↥(Proj (Work.AbVar.P1Grading k)).functionField := γ.hom.toAlgebra
  -- `K(ℙ¹)` is the fraction field of the chart ring
  have hFRchart : IsFractionRing
      (HomogeneousLocalization.Away (Work.AbVar.P1Grading k) (MvPolynomial.X 1))
      ↥(Proj (Work.AbVar.P1Grading k)).functionField := by
    refine IsLocalization.of_ringEquiv_left
      (M₂ := nonZeroDivisors
        (HomogeneousLocalization.Away (Work.AbVar.P1Grading k) (MvPolynomial.X 1)))
      (M₁ := nonZeroDivisors ↥Γ(Proj (Work.AbVar.P1Grading k),
        Proj.basicOpen (Work.AbVar.P1Grading k) (MvPolynomial.X 1)))
      (isoToRingEquiv (Proj.basicOpenIsoAway (Work.AbVar.P1Grading k) (MvPolynomial.X 1)
        (Work.AbVar.P1Chart.X_mem k 1) Nat.one_pos)) ?_ ?_
    · exact submonoid_map_nonZeroDivisors _
    · intro x
      have h2 : (isoToRingEquiv (Proj.basicOpenIsoAway (Work.AbVar.P1Grading k) (MvPolynomial.X 1)
            (Work.AbVar.P1Chart.X_mem k 1) Nat.one_pos)) x
          = (Proj.awayToSection (Work.AbVar.P1Grading k) (MvPolynomial.X 1)).hom x := by
        rw [show (isoToRingEquiv (Proj.basicOpenIsoAway (Work.AbVar.P1Grading k) (MvPolynomial.X 1)
              (Work.AbVar.P1Chart.X_mem k 1) Nat.one_pos)) x
            = ((Proj.basicOpenIsoAway (Work.AbVar.P1Grading k) (MvPolynomial.X 1)
                (Work.AbVar.P1Chart.X_mem k 1) Nat.one_pos).hom).hom x from rfl,
          Proj.basicOpenIsoAway_hom]
      rw [h2, show (algebraMap
          (HomogeneousLocalization.Away (Work.AbVar.P1Grading k) (MvPolynomial.X 1))
          ↥(Proj (Work.AbVar.P1Grading k)).functionField) x = γ.hom x from rfl, hγ]
      rfl
  -- the chart is the generic point of `Spec` of the chart ring
  have hfrom : Spec.map γ ≫ Proj.awayι (Work.AbVar.P1Grading k) (MvPolynomial.X 1)
        (Work.AbVar.P1Chart.X_mem k 1) Nat.one_pos
      = (Proj (Work.AbVar.P1Grading k)).fromSpecStalk
          (genericPoint (Proj (Work.AbVar.P1Grading k))) := by
    rw [hγ, Spec.map_comp, Category.assoc]
    rw [specMap_awayToSection_comp_awayι (Work.AbVar.P1Grading k) (MvPolynomial.X 1)
      (Work.AbVar.P1Chart.X_mem k 1) Nat.one_pos hUaff]
    rw [← Category.assoc]
    rw [specMap_germToFunctionField_isoSpec_inv
      (Proj.basicOpen (Work.AbVar.P1Grading k) (MvPolynomial.X 1)) hUaff]
    exact Scheme.Opens.fromSpecStalkOfMem_ι _ _ _
  -- the `k`-structure of the chart agrees with the canonical one
  letI hAlg : Algebra k ↥(Proj (Work.AbVar.P1Grading k)).functionField :=
    (functionFieldStruct (Proj (Work.AbVar.P1Grading k)) (Work.AbVar.P1 k).hom).hom.toAlgebra
  have hmain : CommRingCat.ofHom (algebraMap k
        (HomogeneousLocalization.Away (Work.AbVar.P1Grading k) (MvPolynomial.X 1))) ≫ γ
      = CommRingCat.ofHom (algebraMap k ↥(Proj (Work.AbVar.P1Grading k)).functionField) := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← awayι_comp_hom k, ← Category.assoc, hfrom, fromSpecStalk_comp_hom]
    congr 1
  -- `RatFunc k` as the fraction field of the chart ring
  let e : (HomogeneousLocalization.Away (Work.AbVar.P1Grading k) (MvPolynomial.X 1)) ≃+*
      Polynomial k := (Work.AbVar.P1Chart.awayXAlgEquiv k 1).toRingEquiv
  letI : Algebra (HomogeneousLocalization.Away (Work.AbVar.P1Grading k) (MvPolynomial.X 1))
      (RatFunc k) := ((algebraMap (Polynomial k) (RatFunc k)).comp e.toRingHom).toAlgebra
  haveI hloc : IsLocalization (nonZeroDivisors
      (HomogeneousLocalization.Away (Work.AbVar.P1Grading k) (MvPolynomial.X 1)))
      (RatFunc k) := by
    refine IsLocalization.of_ringEquiv_left
      (M₁ := nonZeroDivisors (Polynomial k))
      (M₂ := nonZeroDivisors
        (HomogeneousLocalization.Away (Work.AbVar.P1Grading k) (MvPolynomial.X 1)))
      (e := e) ?_ ?_
    · exact submonoid_map_nonZeroDivisors e
    · intro x
      rfl
  have hlin : ∀ a : k, (IsLocalization.algEquiv (nonZeroDivisors
        (HomogeneousLocalization.Away (Work.AbVar.P1Grading k) (MvPolynomial.X 1)))
          ↥(Proj (Work.AbVar.P1Grading k)).functionField (RatFunc k)).toRingEquiv
        ((algebraMap k ↥(Proj (Work.AbVar.P1Grading k)).functionField) a)
      = (algebraMap k (RatFunc k)) a := by
    intro a
    rw [show (algebraMap k ↥(Proj (Work.AbVar.P1Grading k)).functionField) a
        = γ.hom ((algebraMap k (HomogeneousLocalization.Away (Work.AbVar.P1Grading k)
            (MvPolynomial.X 1))) a) from
      (RingHom.congr_fun (congrArg CommRingCat.Hom.hom hmain) a).symm]
    rw [show γ.hom ((algebraMap k (HomogeneousLocalization.Away (Work.AbVar.P1Grading k)
          (MvPolynomial.X 1))) a)
        = (algebraMap (HomogeneousLocalization.Away (Work.AbVar.P1Grading k) (MvPolynomial.X 1))
            ↥(Proj (Work.AbVar.P1Grading k)).functionField)
          ((algebraMap k (HomogeneousLocalization.Away (Work.AbVar.P1Grading k)
            (MvPolynomial.X 1))) a) from rfl]
    change (IsLocalization.algEquiv (nonZeroDivisors
        (HomogeneousLocalization.Away (Work.AbVar.P1Grading k) (MvPolynomial.X 1)))
          ↥(Proj (Work.AbVar.P1Grading k)).functionField (RatFunc k))
        ((algebraMap (HomogeneousLocalization.Away (Work.AbVar.P1Grading k) (MvPolynomial.X 1))
            ↥(Proj (Work.AbVar.P1Grading k)).functionField)
          ((algebraMap k (HomogeneousLocalization.Away (Work.AbVar.P1Grading k)
            (MvPolynomial.X 1))) a)) = (algebraMap k (RatFunc k)) a
    rw [AlgEquiv.commutes (IsLocalization.algEquiv (nonZeroDivisors
        (HomogeneousLocalization.Away (Work.AbVar.P1Grading k) (MvPolynomial.X 1)))
          ↥(Proj (Work.AbVar.P1Grading k)).functionField (RatFunc k))
      ((algebraMap k (HomogeneousLocalization.Away (Work.AbVar.P1Grading k)
        (MvPolynomial.X 1))) a)]
    rw [show (algebraMap (HomogeneousLocalization.Away (Work.AbVar.P1Grading k) (MvPolynomial.X 1))
          (RatFunc k)) = (algebraMap (Polynomial k) (RatFunc k)).comp e.toRingHom from rfl,
      RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k) a]
    congr 1
    rw [RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom]
    exact AlgEquiv.commutes (Work.AbVar.P1Chart.awayXAlgEquiv k 1) a
  exact ⟨AlgEquiv.ofRingEquiv (f := (IsLocalization.algEquiv (nonZeroDivisors
      (HomogeneousLocalization.Away (Work.AbVar.P1Grading k) (MvPolynomial.X 1)))
        ↥(Proj (Work.AbVar.P1Grading k)).functionField (RatFunc k)).toRingEquiv) hlin⟩

/-- **The function field of `ℙ¹` is the rational function field `k(h)`.**  For transcendental
`h` on `C`, the function fields `K(ℙ¹)` and `k(h) = baseField C h` are both `k`-rational of
transcendence degree one, hence isomorphic over `k`.

Construction: the chart `Spec k[t] ⟶ ℙ¹` is an open immersion with dense image, so it induces an
isomorphism `K(ℙ¹) ≅ Frac k[t] = k(t)`; and `Polynomial.algEquivOfTranscendental k h hh` together
with `IsFractionRing` identifies `Frac k[t]` with `↥(baseField C h)`. -/
theorem p1FunctionField_iso {k : Type u} [Field k]
    (C : Work.CurveBasics.Curve k) {h : C.functionField} (hh : Transcendental k h) :
    Nonempty (↥((Work.AbVar.P1 k).left.functionField) ≃ₐ[k]
      ↥(Work.KeyLemma.Curve.baseField C h)) :=
  (p1FunctionField_ratFunc k).map fun e => e.trans (RatFunc.algEquivOfTranscendental h hh)

end Main

end

end Work.KeyLemma.Curve
