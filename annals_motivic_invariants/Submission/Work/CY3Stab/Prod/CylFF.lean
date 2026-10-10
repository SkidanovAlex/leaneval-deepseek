import Mathlib
import Submission.Work.CY3Stab.Cylinder
import Submission.Work.K3.BaseChangeBirational
import Submission.Work.CY3Stab.Prod.isIntegral_wProd
import Submission.Work.CY3Stab.Prod.ProdFibDefs
import Submission.Work.CY3Stab.Prod.SecAt
import Submission.Work.K3Inputs.exists_variety_prodOver_affineSpace

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Prod.CylFF` — function fields of the cylinder and its projection

Piece of the proof that a partial map on the cylinder `𝔸ᵏ ×_𝕜 X` which is the base change of a
partial map on `X` descends to `X`: the compatibility lemmas between the projection
`cylProj : 𝔸ᵏ ×_𝕜 X ⟶ X` and the function fields.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- **The projection `𝔸ᵏ ×_𝕜 X ⟶ X`** of the cylinder. -/
noncomputable abbrev cylProj (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))] (k : ℕ) :
    Work.CY3Stab.WProd (𝕜 := 𝕜) X k ⟶ X :=
  CategoryTheory.Limits.pullback.snd (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
    (X ↘ Spec (CommRingCat.of 𝕜))

/-- The canonical `algebraMap` `𝒪_{X,x} ⟶ K(X)`, as a morphism of rings. -/
noncomputable def ffAlgMap (X : Scheme.{0}) [IrreducibleSpace X] (x : X) :
    X.presheaf.stalk x ⟶ X.functionField :=
  CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)

/-- `ffAlgMap` is the specialization map of the structure sheaf. -/
lemma ffAlgMap_eq_stalkSpecializes (X : Scheme.{0}) [IrreducibleSpace X] (x : X) :
    ffAlgMap X x = X.presheaf.stalkSpecializes (genericPoint_specializes x) := by
  rw [ffAlgMap]
  apply CommRingCat.hom_ext
  rw [RingHom.algebraMap_toAlgebra]
  congr 1

/-- **The generic point of the cylinder specializes onto the generic point of `X`** (via the
section of the projection over the origin). -/
theorem cylProj_specializes_genericPoint (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))]
    (k : ℕ) [IrreducibleSpace X] [IrreducibleSpace (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)] :
    cylProj (𝕜 := 𝕜) X k (genericPoint (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)) ⤳ genericPoint X := by
  have h₁ : genericPoint (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) ⤳
      sec (𝕜 := 𝕜) k X (genericPoint X) := genericPoint_specializes _
  have h₂ : cylProj (𝕜 := 𝕜) X k (sec (𝕜 := 𝕜) k X (genericPoint X)) = genericPoint X := by
    have := congrArg (fun f => f (genericPoint X)) (sec_proj (𝕜 := 𝕜) k X)
    simpa using this
  have h₃ := h₁.map (cylProj (𝕜 := 𝕜) X k).continuous
  rwa [h₂] at h₃

/-- **Functoriality of the germ of an open subscheme along specialization.** -/
theorem Opens.fromSpecStalkOfMem_stalkSpecializes {X : Scheme.{0}} (U : X.Opens) {x y : X}
    (h : x ⤳ y) (hx : x ∈ U) (hy : y ∈ U) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ U.fromSpecStalkOfMem y hy =
      U.fromSpecStalkOfMem x hx := by
  rw [← cancel_mono U.ι]
  rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]

section CylFF

variable (X : Scheme.{0}) [X.Over (Spec (CommRingCat.of 𝕜))] (k : ℕ)

/-- The stalk map of the cylinder projection at the generic point is injective: it is a flat local
map between domains. -/
theorem cylProj_stalkMap_genericPoint_injective [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)]
    [IrreducibleSpace (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)] :
    Function.Injective
      ((cylProj (𝕜 := 𝕜) X k).stalkMap
        (genericPoint (Work.CY3Stab.WProd (𝕜 := 𝕜) X k))).hom := by
  haveI : Flat (CategoryTheory.Limits.pullback.snd (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ Spec (CommRingCat.of 𝕜))
      (X ↘ Spec (CommRingCat.of 𝕜))) := inferInstance
  letI : Algebra (X.presheaf.stalk (cylProj (𝕜 := 𝕜) X k (genericPoint (Work.CY3Stab.WProd (𝕜 := 𝕜) X k))))
      ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk
        (genericPoint (Work.CY3Stab.WProd (𝕜 := 𝕜) X k))) :=
    (((cylProj (𝕜 := 𝕜) X k).stalkMap
      (genericPoint (Work.CY3Stab.WProd (𝕜 := 𝕜) X k))).hom).toAlgebra
  haveI : Module.Flat (X.presheaf.stalk (cylProj (𝕜 := 𝕜) X k (genericPoint (Work.CY3Stab.WProd (𝕜 := 𝕜) X k))))
      ((Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk
        (genericPoint (Work.CY3Stab.WProd (𝕜 := 𝕜) X k))) :=
    Flat.stalkMap (cylProj (𝕜 := 𝕜) X k) (genericPoint (Work.CY3Stab.WProd (𝕜 := 𝕜) X k))
  have h := (Module.isTorsionFree_iff_algebraMap_injective
    (R := X.presheaf.stalk (cylProj (𝕜 := 𝕜) X k (genericPoint (Work.CY3Stab.WProd (𝕜 := 𝕜) X k))))
    (A := (Work.CY3Stab.WProd (𝕜 := 𝕜) X k).presheaf.stalk
      (genericPoint (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)))).mp
    (inferInstance : Module.IsTorsionFree _ _)
  rw [RingHom.algebraMap_toAlgebra] at h
  exact h

/-- **The canonical map of function fields `K(X) ⟶ K(𝔸ᵏ ×_𝕜 X)`** induced by the projection. -/
noncomputable def cylFFMap [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)]
    [IrreducibleSpace (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)] :
    X.functionField ⟶ (Work.CY3Stab.WProd (𝕜 := 𝕜) X k).functionField :=
  CommRingCat.ofHom
    (IsFractionRing.lift
      (A := X.presheaf.stalk (cylProj (𝕜 := 𝕜) X k (genericPoint (Work.CY3Stab.WProd (𝕜 := 𝕜) X k))))
      (K := X.functionField) (L := (Work.CY3Stab.WProd (𝕜 := 𝕜) X k).functionField)
      (g := ((cylProj (𝕜 := 𝕜) X k).stalkMap
        (genericPoint (Work.CY3Stab.WProd (𝕜 := 𝕜) X k))).hom)
      (cylProj_stalkMap_genericPoint_injective X k))

/-- The defining property of `cylFFMap`: it extends the stalk map of the projection at the
generic point. -/
lemma ffAlgMap_cylFFMap [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)]
    [IrreducibleSpace (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)] :
    ffAlgMap X (cylProj (𝕜 := 𝕜) X k (genericPoint (Work.CY3Stab.WProd (𝕜 := 𝕜) X k))) ≫
        cylFFMap (𝕜 := 𝕜) X k =
      (cylProj (𝕜 := 𝕜) X k).stalkMap (genericPoint (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)) := by
  rw [ffAlgMap, cylFFMap]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact IsFractionRing.lift_algebraMap (cylProj_stalkMap_genericPoint_injective X k) a

end CylFF

/-- **The compatibility square of the function field map of the projection**: for every point `y`
of the cylinder, the stalk map of the projection composed with the algebra map of `K(𝔸ᵏ ×_𝕜 X)`
equals the algebra map of `K(X)` composed with `cylFFMap`. -/
theorem cylFFMap_sq {X : Scheme.{0}} [X.Over (Spec (CommRingCat.of 𝕜))] {k : ℕ}
    [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)]
    [IrreducibleSpace (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)]
    (y : Work.CY3Stab.WProd (𝕜 := 𝕜) X k) :
    (cylProj (𝕜 := 𝕜) X k).stalkMap y ≫ ffAlgMap (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) y =
      ffAlgMap X (cylProj (𝕜 := 𝕜) X k y) ≫ cylFFMap (𝕜 := 𝕜) X k := by
  have hnat := Scheme.Hom.stalkSpecializes_stalkMap (cylProj (𝕜 := 𝕜) X k)
    (genericPoint (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)) y (genericPoint_specializes y)
  rw [ffAlgMap_eq_stalkSpecializes (X := Work.CY3Stab.WProd (𝕜 := 𝕜) X k) y, ← hnat,
    ← ffAlgMap_cylFFMap (𝕜 := 𝕜) X k]
  rw [ffAlgMap_eq_stalkSpecializes (X := X)
      (cylProj (𝕜 := 𝕜) X k (genericPoint (Work.CY3Stab.WProd (𝕜 := 𝕜) X k))),
    ffAlgMap_eq_stalkSpecializes (X := X) (cylProj (𝕜 := 𝕜) X k y)]
  rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]

end

end Work.CY3Stab.Prod

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- `fromSpecStalkOfMem` does not depend on the proof of membership. -/
lemma Scheme.Opens.fromSpecStalkOfMem_congr {X : Scheme.{0}} (U : X.Opens) {x : X}
    (h₁ h₂ : x ∈ U) : U.fromSpecStalkOfMem x h₁ = U.fromSpecStalkOfMem x h₂ := by
  rw [← cancel_mono U.ι, Scheme.Opens.fromSpecStalkOfMem_ι]

/-- `fromSpecStalkOfMem` of a partial map does not depend on the proof of membership. -/
lemma PartialMap.fromSpecStalkOfMem_congr {X Y : Scheme.{0}} (f : X.PartialMap Y) {x : X}
    (h₁ h₂ : x ∈ f.domain) : f.fromSpecStalkOfMem h₁ = f.fromSpecStalkOfMem h₂ := by
  simp only [Scheme.PartialMap.fromSpecStalkOfMem]

/-- The germ of a partial map at the generic point, for any proof of density. -/
lemma PartialMap.fromFunctionField_eq_fromSpecStalkOfMem {X Y : Scheme.{0}}
    (f : X.PartialMap Y) [IrreducibleSpace X] (h : genericPoint X ∈ f.domain) :
    f.fromSpecStalkOfMem h = f.fromFunctionField := by
  simp only [Scheme.PartialMap.fromFunctionField, Scheme.PartialMap.fromSpecStalkOfMem,
    Scheme.Opens.fromSpecStalkOfMem_congr]

end

end Work.CY3Stab.Prod

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- Two partial maps with the same rational map have the same restriction to the function
field. -/
lemma PartialMap.fromFunctionField_eq_of_toRationalMap_eq {X Y : Scheme.{0}} [IrreducibleSpace X]
    {f g : X.PartialMap Y} (h : f.toRationalMap = g.toRationalMap) :
    f.fromFunctionField = g.fromFunctionField := by
  rw [← RationalMap.fromFunctionField_toRationalMap (f := f), h,
    RationalMap.fromFunctionField_toRationalMap (f := g)]

/-- The germ of a partial map at a point, composed with the structure map from the stalk to the
function field, is the function field restriction of the partial map. -/
lemma PartialMap.ffAlgMap_fromSpecStalkOfMem_eq_fromFunctionField {X Y : Scheme.{0}}
    (f : X.PartialMap Y) [IrreducibleSpace X] (x : X) (hx : x ∈ f.domain)
    (hg : genericPoint X ∈ f.domain) :
    Spec.map (ffAlgMap X x) ≫ f.fromSpecStalkOfMem hx = f.fromFunctionField := by
  have h := Opens.fromSpecStalkOfMem_stalkSpecializes f.domain (genericPoint_specializes x) hg hx
  rw [← ffAlgMap_eq_stalkSpecializes] at h
  rw [Scheme.PartialMap.fromSpecStalkOfMem, ← Category.assoc, h,
    ← PartialMap.fromFunctionField_eq_fromSpecStalkOfMem f hg]
  rfl

/-- The map on points of `Spec.map` of a homomorphism of fields is surjective. -/
lemma Spec.map_surjective_of_field {K L : Type} [Field K] [Field L] (f : K →+* L) :
    Function.Surjective ⇑(Spec.map (CommRingCat.ofHom f)) := by
  intro z
  exact ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩

end

end Work.CY3Stab.Prod

