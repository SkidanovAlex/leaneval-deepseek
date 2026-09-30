/-
Area AV (abelian-variety toolkit) for the Jacobian challenge: basic definitions.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Abelian varieties: basic definitions

Vocabulary for area `AV` of the Jacobian challenge.

* `Work.AbVar.Sch k` is the category of `k`-schemes, i.e. `Over (Spec k)`.
* `Work.AbVar.Point X` is the type of `k`-points of `X`.
* `Work.AbVar.IsAbelianVariety A` says that `A` is smooth, proper and geometrically
  irreducible over `k`. The group structure is kept separate as a `GrpObj` instance so
  that the class can be stated without it.
* `Work.AbVar.IsPointedMap f` says that `f` maps the unit section to the unit section.
* `Work.AbVar.IsGroupHom f` says that `f` is a homomorphism of group schemes (i.e. a
  monoid-object morphism; this determines the behaviour on inverses).
* `Work.AbVar.sectionLeft`, `Work.AbVar.sectionRight` are the two graph sections
  `X ⟶ X ⊗ Y` and `Y ⟶ X ⊗ Y` used to state the rigidity lemma.

All tensor products are the cartesian monoidal structure on `Over (Spec k)`
(the fibre product over `k`).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped MonObj
open AlgebraicGeometry

namespace Work.AbVar

/-- The category of schemes over a field `k`. -/
abbrev Sch (k : Type u) [Field k] : Type (u + 1) := Over (Spec (.of k))

variable {k : Type u} [Field k]

/-- A `k`-point of a `k`-scheme `X`. -/
abbrev Point (X : Sch k) := 𝟙_ (Sch k) ⟶ X

/-- `X` is an abelian variety over `k`: a smooth, proper and geometrically irreducible
`k`-scheme. The group structure is supplied separately as a `GrpObj X` instance. -/
class IsAbelianVariety (X : Sch k) : Prop where
  smooth : Smooth X.hom
  isProper : IsProper X.hom
  geometricallyIrreducible : GeometricallyIrreducible X.hom

attribute [instance] IsAbelianVariety.smooth IsAbelianVariety.isProper
  IsAbelianVariety.geometricallyIrreducible

/-- A proper, geometrically integral group scheme over a field is commutative
(`AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`). -/
instance (priority := low) {H : Sch k} [GrpObj H] [IsProper H.hom]
    [GeometricallyIntegral H.hom] : IsCommMonObj H :=
  isCommMonObj_of_isProper_of_geometricallyIntegral H

/-- A morphism of group schemes is *pointed* if it maps the unit section to the unit
section. -/
def IsPointedMap {G H : Sch k} [GrpObj G] [GrpObj H] (f : G ⟶ H) : Prop :=
  η[G] ≫ f = η[H]

/-- A morphism of group schemes is a homomorphism if it preserves the group laws.
Concretely this is `IsMonHom f`, i.e. `μ[G] ≫ f = (f ⊗ₘ f) ≫ μ[H]`; this already forces
compatibility with the inverses. -/
abbrev IsGroupHom {G H : Sch k} [GrpObj G] [GrpObj H] (f : G ⟶ H) : Prop := IsMonHom f

section Hom

variable {G H K : Sch k} [GrpObj G] [GrpObj H] [GrpObj K]

lemma IsGroupHom.mul_eq {f : G ⟶ H} (hf : IsGroupHom f) :
    μ[G] ≫ f = (f ⊗ₘ f) ≫ μ[H] := hf.mul_hom

lemma IsGroupHom.one_eq {f : G ⟶ H} (hf : IsGroupHom f) : η[G] ≫ f = η[H] := hf.one_hom

lemma IsGroupHom.isPointedMap {f : G ⟶ H} (hf : IsGroupHom f) : IsPointedMap f := hf.one_hom

@[simp]
lemma isGroupHom_id : IsGroupHom (𝟙 G) := inferInstance

@[simp]
lemma isPointedMap_id : IsPointedMap (𝟙 G) := by simp [IsPointedMap]

lemma IsPointedMap.comp {f : G ⟶ H} {g : H ⟶ K} (hf : IsPointedMap f)
    (hg : IsPointedMap g) : IsPointedMap (f ≫ g) := by
  simp only [IsPointedMap] at hf hg ⊢
  rw [← Category.assoc, hf, hg]

/-- Homomorphisms of group schemes are closed under composition. -/
lemma IsGroupHom.comp {f : G ⟶ H} {g : H ⟶ K} (hf : IsGroupHom f) (hg : IsGroupHom g) :
    IsGroupHom (f ≫ g) :=
  letI := hf
  letI := hg
  inferInstance

/-- The obstruction to a morphism `g : G ⟶ H` of group schemes being a homomorphism:
the map `(x, y) ↦ g (x + y) - g x - g y`, computed in the group of morphisms
`G ⊗ G ⟶ H`. -/
noncomputable def homObstruction {G H : Sch k} [GrpObj G] [GrpObj H] (g : G ⟶ H) :
    G ⊗ G ⟶ H :=
  (μ[G] ≫ g) * (fst G G ≫ g)⁻¹ * (snd G G ≫ g)⁻¹

@[simp]
lemma homObstruction_eq {G H : Sch k} [GrpObj G] [GrpObj H] (g : G ⟶ H) :
    homObstruction g = (μ[G] ≫ g) * (fst G G ≫ g)⁻¹ * (snd G G ≫ g)⁻¹ := rfl

end Hom

section Sections

variable (X Y : Sch k)

/-- The graph section `X ⟶ X ⊗ Y`, `x ↦ (x, y₀)`. -/
noncomputable def sectionLeft (y0 : Point Y) : X ⟶ X ⊗ Y := lift (𝟙 X) (toUnit X ≫ y0)

/-- The graph section `Y ⟶ X ⊗ Y`, `y ↦ (x₀, y)`. -/
noncomputable def sectionRight (x0 : Point X) : Y ⟶ X ⊗ Y := lift (toUnit Y ≫ x0) (𝟙 Y)

@[simp]
lemma sectionLeft_fst (y0 : Point Y) : sectionLeft X Y y0 ≫ fst X Y = 𝟙 X := by
  simp [sectionLeft]

@[simp]
lemma sectionLeft_snd (y0 : Point Y) : sectionLeft X Y y0 ≫ snd X Y = toUnit X ≫ y0 := by
  simp [sectionLeft]

@[simp]
lemma sectionRight_fst (x0 : Point X) : sectionRight X Y x0 ≫ fst X Y = toUnit Y ≫ x0 := by
  simp [sectionRight]

@[simp]
lemma sectionRight_snd (x0 : Point X) : sectionRight X Y x0 ≫ snd X Y = 𝟙 Y := by
  simp [sectionRight]


/-- The map `(x,y) ↦ (x₀,y)` on `X ⊗ Y`, followed by the first projection. -/
@[simp]
lemma snd_sectionRight_fst (x0 : Point X) :
    snd X Y ≫ sectionRight X Y x0 ≫ fst X Y = toUnit (X ⊗ Y) ≫ x0 := by
  simp [sectionRight]

/-- The map `(x,y) ↦ (x₀,y)` on `X ⊗ Y`, followed by the second projection. -/
@[simp]
lemma snd_sectionRight_snd (x0 : Point X) :
    snd X Y ≫ sectionRight X Y x0 ≫ snd X Y = snd X Y := by
  simp [sectionRight]

/-- The map `(x,y) ↦ (x,y₀)` on `X ⊗ Y`, followed by the first projection. -/
@[simp]
lemma fst_sectionLeft_fst (y0 : Point Y) :
    fst X Y ≫ sectionLeft X Y y0 ≫ fst X Y = fst X Y := by
  simp [sectionLeft]

/-- The map `(x,y) ↦ (x,y₀)` on `X ⊗ Y`, followed by the second projection. -/
@[simp]
lemma fst_sectionLeft_snd (y0 : Point Y) :
    fst X Y ≫ sectionLeft X Y y0 ≫ snd X Y = toUnit (X ⊗ Y) ≫ y0 := by
  simp [sectionLeft]

/-- The `k`-point `(x, y)` of `X ⊗ Y` associated to a pair of points. -/
noncomputable def pointProd (x : Point X) (y : Point Y) : Point (X ⊗ Y) := lift x y

@[simp]
lemma pointProd_fst (x : Point X) (y : Point Y) : pointProd X Y x y ≫ fst X Y = x := by
  simp [pointProd]

@[simp]
lemma pointProd_snd (x : Point X) (y : Point Y) : pointProd X Y x y ≫ snd X Y = y := by
  simp [pointProd]

end Sections

section Lift

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K]

/-- The structure morphism `Spec K ⟶ Spec k` of a field extension. -/
noncomputable def specMapOfAlgebra : Spec (.of K) ⟶ Spec (.of k') :=
  Spec.map (CommRingCat.ofHom (algebraMap k' K))

end Lift

end Work.AbVar
