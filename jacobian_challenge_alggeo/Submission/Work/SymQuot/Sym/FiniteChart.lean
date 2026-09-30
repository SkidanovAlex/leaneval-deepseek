/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The chart map `U ⟶ Spec Γ(X,U)^G` is finite (area SY)

For a `K`-scheme `X` whose structure morphism is locally of finite type, an action of a finite
group `G` on `X` by `K`-automorphisms and a `G`-invariant *affine* open subscheme `U ⊆ X`, the
local model of the quotient `X/G` at `U` — the chart map

`A.chartMap U hU : U.toScheme ⟶ Spec Γ(X,U)^G`

— is a **finite** morphism.  This is the local input for the finiteness of the quotient map
`X ⟶ X/G` (`Work.SymQuot.Chart.isFinite_quotientMap`).

The proof is a commutative-algebra statement in commutative algebra dressed as geometry:

* the ring `B = Γ(X,U)` of sections over the affine open `U` is a finitely generated algebra over
  `A₀ = Γ(Spec K, ⊤)` — this is `LocallyOfFiniteType.finiteType_appLE` applied to `X.hom`;
* the action of `G` on `B` is by `A₀`-algebra automorphisms
  (`sectionHom_appLE_hom`: the action fixes the image of `X.hom.appLE`);
* the ring `B` of a finite group action is integral over its invariants `B^G`
  (`Work.SymQuot.Invariants.fixedPoints_isIntegral`), and since it is a finitely generated
  `B^G`-algebra it is a *finite* `B^G`-module — this is the content of
  `ringHom_finite_subtype_fixedPoints`.

Consequently the ring map `B^G → B` is finite, and so is `Spec.map` of it, hence the chart map.
-/
import Mathlib
import Submission.Work.SymQuot.Sym
import Submission.Work.SymQuot.Chart
import Submission.Work.SymQuot.Sections
import Submission.Work.SymQuot.Invariants.fixedPoints_isIntegral
import Submission.Work.SymQuot.Invariants.finiteType_fixedPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot.Sym

/-- **Finiteness of a ring over its invariants.**  Let a finite group `G` act on a commutative
ring `B` by `A`-algebra automorphisms (expressed by the hypothesis `SMulCommClass G A B`, i.e.
that `A → B` lands in the fixed points of `G`) and suppose that `B` is a finitely generated
`A`-algebra.  Then `B` is a *finite* `B^G`-module: the inclusion `B^G ↪ B` is a finite ring map.

Since `B` is integral over `B^G` and is generated as a `B^G`-algebra by generators over `A`
(which lie in the image of `A → B ⊆ B^G`), this is the classical "integral + finitely generated
⟹ finite" statement. -/
theorem ringHom_finite_subtype_fixedPoints {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.FiniteType A B] :
    RingHom.Finite (Subring.subtype (FixedPoints.subring B G)) := by
  -- the image of `A` lies in the fixed points, by `SMulCommClass`
  have hmem : ∀ k : A, algebraMap A B k ∈ FixedPoints.subring B G := by
    intro k
    change algebraMap A B k ∈ FixedPoints.submonoid G B
    rw [FixedPoints.mem_submonoid]
    intro g
    have h1 : algebraMap A B k = k • (1 : B) := Algebra.algebraMap_eq_smul_one k
    rw [h1, smul_comm g k (1 : B), smul_one, ← h1]
  letI : Algebra A ↥(FixedPoints.subring B G) :=
    ((algebraMap A B).codRestrict (FixedPoints.subring B G) hmem).toAlgebra
  haveI hTower : IsScalarTower A ↥(FixedPoints.subring B G) B :=
    IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI hft : Algebra.FiniteType ↥(FixedPoints.subring B G) B :=
    Algebra.FiniteType.of_restrictScalars_finiteType A ↥(FixedPoints.subring B G) B
  haveI hInt : Algebra.IsIntegral ↥(FixedPoints.subring B G) B :=
    Algebra.IsInvariant.isIntegral ↥(FixedPoints.subring B G) B G
  haveI hFin : Module.Finite ↥(FixedPoints.subring B G) B := Algebra.IsIntegral.finite
  exact (RingHom.finite_algebraMap).mpr hFin

/-- **The action of `G` fixes the sections coming from the base.**  If a group acts on the
`K`-scheme `X` by `K`-automorphisms (`hA`), then on the sections over a `G`-invariant open `U`
the induced action (`A.sectionHom U hU g`) fixes every section in the image of the structure
morphism `Γ(Spec K, ⊤) ⟶ Γ(X, U)`.

Equivalently: the square

```
Γ(Spec K,⊤) --X.hom.appLE--> Γ(X,U)
      |                          |
   (identity)              A.sectionHom g
      v                          v
Γ(Spec K,⊤) --X.hom.appLE--> Γ(X,U)
```

commutes.  Here `sectionHom` is *pullback* along `A.hom g`, so the statement is that the pullback
of a section of the base along `X.hom` is unchanged by the action; this is exactly
`A.hom g ≫ X.hom = X.hom` plus the invariance of `U`. -/
theorem sectionHom_appLE_cat {K : Type u} [Field K] (X : Work.GCBasics.Sch K)
    {G : Type u} [Group G] (A : Work.SymQuot.GAction G X.left)
    (hA : ∀ g : G, A.hom g ≫ X.hom = X.hom)
    (U : X.left.Opens) (hUinv : A.IsInvariantOpen U) (g : G) :
    X.hom.appLE ⊤ U (le_top : U ≤ X.hom ⁻¹ᵁ ⊤) ≫
        (A.hom g).appLE U U (le_of_eq (hUinv g).symm)
      = X.hom.appLE ⊤ U (le_top : U ≤ X.hom ⁻¹ᵁ ⊤) := by
  -- (c) `X.hom.appLE ⊤ U = X.hom.appLE ⊤ ⊤ ≫ res`: restrict the *target* open
  have hc := Scheme.Hom.appLE_map (f := X.hom) (U := (⊤ : (Spec (CommRingCat.of K)).Opens))
      (V := (⊤ : X.left.Opens)) (V' := U)
      (e := (le_top : (⊤ : X.left.Opens) ≤ X.hom ⁻¹ᵁ ⊤))
      (i := (homOfLE (le_top : U ≤ (⊤ : X.left.Opens))).op)
  -- (b) `X.hom.appLE ⊤ U = (A.hom g).appLE U U ≫ res'`: restrict the *source* open
  have hb := Scheme.Hom.map_appLE (f := A.hom g) (U := U) (U' := (⊤ : X.left.Opens))
      (V := U) (e := le_of_eq (hUinv g).symm)
      (i := (homOfLE (le_top : U ≤ (⊤ : X.left.Opens))).op)
  -- (a) functoriality of `appLE` for the composite `A.hom g ≫ X.hom = X.hom`
  have hl := Scheme.Hom.appLE_comp_appLE (f := A.hom g) (g := X.hom)
      (U := (⊤ : (Spec (CommRingCat.of K)).Opens)) (V := (⊤ : X.left.Opens)) (W := U)
      (e₁ := (le_top : (⊤ : X.left.Opens) ≤ X.hom ⁻¹ᵁ ⊤))
      (e₂ := (le_top : U ≤ (A.hom g) ⁻¹ᵁ ⊤))
  rw [← hc, Category.assoc, hb, hl, Work.SymQuot.appLE_congr_hom (hA g), hc]

/-- The ring-hom formulation of `sectionHom_appLE_cat`. -/
theorem sectionHom_appLE_hom {K : Type u} [Field K] (X : Work.GCBasics.Sch K)
    {G : Type u} [Group G] (A : Work.SymQuot.GAction G X.left)
    (hA : ∀ g : G, A.hom g ≫ X.hom = X.hom)
    (U : X.left.Opens) (hUinv : A.IsInvariantOpen U) (g : G) :
    (A.sectionHom U hUinv g).comp ((X.hom.appLE ⊤ U (le_top : U ≤ X.hom ⁻¹ᵁ ⊤)).hom)
      = (X.hom.appLE ⊤ U (le_top : U ≤ X.hom ⁻¹ᵁ ⊤)).hom :=
  congrArg CommRingCat.Hom.hom (sectionHom_appLE_cat X A hA U hUinv g)

/-- **The invariant subring of the sections over an affine invariant open is finite.**  Let `X` be
a `K`-scheme locally of finite type over `K`, let a finite group `G` act on `X` by
`K`-automorphisms (`hA`) and let `U ⊆ X` be a `G`-invariant affine open.  Then the ring
`Γ(X,U)` of sections is a finite module over its subring `Γ(X,U)^G` of `G`-invariants. -/
theorem ringHom_finite_subtype_invariants {K : Type u} [Field K] (X : Work.GCBasics.Sch K)
    [LocallyOfFiniteType X.hom] {G : Type u} [Group G] [Fintype G]
    (A : Work.SymQuot.GAction G X.left) (hA : ∀ g : G, A.hom g ≫ X.hom = X.hom)
    {U : X.left.Opens} (hUaff : IsAffineOpen U) (hUinv : A.IsInvariantOpen U) :
    RingHom.Finite (Subring.subtype (A.invariants U hUinv)) := by
  classical
  letI : MulSemiringAction G Γ(X.left, U) := A.sectionMulSemiringAction U hUinv
  -- the `G`-action fixes the sections coming from the base ring `Γ(Spec K, ⊤)`
  have key : ∀ (g : G) (a : Γ(Spec (CommRingCat.of K), ⊤)),
      A.sectionHom U hUinv g (X.hom.appLE ⊤ U (le_top : U ≤ X.hom ⁻¹ᵁ ⊤) a)
        = X.hom.appLE ⊤ U (le_top : U ≤ X.hom ⁻¹ᵁ ⊤) a :=
    fun g a => RingHom.congr_fun (sectionHom_appLE_hom X A hA U hUinv g) a
  letI : Algebra Γ(Spec (CommRingCat.of K), ⊤) Γ(X.left, U) :=
    (X.hom.appLE ⊤ U (le_top : U ≤ X.hom ⁻¹ᵁ ⊤)).hom.toAlgebra
  haveI hft : Algebra.FiniteType Γ(Spec (CommRingCat.of K), ⊤) Γ(X.left, U) :=
    RingHom.finiteType_algebraMap.mpr
      (X.hom.finiteType_appLE (isAffineOpen_top _) hUaff (le_top : U ≤ X.hom ⁻¹ᵁ ⊤))
  haveI hsc : SMulCommClass G Γ(Spec (CommRingCat.of K), ⊤) Γ(X.left, U) :=
    ⟨fun g a b => by
      show A.sectionHom U hUinv g⁻¹ (a • b) = a • (A.sectionHom U hUinv g⁻¹ b)
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      congr 1
      exact key g⁻¹ a⟩
  exact ringHom_finite_subtype_fixedPoints (G := G) (A := Γ(Spec (CommRingCat.of K), ⊤))
    (B := Γ(X.left, U))

/-- **The chart map is finite.**  For an affine `G`-invariant open `U` of a `K`-scheme `X`
locally of finite type over `K`, with `G` a finite group acting by `K`-automorphisms, the
local model `A.chartMap U hU : U.toScheme ⟶ Spec Γ(X,U)^G` of the quotient is a finite
morphism (its ring map is `Γ(X,U)^G ↪ Γ(X,U)`, a finite ring map by
`ringHom_finite_subtype_invariants`). -/
theorem isFinite_chartMap {K : Type u} [Field K] (X : Work.GCBasics.Sch K)
    [LocallyOfFiniteType X.hom] {G : Type u} [Group G] [Fintype G]
    (A : Work.SymQuot.GAction G X.left) (hA : ∀ g : G, A.hom g ≫ X.hom = X.hom)
    {U : X.left.Opens} (hUaff : IsAffineOpen U) (hUinv : A.IsInvariantOpen U) :
    IsFinite (A.chartMap U hUinv) := by
  show IsFinite (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Subring.subtype
    (letI : MulSemiringAction G Γ(X.left, U) := A.sectionMulSemiringAction U hUinv
    FixedPoints.subring Γ(X.left, U) G))))
  haveI hsub : IsFinite (Spec.map (CommRingCat.ofHom (Subring.subtype (A.invariants U hUinv)))) := by
    rw [IsFinite.SpecMap_iff]
    exact ringHom_finite_subtype_invariants X A hA hUaff hUinv
  haveI : IsIso U.toSpecΓ := by rw [← hUaff.isoSpec_hom]; infer_instance
  infer_instance

end Work.SymQuot.Sym
