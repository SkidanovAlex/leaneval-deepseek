import Mathlib
import Submission.Work.Serre.CWModel.Maps
import Submission.Work.StemsB.SerreExact
import Submission.Work.Cohomology.relChainsMapOf_comp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.Assembly

/-!
# The pullback square of pair maps

The map of pairs `(X, q⁻¹{γ₀}) → (B, {b₀})` induced by the composite `p ∘ pullbackSnd` of the
pullback square

```
  X = Γ ×_B E --pullbackSnd--> E
    |                             |
 pullbackFst                       p
    v                             v
    Γ ------------ g -----------> B
```

can be computed in the two ways of the square: the relation
`pullbackPairMap ≫ relPairMap = stagePairMap ≫ pairMapOf` holds on relative singular chains,
because the two underlying maps of pairs are the *same* map of pairs (the composite `X → B`, with
the same underlying map on the subspaces `q⁻¹{γ₀} → {b₀}`, the constant one).

Both sides are `relChainsMapOf` of the composite pair map, so the statement follows from the
functoriality `Work.Cohomology.relChainsMapOf_comp` of `relChainsMapOf`, the definitional
descriptions of the three maps, and the commutativity of the square.

The whole content is therefore: `relChainsMapOf` is functorial in the map of pairs, and the two
composites of the square coincide as maps of pairs.
-/

section Maps

variable {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B] [TopologicalSpace E]

/-- The map on the point subspaces used in `Work.Serre.CWModel.pairMapOf`: the constant map
`{γ₀} → {b₀}`. -/
def pointMapOf (γ₀ : Γ) (b₀ : B) :
    TopCat.of ({γ₀} : Set Γ) ⟶ TopCat.of ({b₀} : Set B) :=
  TopCat.ofHom ⟨fun _ => ⟨b₀, rfl⟩, continuous_const⟩

/-- The map on the fibres used in `Work.Serre.CWModel.stagePairMap`: the first projection
`q⁻¹{γ₀} → {γ₀}` of the pullback square, on the subspaces (the constant map). -/
def stageFibreMap (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) :
    TopCat.of ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) ⟶ TopCat.of ({γ₀} : Set Γ) :=
  TopCat.ofHom ⟨fun x => ⟨Work.StemsB.pullbackFst g p x.1, x.2⟩,
    Continuous.subtype_mk
      ((Work.StemsB.pullbackFst g p).continuous.comp continuous_subtype_val)
      (fun x => x.2)⟩

/-- The map on the fibres used in `Work.Serre.CWModel.pullbackPairMap`: the second projection
`q⁻¹{γ₀} → p⁻¹{b₀}` of the pullback square, on the subspaces. -/
def pullbackFibreMap (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) (b₀ : B) (hbase : g γ₀ = b₀) :
    TopCat.of ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) ⟶
      TopCat.of (p ⁻¹' ({b₀} : Set B)) :=
  TopCat.ofHom ⟨
    (fun x : ↥((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) =>
      ⟨Work.StemsB.pullbackSnd g p x.1, by
        have hx : x.1.1.1 = γ₀ := x.2
        calc p (x.1.1.2) = g (x.1.1.1) := x.1.2.symm
          _ = g γ₀ := by rw [hx]
          _ = b₀ := hbase⟩),
    Continuous.subtype_mk
      ((Work.StemsB.pullbackSnd g p).continuous.comp continuous_subtype_val)
      (fun x => by
        have hx : x.1.1.1 = γ₀ := x.2
        calc p (x.1.1.2) = g (x.1.1.1) := x.1.2.symm
          _ = g γ₀ := by rw [hx]
          _ = b₀ := hbase)⟩

end Maps

section Defs

variable {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B] [TopologicalSpace E]

/-- **`pullbackPairMap` as the relative chain map of the pullback pair map**, definitionally. -/
lemma pullbackPairMap_eq (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) (b₀ : B) (hbase : g γ₀ = b₀) :
    Work.Serre.CWModel.pullbackPairMap g p γ₀ b₀ hbase =
      Work.Cohomology.relChainsMapOf (TopCat.of (Work.StemsB.Pullback g p)) (TopCat.of E)
        ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) (p ⁻¹' ({b₀} : Set B))
        (TopCat.ofHom (Work.StemsB.pullbackSnd g p)) (pullbackFibreMap g p γ₀ b₀ hbase)
        (by ext x; rfl) := rfl

/-- **`relPairMap` as the relative chain map of the map of pairs `(E, p⁻¹{b₀}) → (B, {b₀})`**,
definitionally. -/
lemma relPairMap_eq (p : C(E, B)) (b₀ : B) :
    Work.StemsB.relPairMap p b₀ =
      Work.Cohomology.relChainsMapOf (TopCat.of E) (TopCat.of B) (p ⁻¹' ({b₀} : Set B))
        ({b₀} : Set B) (TopCat.ofHom p) (Work.StemsB.fibreMap p b₀)
        (by ext x; exact x.2) := rfl

/-- **`stagePairMap` as the relative chain map of the first projection**, definitionally. -/
lemma stagePairMap_eq (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) :
    Work.Serre.CWModel.stagePairMap g p γ₀ =
      Work.Cohomology.relChainsMapOf (TopCat.of (Work.StemsB.Pullback g p)) (TopCat.of Γ)
        ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) ({γ₀} : Set Γ)
        (TopCat.ofHom (Work.StemsB.pullbackFst g p)) (stageFibreMap g p γ₀)
        (by ext x; rfl) := rfl

/-- **`pairMapOf` as the relative chain map of `g`**, definitionally. -/
lemma pairMapOf_eq (g : C(Γ, B)) (γ₀ : Γ) (b₀ : B) (hbase : g γ₀ = b₀) :
    Work.Serre.CWModel.pairMapOf g γ₀ b₀ hbase =
      Work.Cohomology.relChainsMapOf (TopCat.of Γ) (TopCat.of B) ({γ₀} : Set Γ) ({b₀} : Set B)
        (TopCat.ofHom g) (pointMapOf γ₀ b₀)
        (by ext x; exact (congrArg g x.2).trans hbase) := rfl

/-- **`relChainsMapOf` only depends on the map of pairs.**  Two maps of pairs with the same
underlying continuous maps (up to propositional equality) induce the same map of relative chain
complexes. -/
lemma relChainsMapOf_congr (X Y : TopCat) (A : Set X) (C : Set Y)
    (f f' : X ⟶ Y) (g g' : TopCat.of A ⟶ TopCat.of C) (hf : f = f') (hg : g = g')
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y C)
    (w' : Work.Cohomology.subtypeIncl X A ≫ f' = g' ≫ Work.Cohomology.subtypeIncl Y C) :
    Work.Cohomology.relChainsMapOf X Y A C f g w
      = Work.Cohomology.relChainsMapOf X Y A C f' g' w' := by
  subst hf
  subst hg
  exact congrArg (fun w => Work.Cohomology.relChainsMapOf X Y A C f g w)
    (Subsingleton.elim w w')

end Defs

section Main

variable {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B] [TopologicalSpace E]

theorem pullbackPairMap_comp {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) (b₀ : B) (hbase : g γ₀ = b₀) :
    CategoryTheory.CategoryStruct.comp (Work.Serre.CWModel.pullbackPairMap g p γ₀ b₀ hbase)
        (Work.StemsB.relPairMap p b₀)
      = CategoryTheory.CategoryStruct.comp (Work.Serre.CWModel.stagePairMap g p γ₀)
        (Work.Serre.CWModel.pairMapOf g γ₀ b₀ hbase) := by
  -- The two composites of the square agree as maps of pairs.
  have hsq : (TopCat.ofHom (Work.StemsB.pullbackSnd g p) ≫ TopCat.ofHom p :
      TopCat.of (Work.StemsB.Pullback g p) ⟶ TopCat.of B)
      = TopCat.ofHom (Work.StemsB.pullbackFst g p) ≫ TopCat.ofHom g := by
    ext x
    exact (x.2).symm
  have hsg : (pullbackFibreMap g p γ₀ b₀ hbase ≫ Work.StemsB.fibreMap p b₀ :
      TopCat.of ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) ⟶
        TopCat.of ({b₀} : Set B))
      = stageFibreMap g p γ₀ ≫ pointMapOf γ₀ b₀ := by
    ext x
    rfl
  -- The compatibility of the two factors with the inclusions of the subspaces.
  have wS : Work.Cohomology.subtypeIncl (TopCat.of (Work.StemsB.Pullback g p))
        ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) ≫
        TopCat.ofHom (Work.StemsB.pullbackSnd g p)
      = pullbackFibreMap g p γ₀ b₀ hbase ≫
        Work.Cohomology.subtypeIncl (TopCat.of E) (p ⁻¹' ({b₀} : Set B)) := by
    ext x; rfl
  have wP : Work.Cohomology.subtypeIncl (TopCat.of E) (p ⁻¹' ({b₀} : Set B)) ≫ TopCat.ofHom p
      = Work.StemsB.fibreMap p b₀ ≫
        Work.Cohomology.subtypeIncl (TopCat.of B) ({b₀} : Set B) := by
    ext x; exact x.2
  have wF : Work.Cohomology.subtypeIncl (TopCat.of (Work.StemsB.Pullback g p))
        ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) ≫
        TopCat.ofHom (Work.StemsB.pullbackFst g p)
      = stageFibreMap g p γ₀ ≫ Work.Cohomology.subtypeIncl (TopCat.of Γ) ({γ₀} : Set Γ) := by
    ext x; rfl
  have wG : Work.Cohomology.subtypeIncl (TopCat.of Γ) ({γ₀} : Set Γ) ≫ TopCat.ofHom g
      = pointMapOf γ₀ b₀ ≫ Work.Cohomology.subtypeIncl (TopCat.of B) ({b₀} : Set B) := by
    ext x; exact (congrArg g x.2).trans hbase
  -- The composites of the two compatibility squares.
  have w1 : Work.Cohomology.subtypeIncl (TopCat.of (Work.StemsB.Pullback g p))
        ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) ≫
        (TopCat.ofHom (Work.StemsB.pullbackSnd g p) ≫ TopCat.ofHom p)
      = (pullbackFibreMap g p γ₀ b₀ hbase ≫ Work.StemsB.fibreMap p b₀) ≫
        Work.Cohomology.subtypeIncl (TopCat.of B) ({b₀} : Set B) := by
    rw [← Category.assoc, wS, Category.assoc, wP, Category.assoc]
  have w2 : Work.Cohomology.subtypeIncl (TopCat.of (Work.StemsB.Pullback g p))
        ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) ≫
        (TopCat.ofHom (Work.StemsB.pullbackFst g p) ≫ TopCat.ofHom g)
      = (stageFibreMap g p γ₀ ≫ pointMapOf γ₀ b₀) ≫
        Work.Cohomology.subtypeIncl (TopCat.of B) ({b₀} : Set B) := by
    rw [← Category.assoc, wF, Category.assoc, wG, Category.assoc]
  have hpairL := Work.Cohomology.relChainsMapOf_comp
    ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) (p ⁻¹' ({b₀} : Set B))
    ({b₀} : Set B) (TopCat.ofHom (Work.StemsB.pullbackSnd g p))
    (pullbackFibreMap g p γ₀ b₀ hbase) wS (TopCat.ofHom p) (Work.StemsB.fibreMap p b₀) wP w1
  have hpairR := Work.Cohomology.relChainsMapOf_comp
    ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) ({γ₀} : Set Γ) ({b₀} : Set B)
    (TopCat.ofHom (Work.StemsB.pullbackFst g p)) (stageFibreMap g p γ₀) wF
    (TopCat.ofHom g) (pointMapOf γ₀ b₀) wG w2
  have hmid := relChainsMapOf_congr (TopCat.of (Work.StemsB.Pullback g p)) (TopCat.of B)
    ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) ({b₀} : Set B)
    _ _ _ _ hsq hsg w1 w2
  calc CategoryTheory.CategoryStruct.comp (Work.Serre.CWModel.pullbackPairMap g p γ₀ b₀ hbase)
        (Work.StemsB.relPairMap p b₀)
      = Work.Cohomology.relChainsMapOf (TopCat.of (Work.StemsB.Pullback g p)) (TopCat.of E)
            ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) (p ⁻¹' ({b₀} : Set B))
            (TopCat.ofHom (Work.StemsB.pullbackSnd g p)) (pullbackFibreMap g p γ₀ b₀ hbase) wS
          ≫ Work.Cohomology.relChainsMapOf (TopCat.of E) (TopCat.of B) (p ⁻¹' ({b₀} : Set B))
            ({b₀} : Set B) (TopCat.ofHom p) (Work.StemsB.fibreMap p b₀) wP := by
        rw [pullbackPairMap_eq, relPairMap_eq]
    _ = Work.Cohomology.relChainsMapOf (TopCat.of (Work.StemsB.Pullback g p)) (TopCat.of B)
            ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) ({b₀} : Set B)
            (TopCat.ofHom (Work.StemsB.pullbackSnd g p) ≫ TopCat.ofHom p)
            (pullbackFibreMap g p γ₀ b₀ hbase ≫ Work.StemsB.fibreMap p b₀) w1 := hpairL
    _ = Work.Cohomology.relChainsMapOf (TopCat.of (Work.StemsB.Pullback g p)) (TopCat.of B)
            ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) ({b₀} : Set B)
            (TopCat.ofHom (Work.StemsB.pullbackFst g p) ≫ TopCat.ofHom g)
            (stageFibreMap g p γ₀ ≫ pointMapOf γ₀ b₀) w2 := hmid
    _ = Work.Cohomology.relChainsMapOf (TopCat.of (Work.StemsB.Pullback g p)) (TopCat.of Γ)
            ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) ({γ₀} : Set Γ)
            (TopCat.ofHom (Work.StemsB.pullbackFst g p)) (stageFibreMap g p γ₀) wF
          ≫ Work.Cohomology.relChainsMapOf (TopCat.of Γ) (TopCat.of B) ({γ₀} : Set Γ)
            ({b₀} : Set B) (TopCat.ofHom g) (pointMapOf γ₀ b₀) wG := hpairR.symm
    _ = CategoryTheory.CategoryStruct.comp (Work.Serre.CWModel.stagePairMap g p γ₀)
        (Work.Serre.CWModel.pairMapOf g γ₀ b₀ hbase) := by
        rw [← stagePairMap_eq, ← pairMapOf_eq]

end Main

end Work.Serre.Assembly
