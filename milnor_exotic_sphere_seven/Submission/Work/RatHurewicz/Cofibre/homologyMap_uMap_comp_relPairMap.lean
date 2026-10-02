import Mathlib
import Submission.Work.RatHurewicz.Cofibre.AssemblyDefs
import Submission.Work.Cohomology.relChainsMapOf_comp

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The square comparing the cover of the cofibre with the pair `(E, p⁻¹(p e₀))`

For a continuous map `p : E → B`, a point `e₀ : E` and the fibre `F = p⁻¹{p e₀}`, the two maps of
pairs

* `(U, U ∩ V) → (E, F) → (B, {p e₀})`  (`uMap` followed by `relPairMap`) and
* `(U, U ∩ V) → (C, V) → (B, {p e₀})`  (the inclusion of pairs followed by `psiMap`),

where `C = cofibre (setIncl F)`, `U = cofibreU (setIncl F)`, `V = cofibreV (setIncl F)` and
`U ∩ V` is modelled by `collarSet`, induce the *same* map on relative homology.  On the nose, both
are induced by the map of pairs sending `z ∈ U` to `p (cofibreURetract z) = cofibreCollapse z` and a
collar point to `b`.

The proof is a chain level computation: both composites are `relChainsMapOf` of the same pair map
(only the first component matters for a `relChainsMapOf`, `cokernel_π_relChainsMapOf`), and the two
first components agree (`p_comp_cofibreURetract`).
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

open Work.RatHurewicz

namespace Work.RatHurewicz.Cofibre

noncomputable section

/-! ## Generalities on `relChainsMapOf` -/

/-- The projection to the relative chain complex commutes with `relChainsMapOf`: a
`relChainsMapOf` is *determined by its first component*. -/
theorem cokernel_π_relChainsMapOf {X Y : TopCat} (A : Set X) (B : Set Y) (f : X ⟶ Y)
    (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B) :
    cokernel.π (Work.Cohomology.inclChains X A) ≫ Work.Cohomology.relChainsMapOf X Y A B f g w
      = Work.Cohomology.chainMap ℤ X Y f ≫ cokernel.π (Work.Cohomology.inclChains Y B) := by
  rw [Work.Cohomology.relChainsMapOf]
  exact Work.Cohomology.cokernel_π_map (Work.Cohomology.inclChains X A)
    (Work.Cohomology.inclChains Y B) (Work.Cohomology.chainMap ℤ (TopCat.of A) (TopCat.of B) g)
    (Work.Cohomology.chainMap ℤ X Y f) _

/-- Two `relChainsMapOf` with the same first component (and arbitrary second components and
compatibility proofs) are equal. -/
theorem relChainsMapOf_eq_of_eq {X Y : TopCat} (A : Set X) (B : Set Y)
    {f₁ f₂ : X ⟶ Y} (hf : f₁ = f₂) {g₁ g₂ : TopCat.of A ⟶ TopCat.of B}
    (w₁ : Work.Cohomology.subtypeIncl X A ≫ f₁ = g₁ ≫ Work.Cohomology.subtypeIncl Y B)
    (w₂ : Work.Cohomology.subtypeIncl X A ≫ f₂ = g₂ ≫ Work.Cohomology.subtypeIncl Y B) :
    Work.Cohomology.relChainsMapOf X Y A B f₁ g₁ w₁
      = Work.Cohomology.relChainsMapOf X Y A B f₂ g₂ w₂ := by
  subst hf
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains X A))).1
  rw [cokernel_π_relChainsMapOf, cokernel_π_relChainsMapOf]

/-- Composition of `relChainsMapOf`, with the compatibility proof of the composite made explicit
(so that it can be used as a rewrite rule). -/
theorem relChainsMapOf_comp' {X Y Z : TopCat} (A : Set X) (B : Set Y) (C : Set Z)
    (f : X ⟶ Y) (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B)
    (f' : Y ⟶ Z) (g' : TopCat.of B ⟶ TopCat.of C)
    (w' : Work.Cohomology.subtypeIncl Y B ≫ f' = g' ≫ Work.Cohomology.subtypeIncl Z C) :
    Work.Cohomology.relChainsMapOf X Y A B f g w ≫ Work.Cohomology.relChainsMapOf Y Z B C f' g' w'
      = Work.Cohomology.relChainsMapOf X Z A C (f ≫ f') (g ≫ g')
          (by
            rw [← Category.assoc, w, Category.assoc, w', ← Category.assoc]) :=
  Work.Cohomology.relChainsMapOf_comp A B C f g w f' g' w' _

/-! ## The collapse of a half-open cone point -/

/-- The collapse of a cone point of height `< 1/2` lands where it should: the value of `p` on the
base of the cone point. -/
theorem p_coneBaseLtHalf {E F B : Type} [TopologicalSpace E] [TopologicalSpace F]
    [TopologicalSpace B] (ι : C(F, E)) (p : C(E, B)) (b : B) (hp : ∀ x, p (ι x) = b)
    (u : ↥(coneLtHalfSet (F := F))) : p (coneBaseLtHalf ι u) = b := by
  obtain ⟨y, hy⟩ := u
  obtain ⟨q, rfl⟩ := Quotient.exists_rep y
  have h := coneBaseLtHalf_coneMk ι q hy
  rw [show (⟨⟦q⟧, hy⟩ : ↥(coneLtHalfSet (F := F))) = ⟨coneMk q, hy⟩ from Subtype.ext rfl, h]
  exact hp q.1

/-- **The retraction `cofibreURetract` computes the collapse `cofibreCollapse` on `U`**: for a point
of the half-open cone `U = {h < 1/2}` of the cofibre of `setIncl F`, pushing it back to `E` and then
applying `p` is the same as collapsing it directly. -/
theorem p_comp_cofibreURetract {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (F : Set E) [Nonempty E] [Nonempty ↥F] (e₀ : E) (p : C(E, B))
    (hp : ∀ y : ↥F, p (setIncl F y) = p e₀) (z : ↥(cofibreU (setIncl F))) :
    p (cofibreURetract (setIncl F) e₀ z)
      = cofibreCollapse (setIncl F) p (p e₀) hp (z : cofibre (setIncl F)) := by
  obtain ⟨q, hq⟩ := z
  obtain ⟨a, rfl⟩ := Quotient.exists_rep q
  rw [cofibreURetract_mk]
  show p (uRetractFun (setIncl F) e₀ a) = cofibreGlue (setIncl F) p (p e₀) a
  cases a with
  | inl x => rfl
  | inr y =>
      rw [mem_cofibreU_iff] at hq
      have hcone : cofibreHeight (setIncl F) (cofibreInclCone (setIncl F) y) < cofibreHalf := hq
      rw [cofibreHeight_cone] at hcone
      show p (if h : coneHeight y < cofibreHalf then
          coneBaseLtHalf (setIncl F) ⟨y, h⟩ else e₀) = p e₀
      rw [dif_pos hcone]
      exact p_coneBaseLtHalf (setIncl F) p (p e₀) hp ⟨y, hcone⟩

/-- **The two pair maps `(U, U ∩ V) → (B, {p e₀})` have the same first component.** -/
theorem uMap_pair_eq {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (F : Set E) [Nonempty E] [Nonempty ↥F] (e₀ : E) (p : C(E, B))
    (hp : ∀ y : ↥F, p (setIncl F y) = p e₀) :
    TopCat.ofHom (cofibreURetract (setIncl F) e₀) ≫ TopCat.ofHom p
      = Work.Cohomology.subtypeIncl (TopCat.of (cofibre (setIncl F))) (cofibreU (setIncl F))
        ≫ TopCat.ofHom (cofibreCollapse (setIncl F) p (p e₀) hp) := by
  apply TopCat.hom_ext
  ext z
  exact p_comp_cofibreURetract F e₀ p hp z

/-! ## The defining maps, unfolded -/

theorem uMap_eq_relChainsMapOf (E : Type) [TopologicalSpace E] (F : Set E) [Nonempty E]
    [Nonempty ↥F] (e₀ : E) :
    uMap F e₀ = Work.Cohomology.relChainsMapOf (TopCat.of ↥(cofibreU (setIncl F))) (TopCat.of E)
      (collarSet (setIncl F)) F (TopCat.ofHom (cofibreURetract (setIncl F) e₀))
      (TopCat.ofHom (collarBase (setIncl F)))
      (by
        ext z
        exact cofibreURetract_eq_collarBase F e₀ z) := rfl

theorem relPairMap_eq_relChainsMapOf {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b : B) :
    Work.StemsB.relPairMap p b = Work.Cohomology.relChainsMapOf (TopCat.of E) (TopCat.of B)
      (p ⁻¹' {b}) ({b} : Set B) (TopCat.ofHom p) (Work.StemsB.fibreMap p b)
      (by
        ext x
        exact x.2) := rfl

theorem relChainsMap_eq_relChainsMapOf (X : TopCat) (U A : Set X) :
    Work.Cohomology.relChainsMap X U A = Work.Cohomology.relChainsMapOf (TopCat.of U) X
      {y : U | (y : X) ∈ A} A (Work.Cohomology.subtypeIncl X U) (Work.Cohomology.inclInterA X U A)
      (by
        ext y
        simp only [Work.Cohomology.subtypeIncl, Work.Cohomology.inclInterA]
        rfl) := rfl

theorem psiMap_eq_relChainsMapOf {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) [Nonempty E] [Nonempty ↥(p ⁻¹' {p e₀})] :
    psiMap (setIncl (p ⁻¹' {p e₀})) (cofibreCollapse (setIncl (p ⁻¹' {p e₀})) p (p e₀) (fun y => y.2))
      (p e₀) (cofibreCollapse_eq_of_mem_cofibreV (setIncl (p ⁻¹' {p e₀})) p (p e₀) (fun y => y.2))
    = Work.Cohomology.relChainsMapOf (TopCat.of (cofibre (setIncl (p ⁻¹' {p e₀})))) (TopCat.of B)
        (cofibreV (setIncl (p ⁻¹' {p e₀}))) ({p e₀} : Set B)
        (TopCat.ofHom (cofibreCollapse (setIncl (p ⁻¹' {p e₀})) p (p e₀) (fun y => y.2)))
        (TopCat.ofHom ⟨fun _ : ↥(cofibreV (setIncl (p ⁻¹' {p e₀}))) => ⟨p e₀, rfl⟩,
          continuous_const⟩)
        (by
          ext z
          exact cofibreCollapse_eq_of_mem_cofibreV (setIncl (p ⁻¹' {p e₀})) p (p e₀)
            (fun y => y.2) z.1 z.2) := rfl

/-! ## The square -/

/-- **The chain level identity** underlying the square: the two composites of pair maps
`(U, U ∩ V) → (B, {p e₀})` are equal. -/
theorem uMap_comp_relPairMap_eq (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : ContinuousMap E B) (e₀ : E) [Nonempty E] [Nonempty (p ⁻¹' {p e₀})] :
    uMap (p ⁻¹' {p e₀}) e₀ ≫ Work.StemsB.relPairMap p (p e₀)
      = Work.Cohomology.relChainsMap (TopCat.of (cofibre (setIncl (p ⁻¹' {p e₀}))))
          (cofibreU (setIncl (p ⁻¹' {p e₀}))) (cofibreV (setIncl (p ⁻¹' {p e₀})))
        ≫ psiMap (setIncl (p ⁻¹' {p e₀}))
            (cofibreCollapse (setIncl (p ⁻¹' {p e₀})) p (p e₀) (fun y => y.2)) (p e₀)
            (cofibreCollapse_eq_of_mem_cofibreV (setIncl (p ⁻¹' {p e₀})) p (p e₀) (fun y => y.2)) := by
  rw [uMap_eq_relChainsMapOf, relPairMap_eq_relChainsMapOf]
  rw [relChainsMap_eq_relChainsMapOf, psiMap_eq_relChainsMapOf]
  rw [relChainsMapOf_comp', relChainsMapOf_comp']
  exact relChainsMapOf_eq_of_eq _ _ (uMap_pair_eq (p ⁻¹' {p e₀}) e₀ p (fun y => y.2)) _ _

/-- **The square commutes on homology**: the composite of the comparison of the cover with the pair
of the fibration and the map of pairs induced by `p` agrees with the composite of the excision
inclusion and the collapse. -/
theorem homologyMap_uMap_comp_relPairMap (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : ContinuousMap E B) (e₀ : E) [Nonempty E] [Nonempty (p ⁻¹' {p e₀})] (i : ℕ) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (Work.RatHurewicz.Cofibre.uMap (p ⁻¹' {p e₀}) e₀) i) (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p (p e₀)) i) = CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap (TopCat.of (Work.RatHurewicz.cofibre (Work.RatHurewicz.setIncl (p ⁻¹' {p e₀})))) (Work.RatHurewicz.cofibreU (Work.RatHurewicz.setIncl (p ⁻¹' {p e₀}))) (Work.RatHurewicz.cofibreV (Work.RatHurewicz.setIncl (p ⁻¹' {p e₀})))) i) (HomologicalComplex.homologyMap (Work.RatHurewicz.Cofibre.psiMap (Work.RatHurewicz.setIncl (p ⁻¹' {p e₀})) (Work.RatHurewicz.cofibreCollapse (Work.RatHurewicz.setIncl (p ⁻¹' {p e₀})) p (p e₀) (fun y => y.2)) (p e₀) (Work.RatHurewicz.Cofibre.cofibreCollapse_eq_of_mem_cofibreV (Work.RatHurewicz.setIncl (p ⁻¹' {p e₀})) p (p e₀) (fun y => y.2))) i) := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun m => HomologicalComplex.homologyMap m i) (uMap_comp_relPairMap_eq E B p e₀)

end

end Work.RatHurewicz.Cofibre
