import Mathlib
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Homology commutes with finite biproducts of chain complexes

For a finite family `K : ι → ChainComplex (ModuleCat ℤ) ℕ` of chain complexes of
`ℤ`-modules, the `n`-th homology of the degreewise biproduct `⨁ i, K i` is the
biproduct of the `n`-th homologies:

`(⨁ i, K i).homology n ≅ ⨁ i, (K i).homology n`.

As in the binary case (`Work.Homology.HomologyBiprod`), the isomorphism is built
from the maps induced in homology by the structure maps of the biproduct of
complexes: `a i = homologyMap (biproduct.π K i) n` and
`c i = homologyMap (biproduct.ι K i) n`.  The two composites are
`biproduct.lift a ≫ biproduct.desc c` and `biproduct.desc c ≫ biproduct.lift a`:

* the first is `∑ i, a i ≫ c i = ∑ i, homologyMap (π i ≫ ι i) n`, which is the
  `homologyMap` of `∑ i, π i ≫ ι i = 𝟙` by additivity of `homologyMap` over
  finite sums;
* the second is computed on the components of the biproduct, using
  `c k ≫ a j = homologyMap (ι k ≫ π j) n = (ι k ≫ π j)`, the "delta" identity.

The first identity is obtained from Mathlib's `biproduct.lift_desc`, which is
stated in `Mathlib.CategoryTheory.Preadditive.Biproducts` only for an index type
`J : Type` (i.e. in universe `0`).  Since the present statement is
universe-polymorphic in `ι`, the few lemmas needed are re-proved here for an
arbitrary index universe `J : Type w`; their proofs are the proofs of the Mathlib
counterparts
(`biproduct.lift_eq`, `biproduct.desc_eq`, `biproduct.lift_desc`,
`biproduct.total`), which are universe-polymorphic in the ingredients they use.
-/

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex

namespace Work.Homology

noncomputable section

/-! ## Universe-polymorphic biproduct calculus

The following four lemmas are the universe-polymorphic versions of
`biproduct.lift_eq`, `biproduct.desc_eq`, `biproduct.lift_desc` and
`biproduct.total`. -/

/-- `biproduct.lift g` is the sum of the maps `g j` followed by the inclusions. -/
theorem biproduct_lift_eq' {C : Type u} [Category.{v} C] [Preadditive C] {J : Type w} [Fintype J]
    {f : J → C} [HasBiproduct f] {T : C} {g : ∀ j, T ⟶ f j} :
    biproduct.lift g = ∑ j, g j ≫ biproduct.ι f j := by
  classical
  ext j
  simp only [Preadditive.sum_comp, biproduct.ι_π, comp_dite, biproduct.lift_π, Category.assoc,
    comp_zero, Finset.sum_dite_eq', Finset.mem_univ, eqToHom_refl, Category.comp_id, ite_true]

/-- `biproduct.desc g` is the sum of the projections followed by the maps `g j`. -/
theorem biproduct_desc_eq' {C : Type u} [Category.{v} C] [Preadditive C] {J : Type w} [Fintype J]
    {f : J → C} [HasBiproduct f] {T : C} {g : ∀ j, f j ⟶ T} :
    biproduct.desc g = ∑ j, biproduct.π f j ≫ g j := by
  classical
  ext j
  simp [Preadditive.comp_sum, biproduct.ι_π_assoc, dite_comp]

/-- The composite `biproduct.lift g ≫ biproduct.desc h` is the sum
`∑ j, g j ≫ h j`. -/
theorem biproduct_lift_desc' {C : Type u} [Category.{v} C] [Preadditive C] {J : Type w} [Fintype J]
    {f : J → C} [HasBiproduct f] {T U : C} (g : ∀ j, T ⟶ f j) (h : ∀ j, f j ⟶ U) :
    biproduct.lift g ≫ biproduct.desc h = ∑ j, g j ≫ h j := by
  classical
  simp [biproduct_lift_eq', biproduct_desc_eq', Preadditive.comp_sum, Preadditive.sum_comp,
    biproduct.ι_π_assoc, comp_dite, dite_comp]

/-- The total identity for a biproduct: `∑ j, π j ≫ ι j = 𝟙 (⨁ f)`. -/
theorem biproduct_total' {C : Type u} [Category.{v} C] [Preadditive C] {J : Type w} [Fintype J]
    {f : J → C} [HasBiproduct f] :
    ∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f) :=
  IsBilimit.total (biproduct.isBilimit f)

/-- `homologyMap` is additive over finite sums of chain maps. -/
lemma homologyMap_sum {K L : ChainComplex (ModuleCat ℤ) ℕ} (n : ℕ) {ι : Type*} (s : Finset ι)
    (f : ι → (K ⟶ L)) :
    homologyMap (∑ i ∈ s, f i) n = ∑ i ∈ s, homologyMap (f i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [homologyMap_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, homologyMap_add, ih]

/-! ## The main theorem -/

/-- **Homology commutes with finite biproducts of chain complexes.** -/
theorem FiniteBiprodHomology {ι : Type*} [Fintype ι]
    (K : ι → ChainComplex (ModuleCat ℤ) ℕ) [CategoryTheory.Limits.HasBiproduct K] (n : ℕ) :
    Nonempty ((CategoryTheory.Limits.biproduct K).homology n ≅
      CategoryTheory.Limits.biproduct (fun i => (K i).homology n)) := by
  classical
  let Z := (biproduct K).homology n
  let H : ι → ModuleCat ℤ := fun i => (K i).homology n
  let a : ∀ i, Z ⟶ H i := fun i => homologyMap (biproduct.π K i) n
  let c : ∀ i, H i ⟶ Z := fun i => homologyMap (biproduct.ι K i) n
  -- The "matrix" identity `c k ≫ a j = ι k ≫ π j` of the two families of maps.
  have hdelta : ∀ k j, c k ≫ a j = biproduct.ι H k ≫ biproduct.π H j := by
    intro k j
    simp only [a, c, ← homologyMap_comp]
    by_cases h : k = j
    · subst h
      rw [biproduct.ι_π_self K k, biproduct.ι_π_self H k, homologyMap_id]
    · rw [biproduct.ι_π_ne K h, homologyMap_zero, biproduct.ι_π_ne H h]
  -- `c k` is a section of `biproduct.lift a` up to the projection `π k`.
  have hck : ∀ k, c k ≫ biproduct.lift a = biproduct.ι H k := by
    intro k
    apply biproduct.hom_ext
    intro j
    rw [Category.assoc, biproduct.lift_π]
    exact hdelta k j
  -- `biproduct.lift a` followed by `biproduct.desc c` is the identity: this is the
  -- `homologyMap` of the total identity, by additivity of `homologyMap` over sums.
  have key : biproduct.lift a ≫ biproduct.desc c = 𝟙 Z := by
    rw [biproduct_lift_desc' (f := H) a c]
    calc ∑ i, a i ≫ c i
        = ∑ i, homologyMap (biproduct.π K i ≫ biproduct.ι K i) n := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [a, c, ← homologyMap_comp]
      _ = homologyMap (∑ i, (biproduct.π K i ≫ biproduct.ι K i)) n :=
          (homologyMap_sum n Finset.univ _).symm
      _ = homologyMap (𝟙 (biproduct K)) n := by rw [biproduct_total']
      _ = 𝟙 Z := by rw [homologyMap_id]
  -- The other composite, computed on components.
  have hdesc : biproduct.desc c ≫ biproduct.lift a = 𝟙 (biproduct H) := by
    apply biproduct.hom_ext'
    intro k
    rw [← Category.assoc, biproduct.ι_desc, Category.comp_id]
    exact hck k
  refine ⟨?_⟩
  exact { hom := biproduct.lift a, inv := biproduct.desc c, hom_inv_id := key, inv_hom_id := hdesc }

end

end Work.Homology
