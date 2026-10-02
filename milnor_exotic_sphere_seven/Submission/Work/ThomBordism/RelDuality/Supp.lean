import Mathlib
import Submission.Work.ThomBordism.RelDuality.Defs
import Submission.Work.ThomBordism.RelDuality.interiorHomology
import Submission.Work.ThomBordism.RelDuality.relClass_lift
import Submission.Work.ThomBordism.RelDuality.goodOfOpen
import Submission.Work.ThomBordism.RelDuality.doubleFundClass
import Submission.Work.ThomBordism.goodUnivCharted
import Submission.Work.ThomBordism.Port.Glue
import Submission.Work.ThomBordism.Port.PdGoodUnivChart
import Submission.Work.ThomBordism.localGenAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Comparing the pair `(M, ∂M)` with the pairs `(M, M∖K)` and with the double

Vocabulary for the proof of `Work.ThomBordism.RelDuality.lefschetzDualityBdry_of_pieces`:

* `bdry9` — the boundary of `M`;
* `suppOf L` — the support in `M` of a subset `L` of the double `D = M ∪_∂M M` (its preimage under
  the first copy);
* `SuppObs K L` — the compatibility condition `M∖K ⊆ D∖L` making the first copy inclusion a map of
  pairs `(M, M∖K) → (D, D∖L)`;
* `suppMap K L h` — the induced map of relative chain complexes;
* `bdryIncl K hK` — the inclusion of relative chain complexes `C_*(M, ∂M) → C_*(M, M∖K)`.

The two technical lemmas are `suppMap_natural` (compatibility of `suppMap` with shrinking the two
supports) and `bdryIncl_singleton_eq_locW` (the local class of `w` at an interior point, in the
`bdryIncl` form).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold Topology

namespace Work.ThomBordism.RelDuality

noncomputable section

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 9) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M] [CompactSpace M] [T2Space M]

/-- The boundary of `M`, as an excluded set. -/
abbrev bdry9 (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 9) M] : Set M :=
  (modelWithCornersEuclideanHalfSpace 9).boundary M

/-- The support in `M` of a subset `L` of the double, i.e. its preimage under the first copy. -/
abbrev suppOf (L : Set (Double 8 M)) : Set M := doubleιM ⁻¹' L

theorem suppOf_intImg : suppOf (M := M) (DoubleFC.intImg 8 M) = DoubleFC.intSet 8 M := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu⟩ := hx
    have hux : u = x := doubleιM_injective hu
    rw [← hux]
    exact u.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem suppOf_mono {L L' : Set (Double 8 M)} (h : L ⊆ L') :
    suppOf (M := M) L ⊆ suppOf (M := M) L' :=
  Set.preimage_mono h

/-- The first copy inclusion, as a morphism of `TopCat`. -/
abbrev dblIota : TopCat.of M ⟶ TopCat.of (Double 8 M) := DoubleFC.iMHom 8 M

/-- The compatibility condition for the first-copy inclusion to induce a map of pairs. -/
abbrev SuppObs (K : Set M) (L : Set (Double 8 M)) : Prop := ∀ x, x ∉ K → doubleιM x ∉ L

/-- The restriction of the first-copy inclusion to the complements of the supports. -/
abbrev suppSubHom (K : Set M) (L : Set (Double 8 M)) (h : SuppObs K L) :
    TopCat.of (Kᶜ : Set M) ⟶ TopCat.of (Lᶜ : Set (Double 8 M)) :=
  TopCat.ofHom ⟨fun z => ⟨doubleιM (z : M), h (z : M) z.2⟩,
    Continuous.subtype_mk ((continuous_doubleιM (n := 8) (M := M)).comp continuous_subtype_val) _⟩

theorem suppSubHom_spec (K : Set M) (L : Set (Double 8 M)) (h : SuppObs K L) :
    Work.Cohomology.subtypeIncl (TopCat.of M) (Kᶜ : Set M) ≫ dblIota (M := M)
      = suppSubHom (M := M) K L h
        ≫ Work.Cohomology.subtypeIncl (TopCat.of (Double 8 M)) (Lᶜ : Set (Double 8 M)) := by
  apply CategoryTheory.ConcreteCategory.hom_ext
  intro z
  rfl

/-- **The map of relative chain complexes** `C_*(M, M∖K) ⟶ C_*(D, D∖L)` induced by the first
copy inclusion. -/
abbrev suppMap (K : Set M) (L : Set (Double 8 M)) (h : SuppObs K L) :
    Work.Cohomology.relChains (TopCat.of M) (Kᶜ : Set M) ⟶
      Work.Cohomology.relChains (TopCat.of (Double 8 M)) (Lᶜ : Set (Double 8 M)) :=
  Work.Cohomology.relChainsMapOf (TopCat.of M) (TopCat.of (Double 8 M))
    (Kᶜ : Set M) (Lᶜ : Set (Double 8 M)) (dblIota (M := M)) (suppSubHom (M := M) K L h)
    (suppSubHom_spec (M := M) K L h)

/-- The singleton case: `suppMap` at `K = {y}`, `L = {doubleιM y}` is `pairMapιM`. -/
theorem suppMap_singleton (y : M) :
    suppMap (M := M) ({y} : Set M) ({doubleιM y} : Set (Double 8 M))
        (by intro x hx hxL; exact hx (by simpa using doubleιM_injective hxL))
      = DoubleFC.pairMapιM 8 M y := by
  unfold suppMap
  refine (cancel_epi (CategoryTheory.Limits.cokernel.π
    (Work.Cohomology.inclChains (TopCat.of M) (({y} : Set M)ᶜ)))).1 ?_
  rw [Work.Cohomology.capRel_cokernel_π_relChainsMapOf, DoubleFC.pairMapιM_π]

/-- **Naturality of `suppMap`** under shrinking the supports. -/
theorem suppMap_natural {K K' : Set M} {L L' : Set (Double 8 M)} (hKK' : K ⊆ K') (hLL' : L ⊆ L')
    (h : SuppObs K L) (h' : SuppObs K' L') :
    suppMap (M := M) K' L' h'
        ≫ Work.Cohomology.relCokerMap (TopCat.of (Double 8 M)) (L'ᶜ) (Lᶜ)
            (fun x hxL' hxL => hxL' (hLL' hxL))
      = Work.Cohomology.relCokerMap (TopCat.of M) (K'ᶜ) (Kᶜ)
            (fun x hxK hxK' => hxK (hKK' hxK')) ≫ suppMap (M := M) K L h := by
  refine (cancel_epi (CategoryTheory.Limits.cokernel.π
    (Work.Cohomology.inclChains (TopCat.of M) (K'ᶜ : Set M)))).1 ?_
  calc CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M) (K'ᶜ : Set M))
        ≫ (suppMap (M := M) K' L' h' ≫ Work.Cohomology.relCokerMap (TopCat.of (Double 8 M))
            (L'ᶜ) (Lᶜ) (fun x hxL' hxL => hxL' (hLL' hxL)))
      = (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M) (K'ᶜ : Set M))
          ≫ suppMap (M := M) K' L' h')
        ≫ Work.Cohomology.relCokerMap (TopCat.of (Double 8 M)) (L'ᶜ) (Lᶜ)
            (fun x hxL' hxL => hxL' (hLL' hxL)) := (Category.assoc _ _ _).symm
    _ = (Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double 8 M))
          (Work.ThomBordism.DoubleFC.iMHom 8 M)
          ≫ CategoryTheory.Limits.cokernel.π
              (Work.Cohomology.inclChains (TopCat.of (Double 8 M)) (L'ᶜ : Set (Double 8 M))))
        ≫ Work.Cohomology.relCokerMap (TopCat.of (Double 8 M)) (L'ᶜ) (Lᶜ)
            (fun x hxL' hxL => hxL' (hLL' hxL)) := by
        rw [Work.Cohomology.capRel_cokernel_π_relChainsMapOf]
    _ = Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double 8 M))
          (Work.ThomBordism.DoubleFC.iMHom 8 M)
        ≫ (CategoryTheory.Limits.cokernel.π
              (Work.Cohomology.inclChains (TopCat.of (Double 8 M)) (L'ᶜ : Set (Double 8 M)))
            ≫ Work.Cohomology.relCokerMap (TopCat.of (Double 8 M)) (L'ᶜ) (Lᶜ)
                (fun x hxL' hxL => hxL' (hLL' hxL))) := (Category.assoc _ _ _).symm
    _ = Work.Cohomology.chainMap ℤ (TopCat.of M) (TopCat.of (Double 8 M))
          (Work.ThomBordism.DoubleFC.iMHom 8 M)
        ≫ CategoryTheory.Limits.cokernel.π
            (Work.Cohomology.inclChains (TopCat.of (Double 8 M)) (Lᶜ : Set (Double 8 M))) := by
        rw [Work.Cohomology.relCokerMap_comp_π]
    _ = CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M) (Kᶜ : Set M))
          ≫ Work.Cohomology.relChainsMapOf (TopCat.of M) (TopCat.of (Double 8 M))
              (Kᶜ : Set M) (Lᶜ : Set (Double 8 M)) (Work.ThomBordism.DoubleFC.iMHom 8 M)
              (suppSubHom (M := M) K L h) (suppSubHom_spec (M := M) K L h) := by
        rw [Work.Cohomology.capRel_cokernel_π_relChainsMapOf]
    _ = CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains (TopCat.of M) (K'ᶜ : Set M))
        ≫ (Work.Cohomology.relCokerMap (TopCat.of M) (K'ᶜ) (Kᶜ)
            (fun x hxK hxK' => hxK (hKK' hxK')) ≫ suppMap (M := M) K L h) := by
        rw [← Category.assoc, Work.Cohomology.relCokerMap_comp_π]

/-! ## Relating the local classes of `w` to the `RelH`-language -/

/-- The inclusion of relative chain complexes `C_*(M, ∂M) ⟶ C_*(M, M∖K)`. -/
abbrev bdryIncl (K : Set M) (hK : K ⊆ (bdry9 M)ᶜ) :
    Work.Cohomology.relChains (TopCat.of M) (bdry9 M) ⟶
      Work.Cohomology.relChains (TopCat.of M) (Kᶜ : Set M) :=
  Work.Cohomology.relCokerMap (TopCat.of M) (bdry9 M) (Kᶜ : Set M)
    (fun x hx hxK => hK hxK hx)

/-- Functoriality of `bdryIncl`. -/
theorem bdryIncl_comp {K K' : Set M} (hK : K ⊆ (bdry9 M)ᶜ) (hK' : K' ⊆ (bdry9 M)ᶜ)
    (hK'K : K' ⊆ K) :
    CategoryTheory.CategoryStruct.comp (bdryIncl (M := M) K hK)
        (Work.Cohomology.relCokerMap (TopCat.of M) (Kᶜ : Set M) (K'ᶜ : Set M)
          (fun x hxK hxK' => hxK (hK'K hxK')))
      = bdryIncl (M := M) K' hK' := by
  unfold bdryIncl
  rw [Work.Cohomology.relCokerMap_comp]

/-- The two spellings of the inclusion of relative chain complexes agree. -/
theorem relChainsIncl_eq_relChainsSubMap (X : TopCat) {A B : Set X} (h : A ⊆ B) :
    Work.ThomBordism.relChainsIncl X h = Work.Cohomology.relChainsSubMap X A B h := by
  apply (cancel_epi (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A))).1
  rw [Work.Cohomology.relChainsSubMap_comp]
  unfold Work.ThomBordism.relChainsIncl
  rw [Work.Cohomology.capRel_cokernel_π_relChainsMapOf, Work.Cohomology.chainMap_id', Category.id_comp]

/-- **The local class of `w` at an interior point, in the `bdryIncl` form.** -/
theorem bdryIncl_singleton_eq_locW
    (w : (Work.Cohomology.relChains (TopCat.of M) (bdry9 M)).homology 9)
    (y : M) (hy : y ∉ bdry9 M) :
    (HomologicalComplex.homologyMap
        (bdryIncl (M := M) ({y} : Set M)
          (by intro z hz hyz; exact hy (Set.mem_singleton_iff.mp hz ▸ hyz))) 9)
      w = RelDoubleClass.locW (n := 8) (M := M) w y hy := by
  have h1 : bdryIncl (M := M) ({y} : Set M)
        (by intro z hz hyz; exact hy (Set.mem_singleton_iff.mp hz ▸ hyz))
      = Work.ThomBordism.relChainsInclPunct (TopCat.of M) (bdry9 M) y hy := by
    unfold bdryIncl Work.ThomBordism.relChainsInclPunct
    rw [← Work.Cohomology.relChainsSubMap_eq_relCokerMap, ← relChainsIncl_eq_relChainsSubMap]
  simp only [RelDoubleClass.locW]
  rw [h1]
  rfl

end

end Work.ThomBordism.RelDuality
