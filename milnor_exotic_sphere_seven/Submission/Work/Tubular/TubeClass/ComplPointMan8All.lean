import Submission.Work.Tubular.TubeClass.ComplPointMan8
import Submission.Work.Cohomology.relChains_vanishing_of_compact
import Submission.Work.Cohomology.relChains_empty_homology_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# `H_m` of a closed `8`-manifold and of the complement of a point, above the dimension

Two vanishing statements for a closed smooth `8`-manifold `V` (`Work.ThomBordism.Man8`):

* `Work.Tubular.TubeClass.isZero_homology_man8_high`: `H_m(V) = 0` for `m > 8`.  This is Hatcher's
  Lemma 3.27 (b) for the compact set `A = V` (`Work.Cohomology.relChains_vanishing_of_compact`),
  which gives `H_m(V, V∖V) = 0`, together with `H_m(V,∅) ≅ H_m(V)`
  (`Work.Cohomology.relChains_empty_homology_iso`).

* `Work.Tubular.TubeClass.isZero_homology_compl_point_man8_all`: `H_m(V ∖ {v₀}) = 0` for `m ≥ 8`.
  This is the combination of the two neighbouring cases: `m = 8` is
  `Work.Tubular.TubeClass.isZero_homology_compl_point_man8` (the *given* fundamental class), and
  `m > 8` follows from the long exact sequence of the pair `(V, V∖{v₀})`, whose outer terms
  `H_{m+1}(V, V∖{v₀})` and `H_m(V)` vanish above the dimension: the connecting map
  `H_{m+1}(V, V∖{v₀}) ⟶ H_m(V∖{v₀})` is zero while `H_m(V∖{v₀}) ⟶ H_m(V)` is injective.
-/

open CategoryTheory Limits
open scoped Topology

namespace Work.Tubular.TubeClass

noncomputable section

open Work.Cohomology

/-- **A closed `8`-manifold has no homology above degree `8`** (Hatcher 3.27 (b) with `A = V`). -/
theorem isZero_homology_man8_high (V : Work.ThomBordism.Man8) (m : ℕ) (hm : 8 < m) :
    IsZero ((singularChains ℤ (TopCat.of V.pt)).homology m) := by
  have h := relChains_vanishing_of_compact (n := 8) (by norm_num)
    (Set.univ : Set (TopCat.of V.pt)) isCompact_univ m hm
  rw [Set.compl_univ] at h
  haveI := relChains_empty_homology_iso (TopCat.of V.pt) m
  exact IsZero.of_iso h (asIso (HomologicalComplex.homologyMap
    (CategoryTheory.Limits.cokernel.π (inclChains (TopCat.of V.pt) ∅)) m))

/-- **The complement of a point in a connected `8`-manifold has no homology above degree `8`**:
`H_m(V ∖ {v₀}) = 0` for every `m ≥ 8`. -/
theorem isZero_homology_compl_point_man8_all (V : Work.ThomBordism.Man8) [ConnectedSpace V.pt]
    (v₀ : V.pt) (m : ℕ) (hm : 8 ≤ m) :
    IsZero ((singularChains ℤ (TopCat.of {y : V.pt | y ≠ v₀})).homology m) := by
  rcases eq_or_lt_of_le hm with h8 | h8
  · subst h8
    exact isZero_homology_compl_point_man8 V v₀
  · set X : TopCat := TopCat.of V.pt with hX
    set A : Set X := {y | y ≠ v₀} with hA
    have h1 : IsZero ((relChains X A).homology (m + 1)) := by
      have h := relChains_vanishing_of_compact (n := 8) (by norm_num) ({v₀} : Set X)
        isCompact_singleton (m + 1) (by omega)
      rwa [Set.compl_singleton_eq] at h
    have h2 : IsZero ((singularChains ℤ X).homology m) := isZero_homology_man8_high V m h8
    have hf : hPairδ X A m = 0 := IsZero.eq_zero_of_src h1 _
    have hrange : (ModuleCat.Hom.hom (hPairδ X A m)).range = ⊥ := by
      rw [hf]; exact LinearMap.range_zero
    have hinj : Function.Injective
        ⇑(ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains X A) m)) := by
      have hker : (ModuleCat.Hom.hom
          (HomologicalComplex.homologyMap (inclChains X A) m)).ker = ⊥ := by
        rw [← (hPair_exact₁ X A m).moduleCat_range_eq_ker, hrange]
      exact LinearMap.ker_eq_bot.mp hker
    haveI : Subsingleton ↥((singularChains ℤ X).homology m) :=
      ModuleCat.isZero_iff_subsingleton.mp h2
    refine ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => ?_⟩
    have heq : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains X A) m)) a
        = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains X A) m)) b :=
      Subsingleton.elim _ _
    have hz : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains X A) m)) (a - b)
        = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (inclChains X A) m)) 0 := by
      rw [map_sub, heq, sub_self, map_zero]
    exact sub_eq_zero.mp (hinj hz)

end

end Work.Tubular.TubeClass
