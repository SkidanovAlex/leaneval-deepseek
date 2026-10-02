import Mathlib
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.homotopyEquiv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative cohomology of a homotopy-equivalent subspace vanishes

If `A ⊆ X` is a subspace and `r : X → A` is a homotopy inverse to the inclusion `A ↪ X` (so that
the pair `(X,A)` is homotopy equivalent, as a pair, to `(A,A)`), then `H^k(X,A;ℤ) = 0` for every
`k` (`Work.Thom.subsingleton_relComplex_of_homotopyRetract`).

The proof uses the long exact cohomology sequence of the pair (`Work.Cohomology.pair_exact₁/₂/₃`).
Since the restriction `H^j(X) ⟶ H^j(A)` is an isomorphism in every degree (homotopy invariance,
`Work.Cohomology.homotopyEquiv`),

* in degree `0`, the exactness at `H^0(X)` makes `H^0(X,A) ⟶ H^0(X)` zero, while this map is a
  monomorphism because the inclusion of relative cochains is injective in degree `0` (and there is
  no differential into degree `0`);
* in positive degree `j + 1`, the exactness at `H^j(A)` makes the connecting map
  `H^j(A) ⟶ H^{j+1}(X,A)` vanish (the preceding restriction being surjective), so that
  `H^{j+1}(X,A) ⟶ H^{j+1}(X)` is injective, and the exactness at `H^{j+1}(X)` makes it zero too.

This module deliberately avoids `Submission.Work.Cohomology.dualZ`; see
`Submission/Work/Thom/CLEAN_TOOLS.md`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Thom

noncomputable section

/-- **The relative cohomology of a homotopy-equivalent subspace vanishes.** -/
theorem subsingleton_relComplex_of_homotopyRetract {X : Type} [TopologicalSpace X] (A : Set X)
    (r : C(X, A))
    (h₁ : ContinuousMap.Homotopic ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)).comp r)
      (ContinuousMap.id X))
    (h₂ : ContinuousMap.Homotopic (r.comp ⟨Subtype.val, continuous_subtype_val⟩)
      (ContinuousMap.id A))
    (k : ℕ) : Subsingleton ((Work.Cohomology.relComplex ℤ (TopCat.of X) A).homology k) := by
  have h1 : TopCat.Homotopy
      (Work.Cohomology.subtypeIncl (TopCat.of X) A ≫ TopCat.ofHom r) (𝟙 (TopCat.of ↥A)) := h₂.some
  have h2 : TopCat.Homotopy
      (TopCat.ofHom r ≫ Work.Cohomology.subtypeIncl (TopCat.of X) A) (𝟙 (TopCat.of X)) := h₁.some
  -- the restriction `H^j(X) ⟶ H^j(A)` is an isomorphism in every degree
  have hiso : ∀ j, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.restr ℤ (TopCat.of X) A) j) := by
    intro j
    have h := Work.Cohomology.homotopyEquiv ℤ (TopCat.of ↥A) (TopCat.of X)
      (Work.Cohomology.subtypeIncl (TopCat.of X) A) (TopCat.ofHom r) h1 h2 j
    exact h
  -- the restriction is therefore injective in degree `k`
  have hker : LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.restr ℤ (TopCat.of X) A) k)) = ⊥ := by
    haveI := hiso k
    exact LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective _).mp (inferInstanceAs (Mono _)))
  -- the image of the inclusion of the relative cohomology is the kernel of the restriction
  have hrange : LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relIncl ℤ (TopCat.of X) A) k))
      = LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.restr ℤ (TopCat.of X) A) k)) :=
    ShortComplex.Exact.moduleCat_range_eq_ker (Work.Cohomology.pair_exact₂ ℤ (TopCat.of X) A k)
  -- hence the inclusion of the relative cohomology is zero
  have hzero : ∀ a : (Work.Cohomology.relComplex ℤ (TopCat.of X) A).homology k,
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relIncl ℤ (TopCat.of X) A) k)) a = 0 := by
    intro a
    exact (Submodule.mem_bot ℤ).mp (by rw [← hker, ← hrange]; exact ⟨a, rfl⟩)
  -- and it is injective, so its source is a subsingleton
  have hinj : Function.Injective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.relIncl ℤ (TopCat.of X) A) k)) := by
    rcases k with _ | j
    · -- degree `0`: there is no differential into degree `0`
      haveI : Mono ((Work.Cohomology.relIncl ℤ (TopCat.of X) A).f 0) := by
        rw [Work.Cohomology.relIncl_f]
        infer_instance
      exact (ModuleCat.mono_iff_injective _).mp
        (HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
          (Work.Cohomology.relIncl ℤ (TopCat.of X) A) 0 (fun i hi => by
            rw [ComplexShape.up_Rel] at hi; omega))
    · -- positive degree: the connecting map out of `H^j(A)` vanishes
      have hδ : Work.Cohomology.pairδ ℤ (TopCat.of X) A j = 0 := by
        have hex := ShortComplex.Exact.moduleCat_range_eq_ker
          (Work.Cohomology.pair_exact₃ ℤ (TopCat.of X) A j)
        change LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (Work.Cohomology.restr ℤ (TopCat.of X) A) j))
          = LinearMap.ker (ModuleCat.Hom.hom (Work.Cohomology.pairδ ℤ (TopCat.of X) A j))
          at hex
        have hsurj : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (Work.Cohomology.restr ℤ (TopCat.of X) A) j)) := by
          haveI := hiso j
          exact (ModuleCat.epi_iff_surjective _).mp (inferInstanceAs (Epi _))
        rw [LinearMap.range_eq_top.mpr hsurj] at hex
        apply ModuleCat.hom_ext
        rw [ModuleCat.hom_zero]
        exact LinearMap.ker_eq_top.mp hex.symm
      have hker' : LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.Cohomology.relIncl ℤ (TopCat.of X) A) (j + 1))) = ⊥ := by
        have hex := ShortComplex.Exact.moduleCat_range_eq_ker
          (Work.Cohomology.pair_exact₁ ℤ (TopCat.of X) A j)
        change LinearMap.range (ModuleCat.Hom.hom (Work.Cohomology.pairδ ℤ (TopCat.of X) A j))
          = LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
            (Work.Cohomology.relIncl ℤ (TopCat.of X) A) (j + 1))) at hex
        rw [hδ, ModuleCat.hom_zero, LinearMap.range_zero] at hex
        exact hex.symm
      exact LinearMap.ker_eq_bot.mp hker'
  exact ⟨fun a b => hinj (by rw [hzero a, hzero b])⟩

end

end Work.Thom
