import Mathlib
import Submission.Work.Thom.Cohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

/-- **If the inclusion `A ↪ X` induces an isomorphism on rational cohomology in every degree, then
the relative cohomology `H^k(X,A;ℚ)` vanishes for `k ≥ 1`.**

This is the long exact sequence of the pair `(X,A)`,
`⋯ → H^{k-1}(A) → H^k(X,A) → H^k(X) → H^k(A) → ⋯`:
the restriction `H^k(X) → H^k(A)` being injective makes `H^k(X,A) → H^k(X)` zero, while the
restriction `H^{k-1}(X) → H^{k-1}(A)` being surjective makes the connecting map
`H^{k-1}(A) → H^k(X,A)` vanish, so that `H^k(X,A) → H^k(X)` is also injective — a zero injective map
has a subsingleton source. -/
theorem isZero_relCoh_of_cohMapIso {X : Type} [TopologicalSpace X] (A : Set X) {k : ℕ} (hk : 1 ≤ k)
    (h : ∀ j : ℕ, CategoryTheory.IsIso (Work.Thom.CohMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥A, X)) ℚ j)) :
    CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ k X A) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, (Nat.sub_add_cancel hk).symm⟩
  subst hm
  -- the restriction `H^j(X) → H^j(A)` is an isomorphism in every degree
  have hiso : ∀ j : ℕ, IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.restr ℚ (TopCat.of X) A) j) := fun j => h j
  -- it is therefore injective in degree `m + 1`
  have hker : LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.restr ℚ (TopCat.of X) A) (m + 1))) = ⊥ := by
    haveI := hiso (m + 1)
    exact LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective _).mp (inferInstanceAs (Mono _)))
  -- the image of the inclusion of the relative cohomology is the kernel of the restriction
  have hrange : LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relIncl ℚ (TopCat.of X) A) (m + 1)))
      = LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.restr ℚ (TopCat.of X) A) (m + 1))) :=
    ShortComplex.Exact.moduleCat_range_eq_ker
      (Work.Cohomology.pair_exact₂ ℚ (TopCat.of X) A (m + 1))
  -- hence the inclusion of the relative cohomology is zero
  have hzero : ∀ a : (Work.Cohomology.relComplex ℚ (TopCat.of X) A).homology (m + 1),
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relIncl ℚ (TopCat.of X) A) (m + 1))) a = 0 := by
    intro a
    exact (Submodule.mem_bot ℚ).mp (by rw [← hker, ← hrange]; exact ⟨a, rfl⟩)
  -- the connecting map `H^m(A) → H^{m+1}(X,A)` vanishes, the restriction in degree `m` being
  -- surjective
  have hδ : Work.Cohomology.pairδ ℚ (TopCat.of X) A m = 0 := by
    have hex := ShortComplex.Exact.moduleCat_range_eq_ker
      (Work.Cohomology.pair_exact₃ ℚ (TopCat.of X) A m)
    change LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.restr ℚ (TopCat.of X) A) m))
      = LinearMap.ker (ModuleCat.Hom.hom (Work.Cohomology.pairδ ℚ (TopCat.of X) A m)) at hex
    have hsurj : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.restr ℚ (TopCat.of X) A) m)) := by
      haveI := hiso m
      exact (ModuleCat.epi_iff_surjective _).mp (inferInstanceAs (Epi _))
    rw [LinearMap.range_eq_top.mpr hsurj] at hex
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_zero]
    exact LinearMap.ker_eq_top.mp hex.symm
  -- so the inclusion of the relative cohomology is injective
  have hker' : LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.relIncl ℚ (TopCat.of X) A) (m + 1))) = ⊥ := by
    have hex := ShortComplex.Exact.moduleCat_range_eq_ker
      (Work.Cohomology.pair_exact₁ ℚ (TopCat.of X) A m)
    change LinearMap.range (ModuleCat.Hom.hom (Work.Cohomology.pairδ ℚ (TopCat.of X) A m))
      = LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relIncl ℚ (TopCat.of X) A) (m + 1))) at hex
    rw [hδ, ModuleCat.hom_zero, LinearMap.range_zero] at hex
    exact hex.symm
  have hinj : Function.Injective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.relIncl ℚ (TopCat.of X) A) (m + 1))) :=
    LinearMap.ker_eq_bot.mp hker'
  haveI : Subsingleton (Work.Thom.RelCoh ℚ (m + 1) X A) :=
    ⟨fun a b => hinj (by rw [hzero a, hzero b])⟩
  exact ModuleCat.isZero_of_subsingleton _

end Work.Serre
