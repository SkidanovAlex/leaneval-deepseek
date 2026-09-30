import Mathlib
import Submission.Work.ThomBordism.excludedMV
import Submission.Work.ThomBordism.convexLocalIso
import Submission.Work.ThomBordism.convexCover
import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.Cohomology.localHomology

set_option synthInstance.maxHeartbeats 400000

/-!
# Local generation from a global generator: the vocabulary

This file fixes the notation used by `Work.ThomBordism.localGeneration` and its supporting lemmas.

* `RelH M n A` is the relative homology `H_n(M, M∖A)` of the pair `(M, M∖A)` (the "excluded set"
  functor, in the `relChains` model).
* `RelHmap M n h` for `h : A ⊆ B` is the restriction `H_n(M, M∖B) → H_n(M, M∖A)`.
* `IsCoordBall n M K` is a coordinate closed ball, in exactly the form required by
  `Work.ThomBordism.convexLocalIso`.
* `RelH_point_iso`, `RelH_point_torsion_free`: the local group `H_n(M, M∖{x}) ≅ ℤ` is torsion free.

Everything here is sorry-free; the heavy lifting is in the companion files.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism

noncomputable section

variable {n : ℕ}

/-- `H_n(M, M∖A)`, the `n`-th relative homology of the pair `(M, M∖A)` (excluded set `A`). -/
abbrev RelH (M : TopCat) (n : ℕ) (A : Set M) := (Work.Cohomology.relChains M Aᶜ).homology n

/-- The restriction `H_n(M, M∖B) → H_n(M, M∖A)` induced by `A ⊆ B` (enlarging the excluded set). -/
abbrev RelHmap (M : TopCat) (n : ℕ) {A B : Set M} (h : A ⊆ B) : RelH M n B →ₗ[ℤ] RelH M n A :=
  (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap M Bᶜ Aᶜ
    (Set.compl_subset_compl.mpr h)) n).hom

/-- A coordinate closed ball of `M`, in the normal form used by
`Work.ThomBordism.convexLocalIso`. -/
def IsCoordBall (n : ℕ) (M : TopCat) [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (K : Set M) : Prop :=
  ∃ z : M, ∃ r : ℝ, 0 < r ∧
    Metric.ball ((chartAt (EuclideanSpace ℝ (Fin n)) z) z) r ⊆
      (chartAt (EuclideanSpace ℝ (Fin n)) z).target ∧
    K = (chartAt (EuclideanSpace ℝ (Fin n)) z) ⁻¹'
          Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) z) z) (r / 2) ∩
        (chartAt (EuclideanSpace ℝ (Fin n)) z).source

/-- Functoriality of the restriction maps. -/
theorem RelHmap_comp (M : TopCat) (n : ℕ) {A B C : Set M} (h₁ : A ⊆ B) (h₂ : B ⊆ C) :
    (RelHmap M n h₁).comp (RelHmap M n h₂) = RelHmap M n (h₁.trans h₂) := by
  simp only [RelHmap]
  rw [← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp]
  rw [Work.Cohomology.relCokerMap_comp]

/-- The local class of a global class `c` at a point `x`. -/
abbrev localClass (M : TopCat) (n : ℕ) (c : (Work.Cohomology.singularChains ℤ M).homology n)
    (x : M) : RelH M n {x} := Work.Cohomology.relLocClass M n c {x}

/-- `IsCoordBall` is compact. -/
theorem IsCoordBall.isCompact {M : TopCat} [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {K : Set M} (h : IsCoordBall n M K) :
    IsCompact K := by
  obtain ⟨z, r, hr, hball, rfl⟩ := h
  have hball' : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) z) z) (r/2) ⊆
      (chartAt (EuclideanSpace ℝ (Fin n)) z).target := fun y hy =>
    hball (Metric.closedBall_subset_ball (by linarith) hy)
  have heq : (chartAt (EuclideanSpace ℝ (Fin n)) z) ⁻¹'
        Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) z) z) (r / 2) ∩
      (chartAt (EuclideanSpace ℝ (Fin n)) z).source
      = (chartAt (EuclideanSpace ℝ (Fin n)) z).symm ''
        Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin n)) z) z) (r / 2) := by
    rw [OpenPartialHomeomorph.symm_image_eq_source_inter_preimage _ hball', Set.inter_comm]
  rw [heq]
  exact (isCompact_closedBall _ _).image_of_continuousOn
    ((chartAt (EuclideanSpace ℝ (Fin n)) z).continuousOn_symm.mono hball')

/-- `IsCoordBall` is closed. -/
theorem IsCoordBall.isClosed {M : TopCat} [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {K : Set M} (h : IsCoordBall n M K) :
    IsClosed K :=
  h.isCompact.isClosed

/-- `IsCoordBall` is nonempty (it contains its centre). -/
theorem IsCoordBall.nonempty {M : TopCat} [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {K : Set M} (h : IsCoordBall n M K) :
    K.Nonempty := by
  obtain ⟨z, r, hr, hball, rfl⟩ := h
  refine ⟨z, ?_, mem_chart_source _ z⟩
  show (chartAt (EuclideanSpace ℝ (Fin n)) z) z ∈ Metric.closedBall ((chartAt _ z) z) (r/2)
  rw [Metric.mem_closedBall, dist_self]
  linarith

/-- **The restriction `H_n(M, M∖K) → H_n(M, M∖{x})` out of a coordinate ball is an isomorphism**
(`Work.ThomBordism.convexLocalIso` in the `RelHmap` notation). -/
theorem IsCoordBall.isIso_restrict {M : TopCat} [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (hn : 1 ≤ n) {K : Set M}
    (h : IsCoordBall n M K) {x : M} (hx : x ∈ K) :
    IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap M Kᶜ ({x} : Set M)ᶜ
      (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx))) n) := by
  obtain ⟨z, r, hr, hball, rfl⟩ := h
  exact convexLocalIso n hn M z r hr hball x hx

/-- **The local group of a charted space is infinite cyclic.** -/
theorem RelH_point_iso (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) :
    Nonempty (RelH M n ({x} : Set M) ≅ ModuleCat.of ℤ ℤ) := by
  have hTop : (Work.Cohomology.relChains (TopCat.of ↑M) ({x} : Set ↑M)ᶜ).homology n
      = (Work.Cohomology.relChains M ({x} : Set ↑M)ᶜ).homology n := rfl
  obtain ⟨e⟩ := Work.Cohomology.localHomology n hn (M : Type) x
  have hh : ({x} : Set ↑M)ᶜ = {y : ↑M | y ≠ x} := by ext y; simp
  exact ⟨(eqToIso hTop).symm.trans ((eqToIso (congrArg (fun S : Set ↑M =>
    (Work.Cohomology.relChains (TopCat.of ↑M) S).homology n) hh)).trans e)⟩

/-- **The local group is torsion free**: `t • v = 0` with `t ≠ 0` forces `v = 0`. -/
theorem RelH_point_torsion_free (n : ℕ) (hn : 1 ≤ n) (M : TopCat) [CompactSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) (t : ℤ)
    (v : RelH M n ({x} : Set M)) (hv : t • v = 0) (ht : t ≠ 0) : v = 0 := by
  obtain ⟨E⟩ := RelH_point_iso n hn M x
  have h1 : (ConcreteCategory.hom E.hom) (t • v) = 0 := by rw [hv, map_zero]
  rw [map_zsmul] at h1
  have h1' : t * (ConcreteCategory.hom E.hom) v = 0 := by simpa using h1
  have h2 : (ConcreteCategory.hom E.hom) v = 0 := (mul_eq_zero.mp h1').resolve_left ht
  have hinj : Function.Injective (ConcreteCategory.hom E.hom) :=
    (ModuleCat.mono_iff_injective E.hom).mp inferInstance
  exact hinj (by rw [h2, map_zero])

end

end Work.ThomBordism
