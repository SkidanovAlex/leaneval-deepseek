import Mathlib
import Submission.Work.Cohomology.local_generator_ball
import Submission.Work.Cohomology.pd_coordinate_ball
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.RelCapHTransfer
import Submission.Work.Cohomology.pd_plumbing
import Submission.Work.Cohomology.excision

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The fundamental class of a coordinate ball pair

Let `M` be a compact Hausdorff space charted in dimension `N ≥ 1`, `c ∈ H_N(M;ℤ)` a class whose
image in `H_N(M, M∖{x})` generates for every point `x` (`hc`), and let

* `e = chartAt _ z`, `r > 0` with `Metric.ball (e z) r ⊆ e.target`,
* `U = e ⁻¹' Metric.ball (e z) r ∩ e.source` (a coordinate ball),
* `K = e ⁻¹' Metric.closedBall (e z) (r/2) ∩ e.source` (a concentric closed ball),
* `A = {y : U | (y : M) ∈ Kᶜ} = U ∖ K`.

Write `μ_K = relLocClass M N c K` for the image of `c` in `H_N(M, M∖K)` (a generator, by
`local_generator_ball`).  The theorem says that any class `μ ∈ H_N(U, A)` whose image under the
inclusion of pairs `(U, A) → (M, M∖K)` is `μ_K` is *the* fundamental class of the pair `(U, A)`:
it generates `H_N(U,A) ≅ ℤ`, and for every `k + m = N` the relative cap product

`x ↦ x ⌢ μ : H^k(U, A; ℤ) → H_m(U; ℤ)`

is bijective — the base case (C) of Poincaré–Lefschetz duality, in the form in which the class is
produced by excision rather than chosen as an abstract generator.

## Proof

* `local_generator_ball` gives that `μ_K` generates `H_N(M, M∖K)`.
* The inclusion of pairs `(U, A) → (M, M∖K)` is an isomorphism on homology (`excision`, since
  `U` and `Kᶜ` are open and `U ∪ Kᶜ = M`); here the crucial point is that `K` is *compact* (it is
  the image of the compact closed ball `Metric.closedBall (e z) (r/2) ⊆ e.target` under
  `e.symm`), hence closed, so that `Kᶜ` is open.
* Therefore `ℤ ∙ μ = ⊤`: the image of `ℤ ∙ μ` is `ℤ ∙ μ_K = ⊤`, and the map is injective.
* The cap-product statement is then `pd_coordinate_ball`.
-/

set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

theorem pd_coordinate_ball_fundamental (N : ℕ) (hN : 1 ≤ N) (M : TopCat) [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
    (c : (Work.Cohomology.singularChains ℤ M).homology N)
    (hc : ∀ x : M, Submodule.span ℤ
      {((HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains M {y | y ≠ x})) N) c)} = ⊤)
    (z : M) (r : ℝ) (hr : 0 < r) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt _ z
    Metric.ball (e z) r ⊆ e.target →
    let U : Set M := e ⁻¹' Metric.ball (e z) r ∩ e.source
    let K : Set M := e ⁻¹' Metric.closedBall (e z) (r/2) ∩ e.source
    let A : Set U := {y | (y : M) ∈ Kᶜ}
    (hzK : z ∈ K) →
    ∀ (μ : (Work.Cohomology.relChains (TopCat.of U) A).homology N),
      (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap M U Kᶜ) N) μ
        = Work.Cohomology.relLocClass M N c K →
      Submodule.span ℤ {μ} = ⊤ ∧
      ∀ (k m : ℕ) (hkm : k + m = N),
        Function.Bijective
          (fun x => (Work.Cohomology.relCapPair (TopCat.of U) A k m) x (hkm ▸ μ)) := by
  intro e hball U K A hzK μ hμ
  -- `μ_K` generates, by `local_generator_ball`
  have hgen : Submodule.span ℤ {Work.Cohomology.relLocClass M N c K} = ⊤ :=
    Work.Cohomology.local_generator_ball N hN M c hc z r hr hball
  -- `r/2 < r` (so that the smaller closed ball is contained in the open ball)
  have hcl2 : Metric.closedBall (e z) (r/2) ⊆ Metric.ball (e z) r := fun v hv => by
    rw [Metric.mem_ball]
    have := Metric.mem_closedBall.mp hv
    linarith
  have hcl : Metric.closedBall (e z) (r/2) ⊆ e.target := hcl2.trans hball
  -- `U` is open
  have hUob : IsOpen U := by
    show IsOpen (e ⁻¹' Metric.ball (e z) r ∩ e.source)
    rw [Set.inter_comm]
    exact e.isOpen_inter_preimage Metric.isOpen_ball
  -- `K` is compact: it is the image of the compact closed ball under `e.symm`
  have hK_eq : K = e.symm '' Metric.closedBall (e z) (r/2) := by
    show e ⁻¹' Metric.closedBall (e z) (r/2) ∩ e.source
      = ↑e.symm '' Metric.closedBall (e z) (r/2)
    rw [Set.inter_comm, ← OpenPartialHomeomorph.symm_image_eq_source_inter_preimage e hcl]
  have hKcob : IsOpen Kᶜ := by
    rw [hK_eq]
    exact ((isCompact_closedBall (e z) (r/2)).image_of_continuousOn
      (e.continuousOn_symm.mono hcl)).isClosed.isOpen_compl
  -- `U ∪ Kᶜ = M`
  have hcov : U ∪ Kᶜ = Set.univ := by
    ext x
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    by_cases hx : x ∈ K
    · left
      have hb : (e : M → EuclideanSpace ℝ (Fin N)) x ∈ Metric.closedBall (e z) (r/2) := by
        have h' := hx
        simp only [K, Set.mem_inter_iff, Set.mem_preimage] at h'
        exact h'.1
      have hsrc : x ∈ e.source := by
        have h' := hx
        simp only [K, Set.mem_inter_iff, Set.mem_preimage] at h'
        exact h'.2
      exact ⟨Set.mem_preimage.mpr (hcl2 hb), hsrc⟩
    · right
      exact hx
  -- excision: the inclusion of pairs `(U, A) → (M, M∖K)` is an isomorphism on homology
  have hiso : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap M U Kᶜ) N) :=
    Work.Cohomology.excision_relChainsMap_isIso M U Kᶜ hUob hKcob hcov N
  -- the image of `ℤ ∙ μ` is `⊤`, and the map is injective, so `ℤ ∙ μ = ⊤`
  have hμgen : Submodule.span ℤ {μ} = ⊤ := by
    let φ : ↥((Work.Cohomology.relChains (TopCat.of U) A).homology N) →ₗ[ℤ]
        ↥((Work.Cohomology.relChains M Kᶜ).homology N) :=
      (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap M U Kᶜ) N).hom
    have hφμ : φ μ = Work.Cohomology.relLocClass M N c K := hμ
    have hspanφ : Submodule.span ℤ {φ μ} = ⊤ := by rw [hφμ]; exact hgen
    have hinj : Function.Injective φ := by
      have h := (ModuleCat.mono_iff_injective
        (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap M U Kᶜ) N)).mp
        (IsIso.mono_of_iso _)
      simpa [φ] using h
    refine le_antisymm le_top ?_
    intro v _
    have hmem : φ v ∈ Submodule.map φ (Submodule.span ℤ ({μ} : Set _)) := by
      rw [Submodule.map_span, Set.image_singleton, hspanφ]
      exact Submodule.mem_top
    obtain ⟨x, hx, hxv⟩ := hmem
    have hxv' : x = v := hinj hxv
    rw [← hxv']
    exact hx
  refine ⟨hμgen, fun k m hkm => ?_⟩
  -- the cap product with the fundamental class of the pair, by `pd_coordinate_ball`
  exact Work.Cohomology.pd_coordinate_ball N hN M z r hr hball μ hμgen k m hkm

end

end Work.Cohomology
