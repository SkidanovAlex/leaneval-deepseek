import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Compactness.Paracompact

open Set Filter Function
open scoped Topology

namespace Commons.Topology.Surface

/-- For a point `x` of a complex-charted space and a radius `r ≥ 0`, the closed coordinate ball
`(chartAt ℂ x).symm '' closedBall ((chartAt ℂ x) x) r` contains `x`. -/
lemma mem_coordinateBall {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (x : X) (r : ℝ)
    (hr : 0 ≤ r) : x ∈ (chartAt ℂ x).symm '' Metric.closedBall ((chartAt ℂ x) x) r :=
  ⟨(chartAt ℂ x) x, Metric.mem_closedBall.mpr (by simpa using hr),
   (chartAt ℂ x).left_inv (mem_chart_source ℂ x)⟩

/-- The image of a coordinate closed ball (contained in the chart target) under the inverse chart is
compact. -/
lemma isCompact_symm_image_closedBall_chart {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (x : X) {r : ℝ}
    (hr : Metric.closedBall ((chartAt ℂ x) x) r ⊆ (chartAt ℂ x).target) :
    IsCompact ((chartAt ℂ x).symm '' Metric.closedBall ((chartAt ℂ x) x) r) :=
  (isCompact_closedBall _ _).image_of_continuousOn
    ((chartAt ℂ x).continuousOn_symm.mono hr)

/-- The coordinate closed balls whose closed ball in the model space is contained in the chart
target form a neighbourhood basis of `𝓝 x`. -/
lemma hasBasis_nhds_coordinateBall {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (x : X) :
    (𝓝 x).HasBasis
      (fun r : ℝ => 0 < r ∧ Metric.closedBall ((chartAt ℂ x) x) r ⊆ (chartAt ℂ x).target)
      (fun r : ℝ => (chartAt ℂ x).symm '' Metric.closedBall ((chartAt ℂ x) x) r) := by
  rw [hasBasis_iff]
  intro t
  constructor
  · intro ht
    have hmap : (𝓝 ((chartAt ℂ x) x)).map ((chartAt ℂ x).symm) = 𝓝 x :=
      (chartAt ℂ x).symm_map_nhds_eq (mem_chart_source ℂ x)
    have hpre : (chartAt ℂ x).symm ⁻¹' t ∈ 𝓝 ((chartAt ℂ x) x) := by
      have : t ∈ (𝓝 ((chartAt ℂ x) x)).map (chartAt ℂ x).symm := hmap ▸ ht
      exact mem_map.mp this
    have htarget : (chartAt ℂ x).target ∈ 𝓝 ((chartAt ℂ x) x) := chart_target_mem_nhds ℂ x
    rcases (Metric.nhds_basis_closedBall.mem_iff.mp (inter_mem hpre htarget)) with ⟨ε, hε, hsub⟩
    exact ⟨ε, ⟨hε, hsub.trans inter_subset_right⟩,
      fun y ⟨w, hw, hwy⟩ => hwy ▸ (hsub hw).1⟩
  · rintro ⟨r, ⟨hr, -⟩, hsub⟩
    have hmap : (𝓝 ((chartAt ℂ x) x)).map ((chartAt ℂ x).symm) = 𝓝 x :=
      (chartAt ℂ x).symm_map_nhds_eq (mem_chart_source ℂ x)
    have hmem : (chartAt ℂ x).symm '' Metric.closedBall ((chartAt ℂ x) x) r ∈ 𝓝 x := by
      have : (chartAt ℂ x).symm '' Metric.closedBall ((chartAt ℂ x) x) r
          ∈ (𝓝 ((chartAt ℂ x) x)).map ((chartAt ℂ x).symm) := by
        rw [mem_map]
        exact mem_of_superset (Metric.closedBall_mem_nhds _ hr)
          (fun w hw => ⟨w, hw, rfl⟩)
      rwa [hmap] at this
    exact mem_of_superset hmem hsub

/-- **Corrected form of `exists_locallyFinite_coordinateBall_cover`:** the hypothesis
`hX : ¬ CompactSpace X` is indispensable; without it the statement is (formally) false, since every
term `(chartAt ℂ (c n)).symm '' closedBall ((chartAt ℂ (c n)) (c n)) (r n)` contains `c n`
(`(chartAt ℂ x).left_inv (mem_chart_source ℂ x)` and `dist_self`), while a locally finite family of
nonempty sets in a compact space has only finitely many nonempty members
(`LocallyFinite.finite_of_compact`).

Suggested route: `ChartedSpace.locallyCompactSpace` and
`sigmaCompactSpace_of_locallyCompact_secondCountable` provide the instances; apply
`refinement_of_locallyCompact_sigmaCompact_of_nhds_basis` to the neighbourhood basis of coordinate
closed balls (`hasBasis_nhds_coordinateBall`) to get a locally finite covering indexed by some `α`;
`isCompact_symm_image_closedBall` gives compactness of the terms (hence their nonemptiness);
`LocallyFinite.encodable` makes `α` encodable and `hX` makes `α` infinite (a finite `α` would
express `X` as a finite union of compact sets, i.e. `CompactSpace X`); finally
`Denumerable.ofEncodableOfInfinite` + `Denumerable.eqv` reindex by `ℕ`
(`LocallyFinite.comp_injective`). -/
theorem exists_locallyFinite_coordinateBall_cover_of_noncompact {X : Type*} [TopologicalSpace X]
    [T2Space X] [SecondCountableTopology X] [ChartedSpace ℂ X] (hX : ¬ CompactSpace X) :
    ∃ (c : ℕ → X) (r : ℕ → ℝ), (∀ n, 0 < r n) ∧
      (∀ n, Metric.closedBall ((chartAt ℂ (c n)) (c n)) (r n) ⊆ (chartAt ℂ (c n)).target) ∧
      (∀ n, IsCompact ((chartAt ℂ (c n)).symm ''
        Metric.closedBall ((chartAt ℂ (c n)) (c n)) (r n))) ∧
      (⋃ n, (chartAt ℂ (c n)).symm ''
        Metric.closedBall ((chartAt ℂ (c n)) (c n)) (r n)) = Set.univ ∧
      LocallyFinite (fun n => (chartAt ℂ (c n)).symm ''
        Metric.closedBall ((chartAt ℂ (c n)) (c n)) (r n)) := by
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  haveI : SigmaCompactSpace X := sigmaCompactSpace_of_locallyCompact_secondCountable
  -- Take a locally finite refinement of the coordinate-ball neighbourhood basis.
  obtain ⟨α, c, r, hp, hcov, hlf⟩ :=
    refinement_of_locallyCompact_sigmaCompact_of_nhds_basis
      (ι := fun _ : X => ℝ)
      (p := fun x (r : ℝ) =>
        0 < r ∧ Metric.closedBall ((chartAt ℂ x) x) r ⊆ (chartAt ℂ x).target)
      (B := fun x (r : ℝ) =>
        (chartAt ℂ x).symm '' Metric.closedBall ((chartAt ℂ x) x) r)
      (fun x => hasBasis_nhds_coordinateBall x)
  -- Each term is nonempty and compact.
  have hne : ∀ a, ((chartAt ℂ (c a)).symm ''
      Metric.closedBall ((chartAt ℂ (c a)) (c a)) (r a)).Nonempty :=
    fun a => ⟨c a, mem_coordinateBall (c a) (r a) (hp a).1.le⟩
  have hcomp : ∀ a, IsCompact ((chartAt ℂ (c a)).symm ''
      Metric.closedBall ((chartAt ℂ (c a)) (c a)) (r a)) :=
    fun a => isCompact_symm_image_closedBall_chart (c a) (hp a).2
  -- The index type is encodable, and infinite because `X` is not compact.
  letI : Encodable α := hlf.encodable hne
  have hInf : Infinite α := by
    rw [← not_finite_iff_infinite]
    intro hfin
    haveI : Fintype α := Fintype.ofFinite α
    exact hX (isCompact_univ_iff.mp (by
      rw [← hcov]
      exact isCompact_iUnion hcomp))
  letI : Denumerable α := Denumerable.ofEncodableOfInfinite α
  refine ⟨fun n => c ((Denumerable.eqv α).symm n), fun n => r ((Denumerable.eqv α).symm n),
    fun n => (hp ((Denumerable.eqv α).symm n)).1,
    fun n => (hp ((Denumerable.eqv α).symm n)).2,
    fun n => hcomp ((Denumerable.eqv α).symm n), ?_, ?_⟩
  · apply eq_univ_iff_forall.2
    intro y
    have hy : y ∈ (⋃ a, (chartAt ℂ (c a)).symm ''
        Metric.closedBall ((chartAt ℂ (c a)) (c a)) (r a)) := by
      rw [hcov]; exact mem_univ y
    rcases mem_iUnion.1 hy with ⟨a, ha⟩
    rcases (Denumerable.eqv α).symm.surjective a with ⟨n, rfl⟩
    exact mem_iUnion.2 ⟨n, ha⟩
  · simpa only [Function.comp_def] using
      hlf.comp_injective (g := (Denumerable.eqv α).symm) (Denumerable.eqv α).symm.injective

end Commons.Topology.Surface