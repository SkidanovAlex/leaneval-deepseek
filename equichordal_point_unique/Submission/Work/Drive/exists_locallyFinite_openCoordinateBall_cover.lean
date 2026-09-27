import Mathlib
import Submission.Commons.Topology.Surface.exists_locallyFinite_coordinateBall_cover_of_noncompact

open Set Filter Metric
open scoped Topology

noncomputable section

namespace Work.Drive

/-- The coordinate *open* balls whose closed ball in the model space is contained in the chart
target form a neighbourhood basis of `𝓝 x`.  This is the open-ball analogue of
`Commons.Topology.Surface.hasBasis_nhds_coordinateBall`. -/
lemma hasBasis_nhds_coordinateOpenBall {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (x : X) :
    (𝓝 x).HasBasis
      (fun r : ℝ => 0 < r ∧ Metric.closedBall ((chartAt ℂ x) x) r ⊆ (chartAt ℂ x).target)
      (fun r : ℝ => (chartAt ℂ x).symm '' Metric.ball ((chartAt ℂ x) x) r) := by
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
    rcases (Metric.nhds_basis_ball.mem_iff.mp (inter_mem hpre htarget)) with ⟨ε, hε, hsub⟩
    refine ⟨ε / 2, ⟨half_pos hε, ?_⟩, ?_⟩
    · exact (Metric.closedBall_subset_ball (half_lt_self hε)).trans
        (hsub.trans inter_subset_right)
    · rintro y ⟨w, hw, hwy⟩
      rw [← hwy]
      exact (hsub (Metric.ball_subset_ball (le_of_lt (half_lt_self hε)) hw)).1
  · rintro ⟨r, ⟨hr, -⟩, hsub⟩
    have hmap : (𝓝 ((chartAt ℂ x) x)).map ((chartAt ℂ x).symm) = 𝓝 x :=
      (chartAt ℂ x).symm_map_nhds_eq (mem_chart_source ℂ x)
    have hmem : (chartAt ℂ x).symm '' Metric.ball ((chartAt ℂ x) x) r ∈ 𝓝 x := by
      have : (chartAt ℂ x).symm '' Metric.ball ((chartAt ℂ x) x) r
          ∈ (𝓝 ((chartAt ℂ x) x)).map ((chartAt ℂ x).symm) := by
        rw [mem_map]
        exact mem_of_superset (Metric.ball_mem_nhds _ hr)
          (fun w hw => ⟨w, hw, rfl⟩)
      rwa [hmap] at this
    exact mem_of_superset hmem hsub

/-- Route: adapt `Commons.Topology.Surface.exists_locallyFinite_coordinateBall_cover_of_noncompact`
(the same file also proves `hasBasis_nhds_coordinateBall`), replacing the closed-ball neighbourhood
basis by the *open*-ball basis `{(chartAt ℂ x).symm '' Metric.ball ((chartAt ℂ x) x) r | r > 0,
Metric.closedBall ((chartAt ℂ x) x) r ⊆ (chartAt ℂ x).target}` and rerunning the same
`refinement_of_locallyCompact_sigmaCompact_of_nhds_basis` + `LocallyFinite.encodable` +
`Denumerable.ofEncodableOfInfinite` argument. -/
theorem exists_locallyFinite_openCoordinateBall_cover {X : Type*} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] [ChartedSpace ℂ X] (hX : ¬ CompactSpace X) :
    ∃ (c : ℕ → X) (r : ℕ → ℝ), (∀ n, 0 < r n) ∧
      (∀ n, Metric.closedBall ((chartAt ℂ (c n)) (c n)) (r n) ⊆ (chartAt ℂ (c n)).target) ∧
      (∀ n, IsOpen ((chartAt ℂ (c n)).symm '' Metric.ball ((chartAt ℂ (c n)) (c n)) (r n))) ∧
      (⋃ n, (chartAt ℂ (c n)).symm '' Metric.ball ((chartAt ℂ (c n)) (c n)) (r n)) = Set.univ ∧
      LocallyFinite (fun n => (chartAt ℂ (c n)).symm ''
        Metric.ball ((chartAt ℂ (c n)) (c n)) (r n)) := by
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  haveI : SigmaCompactSpace X := sigmaCompactSpace_of_locallyCompact_secondCountable
  -- Take a locally finite refinement of the coordinate open-ball neighbourhood basis.
  obtain ⟨α, c, r, hp, hcov, hlf⟩ :=
    refinement_of_locallyCompact_sigmaCompact_of_nhds_basis
      (ι := fun _ : X => ℝ)
      (p := fun x (r : ℝ) =>
        0 < r ∧ Metric.closedBall ((chartAt ℂ x) x) r ⊆ (chartAt ℂ x).target)
      (B := fun x (r : ℝ) =>
        (chartAt ℂ x).symm '' Metric.ball ((chartAt ℂ x) x) r)
      (fun x => hasBasis_nhds_coordinateOpenBall x)
  -- Each term is nonempty and open.
  have hne : ∀ a, ((chartAt ℂ (c a)).symm ''
      Metric.ball ((chartAt ℂ (c a)) (c a)) (r a)).Nonempty :=
    fun a => ⟨c a, (chartAt ℂ (c a)) (c a),
      Metric.mem_ball_self (hp a).1, (chartAt ℂ (c a)).left_inv (mem_chart_source ℂ (c a))⟩
  have hopen : ∀ a, IsOpen ((chartAt ℂ (c a)).symm ''
      Metric.ball ((chartAt ℂ (c a)) (c a)) (r a)) :=
    fun a => ((chartAt ℂ (c a)).isOpen_symm_image_iff_of_subset_target
      (Metric.ball_subset_closedBall.trans (hp a).2)).mpr Metric.isOpen_ball
  -- The corresponding closed coordinate balls are compact.
  have hcomp : ∀ a, IsCompact ((chartAt ℂ (c a)).symm ''
      Metric.closedBall ((chartAt ℂ (c a)) (c a)) (r a)) :=
    fun a => Commons.Topology.Surface.isCompact_symm_image_closedBall_chart (c a) (hp a).2
  -- The index type is encodable, and infinite because `X` is not compact.
  letI : Encodable α := hlf.encodable hne
  haveI : Infinite α := by
    rw [← not_finite_iff_infinite]
    intro hfin
    haveI : Fintype α := Fintype.ofFinite α
    refine hX (isCompact_univ_iff.mp ?_)
    have hsub : (⋃ a, (chartAt ℂ (c a)).symm ''
          Metric.ball ((chartAt ℂ (c a)) (c a)) (r a)) ⊆
        ⋃ a, (chartAt ℂ (c a)).symm ''
          Metric.closedBall ((chartAt ℂ (c a)) (c a)) (r a) :=
      Set.iUnion_mono fun a => Set.image_mono Metric.ball_subset_closedBall
    have hcov' : (⋃ a, (chartAt ℂ (c a)).symm ''
          Metric.closedBall ((chartAt ℂ (c a)) (c a)) (r a)) = Set.univ :=
      eq_univ_of_univ_subset (hcov ▸ hsub)
    rw [← hcov']
    exact isCompact_iUnion hcomp
  letI : Denumerable α := Denumerable.ofEncodableOfInfinite α
  refine ⟨fun n => c ((Denumerable.eqv α).symm n), fun n => r ((Denumerable.eqv α).symm n),
    fun n => (hp ((Denumerable.eqv α).symm n)).1,
    fun n => (hp ((Denumerable.eqv α).symm n)).2,
    fun n => hopen ((Denumerable.eqv α).symm n), ?_, ?_⟩
  · apply eq_univ_iff_forall.2
    intro y
    have hy : y ∈ (⋃ a, (chartAt ℂ (c a)).symm ''
        Metric.ball ((chartAt ℂ (c a)) (c a)) (r a)) := by
      rw [hcov]; exact mem_univ y
    rcases mem_iUnion.1 hy with ⟨a, ha⟩
    rcases (Denumerable.eqv α).symm.surjective a with ⟨n, rfl⟩
    exact mem_iUnion.2 ⟨n, ha⟩
  · simpa only [Function.comp_def] using
      hlf.comp_injective (g := (Denumerable.eqv α).symm) (Denumerable.eqv α).symm.injective

end Work.Drive
