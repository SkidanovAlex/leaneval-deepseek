import Mathlib
import Submission.Lib.Unif2.Commons.Topology.Surface.exists_locallyFinite_coordinateBall_cover_of_noncompact

/-!
# A *locally finite* open cover by relatively compact sets

Step 1b of the ABS exhaustion (Anghel--Bruin--Stan, *Uniformization of Riemann surfaces revisited*,
arXiv:2008.12189): the cover that `SmoothPartitionOfUnity.exists_isSubordinate` consumes.

The sibling `Work.SimplyConnected.ABS.OneEnded.exists_isOpen_isCompact_closure_cover` produces an
*increasing* open cover by relatively compact sets (the right shape for the compact sublevel sets of
the exhaustion function), but an increasing cover is never locally finite, and Mathlib's
`SmoothPartitionOfUnity.exists_isSubordinate` takes a locally finite family of open sets.  The
present lemma supplies the locally finite companion: an open, locally finite cover `U` of `ℕ`-indexed
relatively compact sets.

## Proof

Both covers come from the same engine,
`refinement_of_locallyCompact_sigmaCompact_of_nhds_basis`, applied to a neighbourhood basis of `𝓝 x`
given by *coordinate balls*:

* the sibling `Commons.Topology.Surface.exists_locallyFinite_coordinateBall_cover_of_noncompact` uses
  `hasBasis_nhds_coordinateBall` (images of *closed* balls, with the closed ball inside the chart
  target), which is what makes each member compact but leaves the family closed;
* here we use `hasBasis_nhds_openCoordinateBall` below — images of *open* balls, with the same
  "room" condition on the closed ball in the chart target.  The members are then open, and the
  closure of a member is contained in the image of the corresponding *closed* ball, which is compact
  by `Commons.Topology.Surface.isCompact_symm_image_closedBall_chart`.

The refinement engine returns a locally finite family indexed by an arbitrary type `α`; `α` is
infinite (a finite cover by relatively compact sets would make `X` compact), and
`LocallyFinite.encodable` + `Denumerable.ofEncodableOfInfinite` re-index it by `ℕ` while
`LocallyFinite.comp_injective` transports local finiteness — exactly the bookkeeping of the
closed-ball sibling, and the API used there verbatim.
-/

open Set Filter

open scoped Topology

set_option maxHeartbeats 1000000

namespace Work.SimplyConnected.ABS.OneEnded

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Open coordinate balls with room for the closed ball form a neighbourhood basis.**

The predicate keeps the `target`-membership of a *closed* ball of the same radius, which is what the
refinement engine needs in order to hand back relatively compact members. -/
theorem hasBasis_nhds_openCoordinateBall (x : X) :
    (𝓝 x).HasBasis
      (fun r : ℝ => 0 < r ∧ Metric.closedBall ((chartAt ℂ x) x) r ⊆ (chartAt ℂ x).target)
      (fun r => (chartAt ℂ x).symm '' Metric.ball ((chartAt ℂ x) x) r) := by
  have hb : (𝓝 x).HasBasis (fun r : ℝ => 0 < r)
      (fun r => (chartAt ℂ x).symm '' Metric.ball ((chartAt ℂ x) x) r) := by
    have hmap : (𝓝 ((chartAt ℂ x) x)).map (chartAt ℂ x).symm = 𝓝 x :=
      (chartAt ℂ x).symm_map_nhds_eq (mem_chart_source ℂ x)
    rw [← hmap]
    exact (Metric.nhds_basis_ball (x := (chartAt ℂ x) x)).map (chartAt ℂ x).symm
  rw [hasBasis_iff] at hb ⊢
  intro t
  rw [hb t]
  constructor
  · rintro ⟨r, hr, hrt⟩
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
      ((chartAt ℂ x).open_target.mem_nhds
        ((chartAt ℂ x).map_source (mem_chart_source ℂ x)))
    refine ⟨min r (δ / 2), ⟨lt_min hr (by linarith), ?_⟩, ?_⟩
    · refine (Metric.closedBall_subset_closedBall (min_le_right _ _)).trans ?_
      exact (Metric.closedBall_subset_ball (by linarith)).trans hδsub
    · exact (image_mono (Metric.ball_subset_ball (min_le_left _ _))).trans hrt
  · rintro ⟨r, ⟨hr, -⟩, hrt⟩
    exact ⟨r, hr, hrt⟩

/-- **A countable locally finite open cover of a non-compact surface by relatively compact sets.** -/
theorem exists_locallyFinite_isOpen_isCompact_closure_cover [T2Space X] [SecondCountableTopology X]
    (hX : ¬ CompactSpace X) :
    ∃ U : ℕ → Set X, (∀ n, IsOpen (U n)) ∧ (∀ n, IsCompact (closure (U n))) ∧
      (⋃ n, U n) = Set.univ ∧ LocallyFinite U := by
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  haveI : SigmaCompactSpace X := sigmaCompactSpace_of_locallyCompact_secondCountable
  obtain ⟨α, c, r, hp, hcov, hlf⟩ :=
    refinement_of_locallyCompact_sigmaCompact_of_nhds_basis
      (ι := fun _ : X => ℝ)
      (p := fun x (r : ℝ) => 0 < r ∧ Metric.closedBall ((chartAt ℂ x) x) r ⊆ (chartAt ℂ x).target)
      (B := fun x (r : ℝ) => (chartAt ℂ x).symm '' Metric.ball ((chartAt ℂ x) x) r)
      (fun x => hasBasis_nhds_openCoordinateBall x)
  let B : α → Set X := fun a => (chartAt ℂ (c a)).symm ''
      Metric.ball ((chartAt ℂ (c a)) (c a)) (r a)
  have hopen : ∀ a, IsOpen (B a) := fun a =>
    (chartAt ℂ (c a)).isOpen_image_symm_of_subset_target Metric.isOpen_ball
      ((Metric.ball_subset_closedBall).trans (hp a).2)
  have hcomp : ∀ a, IsCompact ((chartAt ℂ (c a)).symm ''
      Metric.closedBall ((chartAt ℂ (c a)) (c a)) (r a)) := fun a =>
    Commons.Topology.Surface.isCompact_symm_image_closedBall_chart (c a) (hp a).2
  have hclo : ∀ a, IsCompact (closure (B a)) := fun a =>
    IsCompact.of_isClosed_subset (hcomp a) isClosed_closure
      (closure_minimal (image_mono Metric.ball_subset_closedBall) (hcomp a).isClosed)
  have hcovB : (⋃ a, B a) = Set.univ := hcov
  have hne : ∀ a, (B a).Nonempty := fun a =>
    ⟨c a, (chartAt ℂ (c a)) (c a), Metric.mem_ball_self (hp a).1,
      (chartAt ℂ (c a)).left_inv (mem_chart_source ℂ (c a))⟩
  have hInf : Infinite α := by
    rw [← not_finite_iff_infinite]
    intro hfin
    haveI : Fintype α := Fintype.ofFinite α
    refine hX (isCompact_univ_iff.mp ?_)
    have hsub : (Set.univ : Set X) ⊆ ⋃ a, closure (B a) := by
      rw [← hcovB]
      exact iUnion_mono fun a => subset_closure
    exact (isCompact_iUnion hclo).of_isClosed_subset isClosed_univ hsub
  letI : Encodable α := hlf.encodable hne
  letI : Denumerable α := Denumerable.ofEncodableOfInfinite α
  refine ⟨fun n => B ((Denumerable.eqv α).symm n), fun n => hopen _, fun n => hclo _, ?_, ?_⟩
  · apply eq_univ_iff_forall.2
    intro y
    have hy : y ∈ (⋃ a, B a) := by rw [hcovB]; exact mem_univ y
    rcases mem_iUnion.1 hy with ⟨a, ha⟩
    rcases (Denumerable.eqv α).symm.surjective a with ⟨n, rfl⟩
    exact mem_iUnion.2 ⟨n, ha⟩
  · simpa only [Function.comp_def] using
      hlf.comp_injective (g := (Denumerable.eqv α).symm) (Denumerable.eqv α).symm.injective

end Work.SimplyConnected.ABS.OneEnded
