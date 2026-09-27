import Mathlib
import Submission.Work.Whitney.PathTools.joinedIn_compl_of_arc_plane
import Submission.Work.Whitney.PathTools.janiszewski_subsingleton
import Submission.Work.Whitney.PathTools.ball_sdiff_totallyDisconnected_unrestricted

/-!
# The "room lemma" in the plane

If a compact arc meets the boundary sphere of an open ball in at most one point, then the ball
minus the arc is connected, in the strong sense that any two of its points are joined by a path
inside the ball.

This is the "you can walk around the endpoint" statement: an arc having at most one of its
endpoints on the sphere does not separate the ball.  The proof combines

* the planar arc theorem `Work.Whitney.PathTools.joinedIn_compl_of_arc_plane` (an arc does not
  separate the plane),
* convexity of the ball (its boundary sphere is avoided by the straight segment),
* Janiszewski's theorem for compacta with at most one common point
  (`Work.Whitney.PathTools.janiszewski_subsingleton`),
* the ball/sphere splitting lemma
  `Work.Whitney.PathTools.joinedIn_ball_sdiff_iff_compl_union_sphere`.
-/

namespace Work.Whitney.PathTools

open Set Metric Topology
open scoped Topology

noncomputable section

/-- **Room lemma (planar).**  Let `D` be an open ball in the plane and let `γ '' K` be a compact
arc whose points on the boundary sphere of `D` form a subsingleton.  Then two points of the ball
avoiding the arc can be joined by a path avoiding the arc *and staying in the ball*. -/
theorem joinedIn_ball_sdiff_arc_of_inter_sphere_subsingleton
    {p : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r)
    {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {K : Set ℝ} (hK : IsCompact K)
    (hcont : ContinuousOn γ K) (hinj : Set.InjOn γ K)
    (hsub : γ '' K ⊆ Metric.closedBall p r)
    (hss : ((γ '' K) ∩ Metric.sphere p r).Subsingleton)
    {X Y : EuclideanSpace ℝ (Fin 2)}
    (hX : X ∈ Metric.ball p r \ γ '' K) (hY : Y ∈ Metric.ball p r \ γ '' K) :
    JoinedIn (Metric.ball p r \ γ '' K) X Y := by
  have harc : IsCompact (γ '' K) := hK.image_of_continuousOn hcont
  have hsph : IsCompact (Metric.sphere p r) := isCompact_sphere p r
  have hXb : X ∈ Metric.ball p r := hX.1
  have hYb : Y ∈ Metric.ball p r := hY.1
  have hXa : X ∉ γ '' K := hX.2
  have hYa : Y ∉ γ '' K := hY.2
  have hXs : X ∉ Metric.sphere p r := fun h =>
    (ne_of_lt (Metric.mem_ball.mp hXb)) (Metric.mem_sphere.mp h)
  have hYs : Y ∉ Metric.sphere p r := fun h =>
    (ne_of_lt (Metric.mem_ball.mp hYb)) (Metric.mem_sphere.mp h)
  -- (1) avoid the arc: the planar arc theorem
  have h1 : JoinedIn ((γ '' K)ᶜ) X Y := joinedIn_compl_of_arc_plane hK hcont hinj hXa hYa
  -- (2) avoid the boundary sphere: the ball is convex
  have h2 : JoinedIn ((Metric.sphere p r)ᶜ) X Y := by
    have hsub' : Metric.ball p r ⊆ (Metric.sphere p r)ᶜ := by
      intro x hx
      rw [mem_compl_iff, Metric.mem_sphere]
      exact ne_of_lt (Metric.mem_ball.mp hx)
    have hpc : IsPathConnected (Metric.ball p r) :=
      (convex_ball p r).isPathConnected ⟨X, hXb⟩
    exact (hpc.joinedIn X hXb Y hYb).mono hsub'
  -- (3) Janiszewski with subsingleton intersection
  have h3 : JoinedIn (((γ '' K) ∪ Metric.sphere p r)ᶜ) X Y :=
    janiszewski_subsingleton harc hsph hss
      (by rw [mem_union, not_or]; exact ⟨hXa, hXs⟩)
      (by rw [mem_union, not_or]; exact ⟨hYa, hYs⟩) h1 h2
  -- (4) convert back to a path inside the ball
  exact (joinedIn_ball_sdiff_iff_compl_union_sphere (K := γ '' K) hXb hYb).mpr h3

/-- Variant with the whole arc lying strictly inside the ball. -/
theorem joinedIn_ball_sdiff_arc_of_subset_ball
    {p : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r)
    {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {K : Set ℝ} (hK : IsCompact K)
    (hcont : ContinuousOn γ K) (hinj : Set.InjOn γ K)
    (hsub : γ '' K ⊆ Metric.ball p r)
    {X Y : EuclideanSpace ℝ (Fin 2)}
    (hX : X ∈ Metric.ball p r \ γ '' K) (hY : Y ∈ Metric.ball p r \ γ '' K) :
    JoinedIn (Metric.ball p r \ γ '' K) X Y := by
  refine joinedIn_ball_sdiff_arc_of_inter_sphere_subsingleton hr hK hcont hinj
    (hsub.trans Metric.ball_subset_closedBall) ?_ hX hY
  have hempty : γ '' K ∩ Metric.sphere p r = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro z ⟨hzarc, hzsph⟩
    rw [Metric.mem_sphere] at hzsph
    exact (ne_of_lt (Metric.mem_ball.mp (hsub hzarc))) hzsph
  rw [hempty]
  intro a ha
  exact absurd ha (Set.notMem_empty a)

/-- **Room lemma for a "pacman":** an arc whose image inside the ball has an endpoint on the
boundary sphere and runs to an interior endpoint does not separate the ball. -/
theorem isPathConnected_ball_sdiff_arc_of_pacman
    {p : EuclideanSpace ℝ (Fin 2)} {r : ℝ} (hr : 0 < r)
    {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {K : Set ℝ} (hK : IsCompact K)
    (hcont : ContinuousOn γ K) (hinj : Set.InjOn γ K)
    (hsub : γ '' K ⊆ Metric.closedBall p r)
    (hss : ((γ '' K) ∩ Metric.sphere p r).Subsingleton)
    (hne : (Metric.ball p r \ γ '' K).Nonempty) :
    IsPathConnected (Metric.ball p r \ γ '' K) := by
  refine isPathConnected_iff.mpr ⟨hne, fun X hX Y hY => ?_⟩
  exact joinedIn_ball_sdiff_arc_of_inter_sphere_subsingleton hr hK hcont hinj hsub hss hX hY

end

end Work.Whitney.PathTools
