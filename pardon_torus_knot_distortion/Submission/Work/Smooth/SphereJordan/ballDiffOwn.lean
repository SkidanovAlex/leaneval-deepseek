import Mathlib
import Submission.Work.Smooth.JordanSeparation.janiszewski_disjoint

/-!
# A compact obstacle inside a ball does not disconnect the ball (inside our tree)

`Work.BoxShrink.Pinch`'s version of this statement, and the copy in
`Submission/Work/Smooth/SphereJordan/ballSdiffDiscPreconnected.lean`, both route through the
`Work.Spike` chain, whose modules cannot be imported together with the
`isPreconnected_frontier_connectedComponentIn` tree (duplicate declaration of
`isPreconnected_insert_of_mem_closure`).  Here the same proof is re-run using **our** tree's
`Work.Smooth.JordanSeparation.janiszewski_disjoint`, so the result is available in our build.

The argument is the classical one: if `K` is compact with preconnected complement and `K` lies in
the ball `B = ball p ε`, put `Q := Bᶜ ∩ closedBall 0 (‖p‖ + ε)`.  Then `Q` and `K` are disjoint
compacta, any two points of `Kᶜ` are joined inside `Kᶜ` (hypothesis) and inside `Qᶜ` (the ball is
convex and disjoint from `Q`), so Janiszewski joins them inside `(K ∪ Q)ᶜ`; and
`(K ∪ Q)ᶜ = (B \ K) ∪ (closedBall 0 (‖p‖+ε))ᶜ` is a disjoint union of open sets with the two
points in the first summand.
-/

namespace Work.Smooth.SphereJordan

open Set Metric

noncomputable section

/-- **Janiszewski for a compact obstacle inside a large ball.**  If `K ⊆ ℂ` is compact with
preconnected complement and `K ⊆ Metric.ball p ε`, then `Metric.ball p ε \ K` is preconnected. -/
theorem isPreconnected_ball_diff_of_isPreconnected_compl {K : Set ℂ} (hK : IsCompact K)
    (hKc : IsPreconnected Kᶜ) {p : ℂ} {ε : ℝ} (hsub : K ⊆ Metric.ball p ε) :
    IsPreconnected (Metric.ball p ε \ K) := by
  have hKcl : IsClosed K := hK.isClosed
  have hball_sub : Metric.ball p ε ⊆ Metric.closedBall (0 : ℂ) (‖p‖ + ε) := by
    intro z hz
    rw [Metric.mem_ball] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have hdist : ‖z - p‖ < ε := by simpa [dist_eq_norm] using hz
    have h1 : ‖z‖ ≤ ‖z - p‖ + ‖p‖ := by
      have h := norm_add_le (z - p) p
      rwa [sub_add_cancel] at h
    linarith
  set Q : Set ℂ := (Metric.ball p ε)ᶜ ∩ Metric.closedBall (0 : ℂ) (‖p‖ + ε) with hQ
  have hQcompact : IsCompact Q := by
    rw [hQ]
    exact (isCompact_closedBall (0 : ℂ) (‖p‖ + ε)).of_isClosed_subset
      (Metric.isOpen_ball.isClosed_compl.inter Metric.isClosed_closedBall) inter_subset_right
  have hdisj : Disjoint K Q := by
    rw [hQ, Set.disjoint_left]
    intro z hzK hzQ
    exact hzQ.1 (hsub hzK)
  have hKQ_eq : (K ∪ Q)ᶜ
      = (Metric.ball p ε \ K) ∪ (Metric.closedBall (0 : ℂ) (‖p‖ + ε))ᶜ := by
    ext z
    constructor
    · intro hz
      have hzK : z ∉ K := fun h => hz (Or.inl h)
      by_cases hzb : z ∈ Metric.ball p ε
      · exact Or.inl ⟨hzb, hzK⟩
      · refine Or.inr ?_
        rintro hzcB
        exact hz (Or.inr ⟨hzb, hzcB⟩)
    · rintro (⟨hzb, hzK⟩ | hzcB)
      · rintro (h | h)
        · exact hzK h
        · exact h.1 hzb
      · rintro (h | h)
        · exact hzcB (hball_sub (hsub h))
        · exact hzcB h.2
  rcases (Metric.ball p ε \ K).eq_empty_or_nonempty with hemp | ⟨x, hx⟩
  · rw [hemp]; exact isPreconnected_empty
  · obtain ⟨hxB, hxK⟩ := hx
    have hxKQ : x ∉ K ∪ Q := by
      rw [hQ]
      rintro (h | h)
      · exact hxK h
      · exact h.1 hxB
    have hkey : connectedComponentIn (Metric.ball p ε \ K) x = Metric.ball p ε \ K := by
      refine Set.Subset.antisymm (connectedComponentIn_subset _ _) fun y hy => ?_
      obtain ⟨hyB, hyK⟩ := hy
      have hcomp1 : y ∈ connectedComponentIn Kᶜ x :=
        hKc.subset_connectedComponentIn hxK subset_rfl hyK
      have hcomp2 : y ∈ connectedComponentIn Qᶜ x := by
        have hsubQ : Metric.ball p ε ⊆ Qᶜ := by
          rw [hQ]
          intro z hz h
          exact h.1 hz
        exact connectedComponentIn_mono x hsubQ
          ((convex_ball p ε).isPreconnected.subset_connectedComponentIn hxB subset_rfl hyB)
      have hyKQ : y ∉ K ∪ Q := by
        rw [hQ]
        rintro (h | h)
        · exact hyK h
        · exact h.1 hyB
      have hjan := Work.Smooth.JordanSeparation.janiszewski_disjoint hK hQcompact hdisj
        hxKQ hyKQ hcomp1 hcomp2
      rw [hKQ_eq] at hjan
      have hOpen₁ : IsOpen (Metric.ball p ε \ K) := by
        rw [Set.sdiff_eq]; exact Metric.isOpen_ball.inter hKcl.isOpen_compl
      have hOpen₂ : IsOpen ((Metric.closedBall (0 : ℂ) (‖p‖ + ε))ᶜ) :=
        Metric.isClosed_closedBall.isOpen_compl
      have hdisj₂ : Disjoint (Metric.ball p ε \ K) ((Metric.closedBall (0 : ℂ) (‖p‖ + ε))ᶜ) := by
        rw [Set.disjoint_left]
        intro z hz
        simp only [Set.mem_compl_iff, not_not]
        exact hball_sub hz.1
      have hCsub : connectedComponentIn
          ((Metric.ball p ε \ K) ∪ (Metric.closedBall (0 : ℂ) (‖p‖ + ε))ᶜ) x
          ⊆ Metric.ball p ε \ K :=
        (isPreconnected_connectedComponentIn (x := x)
          (F := (Metric.ball p ε \ K) ∪ (Metric.closedBall (0 : ℂ) (‖p‖ + ε))ᶜ)).subset_left_of_subset_union
          hOpen₁ hOpen₂ hdisj₂ (connectedComponentIn_subset _ _)
          ⟨x, mem_connectedComponentIn (Or.inl ⟨hxB, hxK⟩), hxB, hxK⟩
      have hmem : x ∈ connectedComponentIn
          ((Metric.ball p ε \ K) ∪ (Metric.closedBall (0 : ℂ) (‖p‖ + ε))ᶜ) x :=
        mem_connectedComponentIn (Or.inl ⟨hxB, hxK⟩)
      exact (isPreconnected_connectedComponentIn).subset_connectedComponentIn hmem hCsub hjan
    rw [← hkey]
    exact isPreconnected_connectedComponentIn

end

end Work.Smooth.SphereJordan
