import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.DiscCurve
import Submission.Work.Smooth.SphereJordan.bumpSideV
import Submission.Work.Smooth.SphereJordan.jsepExists
import Submission.Work.Smooth.SphereJordan.crosscutComponents
import Submission.Work.BoxShrink.Pinch.janiszewskiDisjointCompact
import Submission.Work.Smooth.SphereJordan.compl_range_disc_preconnected_plane

-- the statement's arc hypotheses `hδ`, `hδsub` and the endpoint conditions `hs0`, `hs1` are not
-- needed for the conclusion: the lemma holds for an arbitrary `s`
set_option linter.unusedVariables false

namespace Work.Smooth.SphereJordan

/-!
# The complement of an embedded disc inside a large ball is preconnected

`Work.Smooth.SphereJordan.ballSdiffDiscPreconnected`: if `f : 𝔻 → ℂ` is an injective continuous
map (so that `K = range f` is an embedded closed disc) and `δ` is an arc of the frontier of `K`
with `p = δ s` an interior point of the arc, then for *some* `ε > 0` the set
`Metric.ball p ε \ K` is preconnected.

The geometry is that of a large ball: choose `ε` so large that the whole disc `K` lies inside the
ball `Metric.ball p ε` but still strictly inside a compact set `Q = (Metric.ball p ε)ᶜ ∩
Metric.closedBall 0 R`.  Then `Q` and `K` are disjoint compacta, and any two points of `Kᶜ` are
joined in `Kᶜ` (`compl_range_disc_preconnected_plane`) and also in `Qᶜ` (because the ball is
convex and disjoint from `Q`); Janiszewski's theorem for disjoint compacta
(`Work.BoxShrink.Pinch.janiszewskiDisjointCompact`) then joins them in `(K ∪ Q)ᶜ`.  As
`(K ∪ Q)ᶜ = (Metric.ball p ε \ K) ∪ (Metric.closedBall 0 R)ᶜ` is a disjoint union of two open
sets and both the points considered lie in the first, the connection already takes place in the
ball.
-/

/-- **Janiszewski for a compact obstacle inside a large ball.**

If `K ⊆ ℂ` is compact with preconnected complement and `K` lies in the ball `Metric.ball p ε`,
then `Metric.ball p ε \ K` is preconnected. -/
theorem isPreconnected_ball_sdiff_of_isPreconnected_compl {K : Set ℂ} (hK : IsCompact K)
    (hKc : IsPreconnected Kᶜ) {p : ℂ} {ε : ℝ} (hsub : K ⊆ Metric.ball p ε) :
    IsPreconnected (Metric.ball p ε \ K) := by
  have hKcl : IsClosed K := hK.isClosed
  -- the ball sits in the closed ball of radius `‖p‖ + ε` about the origin
  have hball_sub : Metric.ball p ε ⊆ Metric.closedBall (0 : ℂ) (‖p‖ + ε) := by
    intro z hz
    rw [Metric.mem_ball] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have hdist : ‖z - p‖ < ε := by simpa [dist_eq_norm] using hz
    have h1 : ‖z‖ ≤ ‖z - p‖ + ‖p‖ := by
      have h := norm_add_le (z - p) p
      rwa [sub_add_cancel] at h
    linarith
  -- the outer compact obstacle
  set Q : Set ℂ := (Metric.ball p ε)ᶜ ∩ Metric.closedBall (0 : ℂ) (‖p‖ + ε) with hQ
  have hQcompact : IsCompact Q := by
    rw [hQ]
    exact Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨(Metric.isOpen_ball.isClosed_compl).inter Metric.isClosed_closedBall,
        Metric.isBounded_closedBall.subset Set.inter_subset_right⟩
  have hdisj : Disjoint K Q := by
    rw [hQ, Set.disjoint_left]
    intro z hzK hzQ
    exact hzQ.1 (hsub hzK)
  -- the complement of `K ∪ Q` is a disjoint union of two open sets
  have hQc : Qᶜ = Metric.ball p ε ∪ (Metric.closedBall (0 : ℂ) (‖p‖ + ε))ᶜ := by
    rw [hQ, Set.compl_inter]
    ext z
    simp
  have hKQ_eq : (K ∪ Q)ᶜ = (Metric.ball p ε \ K) ∪ (Metric.closedBall (0 : ℂ) (‖p‖ + ε))ᶜ := by
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
      -- the two connectedness hypotheses of Janiszewski
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
      have hjan := Work.BoxShrink.Pinch.janiszewskiDisjointCompact hK hQcompact hdisj
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

/-- **Pardon's disc/arc lemma.** -/
theorem ballSdiffDiscPreconnected {f : C(Work.Smooth.SphereJordan.Disc, ℂ)}
    (hf : Function.Injective f)
    {δ : C(Set.Icc (0 : ℝ) 1, ℂ)} (hδ : Function.Injective δ)
    (hδsub : Set.range δ ⊆ frontier (Set.range f))
    (s : Set.Icc (0 : ℝ) 1) (hs0 : s ≠ ⟨0, by norm_num⟩) (hs1 : s ≠ ⟨1, by norm_num⟩) :
    ∃ ε : ℝ, 0 < ε ∧ IsPreconnected (Metric.ball (δ s) ε \ Set.range f) := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z : Work.Smooth.SphereJordan.Disc, ‖f z‖ ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_range (f.continuous.norm)).bddAbove
    exact ⟨M, fun z => hM ⟨z, rfl⟩⟩
  have hM0 : 0 ≤ M := by
    have h1 : ‖f ⟨(0 : ℂ), by simp [Metric.mem_closedBall]⟩‖ ≤ M := hM _
    exact le_trans (norm_nonneg _) h1
  have hεpos : 0 < ‖δ s‖ + M + 1 := by linarith [norm_nonneg (δ s)]
  refine ⟨‖δ s‖ + M + 1, hεpos, ?_⟩
  refine isPreconnected_ball_sdiff_of_isPreconnected_compl (isCompact_range f.continuous)
    (compl_range_disc_preconnected_plane hf) ?_
  rintro z ⟨w, rfl⟩
  rw [Metric.mem_ball, dist_eq_norm]
  calc ‖f w - δ s‖ ≤ ‖f w‖ + ‖δ s‖ := norm_sub_le _ _
    _ ≤ M + ‖δ s‖ := by linarith [hM w]
    _ < ‖δ s‖ + M + 1 := by linarith

end Work.Smooth.SphereJordan
