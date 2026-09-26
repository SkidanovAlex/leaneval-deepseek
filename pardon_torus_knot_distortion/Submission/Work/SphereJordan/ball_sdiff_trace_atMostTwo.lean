import Mathlib
import Submission.Work.SphereJordan.chamberDefs
import Submission.Work.Smooth.SphereJordan.ballDiffOwn
import Submission.Work.Smooth.JordanSeparation.janiszewski_connectedInter_plane
import Submission.Work.SphereJordan.exteriorGermSetup

namespace Work.SphereJordan

open Set Metric

noncomputable section

/-! ## Elementary preliminaries -/

/-- **Pigeonhole for a set covered by two preconnected pieces.**  If `T = A ∪ B` with `A` and `B`
preconnected, then of any three points of `T` two lie in the same connected component of `T`. -/
theorem atMostTwo_of_union_of_two_preconnected {α : Type*} [TopologicalSpace α] {T A B : Set α}
    (hT : T = A ∪ B) (hA : IsPreconnected A) (hB : IsPreconnected B) (hAT : A ⊆ T)
    (hBT : B ⊆ T) {x y z : α} (hx : x ∈ T) (hy : y ∈ T) (hz : z ∈ T) :
    connectedComponentIn T x = connectedComponentIn T y ∨
      connectedComponentIn T x = connectedComponentIn T z ∨
      connectedComponentIn T y = connectedComponentIn T z := by
  have keyA : ∀ p q : α, p ∈ A → q ∈ A →
      connectedComponentIn T p = connectedComponentIn T q := fun p q hp hq =>
    connectedComponentIn_eq ((hA.subset_connectedComponentIn hp hAT) hq)
  have keyB : ∀ p q : α, p ∈ B → q ∈ B →
      connectedComponentIn T p = connectedComponentIn T q := fun p q hp hq =>
    connectedComponentIn_eq ((hB.subset_connectedComponentIn hp hBT) hq)
  have hxAB : x ∈ A ∪ B := hT ▸ hx
  have hyAB : y ∈ A ∪ B := hT ▸ hy
  have hzAB : z ∈ A ∪ B := hT ▸ hz
  rcases hxAB with hxA | hxB
  · rcases hyAB with hyA | hyB
    · exact Or.inl (keyA x y hxA hyA)
    · rcases hzAB with hzA | hzB
      · exact Or.inr (Or.inl (keyA x z hxA hzA))
      · exact Or.inr (Or.inr (keyB y z hyB hzB))
  · rcases hyAB with hyA | hyB
    · rcases hzAB with hzA | hzB
      · exact Or.inr (Or.inr (keyA y z hyA hzA))
      · exact Or.inr (Or.inl (keyB x z hxB hzB))
    · exact Or.inl (keyB x y hxB hyB)

/-- A closed ball of radius `ε` around `p` is contained in the closed ball of radius `‖p‖ + ε`
around the origin. -/
theorem closedBall_subset_closedBall_norm_add (p : ℂ) (ε : ℝ) :
    Metric.closedBall p ε ⊆ Metric.closedBall (0 : ℂ) (‖p‖ + ε) := by
  intro z hz
  rw [Metric.mem_closedBall] at hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 : ‖z‖ ≤ ‖z - p‖ + ‖p‖ := by
    have h := norm_add_le (z - p) p
    rwa [sub_add_cancel] at h
  have h2 : ‖z - p‖ ≤ ε := by simpa [dist_eq_norm] using hz
  linarith

/-- The open ball of radius `ε` around `p` is contained in the closed ball of radius `‖p‖ + ε`
around the origin. -/
theorem ball_subset_closedBall_norm_add (p : ℂ) (ε : ℝ) :
    Metric.ball p ε ⊆ Metric.closedBall (0 : ℂ) (‖p‖ + ε) := by
  intro z hz
  rw [Metric.mem_ball] at hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 : ‖z‖ ≤ ‖z - p‖ + ‖p‖ := by
    have h := norm_add_le (z - p) p
    rwa [sub_add_cancel] at h
  have h2 : ‖z - p‖ < ε := by simpa [dist_eq_norm] using hz
  linarith

/-- **`closure S.V` is contained in any closed ball containing `S.V` and the trace.** -/
theorem closure_V_subset_closedBall {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation γ) {p : ℂ} {ε : ℝ}
    (hsub : γ.trace ⊆ Metric.closedBall p ε) (hV : S.V ⊆ Metric.ball p ε) :
    closure S.V ⊆ Metric.closedBall p ε := by
  rw [closure_eq_self_union_frontier, frontier_V_eq_trace S]
  exact Set.union_subset (Subset.trans hV Metric.ball_subset_closedBall) hsub

/-! ## An abstract preconnectedness statement -/

/-- **The complement of a compact set in a ball, when the complement of the compact set and its
part outside the ball are preconnected.**  If `K` is compact with preconnected complement and with
`K ∩ (ball p ε)ᶜ` preconnected, and `K` lies in the closed ball of radius `ε`, then
`Metric.ball p ε \ K` is preconnected.

The argument is Janiszewski's: cut the plane along `K` and along the annular region
`Q = (ball p ε)ᶜ ∩ closedBall 0 (‖p‖ + ε)`.  The two cuts meet in `K ∩ (ball p ε)ᶜ`, which is
preconnected; hence any two points of `ball p ε \ K` are joined avoiding `K ∪ Q`.  But
`(K ∪ Q)ᶜ = (ball p ε \ K) ∪ (closedBall 0 (‖p‖ + ε))ᶜ` is a disjoint union of open sets with the
two points in the first summand, so they are joined inside `ball p ε \ K`. -/
theorem isPreconnected_ball_sdiff_of_isCompact_of_compl {K : Set ℂ} {p : ℂ} {ε : ℝ}
    (hK : IsCompact K) (hKc : IsPreconnected Kᶜ) (hKsub : K ⊆ Metric.closedBall p ε)
    (hZ : IsPreconnected (K ∩ (Metric.ball p ε)ᶜ)) :
    IsPreconnected (Metric.ball p ε \ K) := by
  have hball_sub : Metric.ball p ε ⊆ Metric.closedBall (0 : ℂ) (‖p‖ + ε) :=
    ball_subset_closedBall_norm_add p ε
  have hKsub' : K ⊆ Metric.closedBall (0 : ℂ) (‖p‖ + ε) :=
    Subset.trans hKsub (closedBall_subset_closedBall_norm_add p ε)
  set Q : Set ℂ := (Metric.ball p ε)ᶜ ∩ Metric.closedBall (0 : ℂ) (‖p‖ + ε) with hQ
  have hQcompact : IsCompact Q := by
    rw [hQ]
    exact (isCompact_closedBall (0 : ℂ) (‖p‖ + ε)).of_isClosed_subset
      (Metric.isOpen_ball.isClosed_compl.inter Metric.isClosed_closedBall) inter_subset_right
  have hKQ : K ∩ Q = K ∩ (Metric.ball p ε)ᶜ := by
    apply Subset.antisymm
    · rintro z ⟨hzK, hzQ⟩
      exact ⟨hzK, hzQ.1⟩
    · rintro z ⟨hzK, hzB⟩
      exact ⟨hzK, hzB, hKsub' hzK⟩
  rcases (K ∩ Q).eq_empty_or_nonempty with hemp | hne
  · -- `K` lies inside the ball: the result is the standard "ball minus a compact obstacle"
    have hKball : K ⊆ Metric.ball p ε := by
      intro z hzK
      have hzcl : z ∈ Metric.closedBall (0 : ℂ) (‖p‖ + ε) := hKsub' hzK
      by_contra hzb
      have hmem : z ∈ K ∩ Q := ⟨hzK, hzb, hzcl⟩
      rw [hemp] at hmem
      exact hmem
    exact Work.Smooth.SphereJordan.isPreconnected_ball_diff_of_isPreconnected_compl
      hK hKc hKball
  · obtain ⟨z₀, hz₀⟩ := hne
    have hpre : IsPreconnected (K ∩ Q) := by rw [hKQ]; exact hZ
    rcases (Metric.ball p ε \ K).eq_empty_or_nonempty with hempB | ⟨x, hx⟩
    · rw [hempB]; exact isPreconnected_empty
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
        have hjan := Work.Smooth.JordanSeparation.janiszewski_connectedInter_plane hK hQcompact
          ⟨z₀, hz₀⟩ hpre hxKQ hyKQ hcomp1 hcomp2
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
              · exact hzcB (hKsub' h)
              · exact hzcB h.2
        rw [hKQ_eq] at hjan
        have hOpen₁ : IsOpen (Metric.ball p ε \ K) := by
          rw [Set.sdiff_eq]; exact Metric.isOpen_ball.inter hK.isClosed.isOpen_compl
        have hOpen₂ : IsOpen ((Metric.closedBall (0 : ℂ) (‖p‖ + ε))ᶜ) :=
          Metric.isClosed_closedBall.isOpen_compl
        have hdisj₂ : Disjoint (Metric.ball p ε \ K)
            ((Metric.closedBall (0 : ℂ) (‖p‖ + ε))ᶜ) := by
          rw [Set.disjoint_left]
          intro z hz
          simp only [Set.mem_compl_iff, not_not]
          exact hball_sub hz.1
        have hCsub : connectedComponentIn
            ((Metric.ball p ε \ K) ∪ (Metric.closedBall (0 : ℂ) (‖p‖ + ε))ᶜ) x
            ⊆ Metric.ball p ε \ K :=
          (isPreconnected_connectedComponentIn (x := x)
            (F := (Metric.ball p ε \ K)
              ∪ (Metric.closedBall (0 : ℂ) (‖p‖ + ε))ᶜ)).subset_left_of_subset_union
            hOpen₁ hOpen₂ hdisj₂ (connectedComponentIn_subset _ _)
            ⟨x, mem_connectedComponentIn (Or.inl ⟨hxB, hxK⟩), hxB, hxK⟩
        have hmem : x ∈ connectedComponentIn
            ((Metric.ball p ε \ K) ∪ (Metric.closedBall (0 : ℂ) (‖p‖ + ε))ᶜ) x :=
          mem_connectedComponentIn (Or.inl ⟨hxB, hxK⟩)
        exact (isPreconnected_connectedComponentIn).subset_connectedComponentIn hmem hCsub hjan
      rw [← hkey]
      exact isPreconnected_connectedComponentIn

/-! ## The target -/

theorem ball_sdiff_trace_atMostTwo {γ : Work.Smooth.Jordan.PlaneCurve}
    (S : Work.Smooth.Jordan.PlaneSeparation γ) {p : ℂ} {ε : ℝ}
    (hsub : γ.trace ⊆ Metric.closedBall p ε) (hV : S.V ⊆ Metric.ball p ε)
    (hZ : IsPreconnected (γ.trace ∩ (Metric.ball p ε)ᶜ)) :
    ∀ x y z : ℂ, x ∈ Metric.ball p ε \ γ.trace → y ∈ Metric.ball p ε \ γ.trace →
      z ∈ Metric.ball p ε \ γ.trace →
      connectedComponentIn (Metric.ball p ε \ γ.trace) x =
        connectedComponentIn (Metric.ball p ε \ γ.trace) y ∨
      connectedComponentIn (Metric.ball p ε \ γ.trace) x =
        connectedComponentIn (Metric.ball p ε \ γ.trace) z ∨
      connectedComponentIn (Metric.ball p ε \ γ.trace) y =
        connectedComponentIn (Metric.ball p ε \ γ.trace) z := by
  have hKV : closure S.V ⊆ Metric.closedBall p ε := closure_V_subset_closedBall S hsub hV
  have hKVcompact : IsCompact (closure S.V) :=
    (isCompact_closedBall p ε).of_isClosed_subset isClosed_closure hKV
  have hKc : IsPreconnected (closure S.V)ᶜ := by
    rw [← U_eq_compl_closure_V S]; exact S.preconn_U
  have hInt : closure S.V ∩ (Metric.ball p ε)ᶜ = γ.trace ∩ (Metric.ball p ε)ᶜ := by
    apply Subset.antisymm
    · rintro z ⟨hzcl, hzB⟩
      rw [closure_eq_self_union_frontier, frontier_V_eq_trace S] at hzcl
      rcases hzcl with h | h
      · exact absurd (hV h) hzB
      · exact ⟨h, hzB⟩
    · rintro z ⟨hzt, hzB⟩
      exact ⟨trace_subset_closure_V S hzt, hzB⟩
  have hBpre : IsPreconnected (Metric.ball p ε \ closure S.V) :=
    isPreconnected_ball_sdiff_of_isCompact_of_compl hKVcompact hKc hKV (by rw [hInt]; exact hZ)
  -- the two preconnected pieces
  have hAc : S.V ⊆ (γ.trace ∪ (Metric.ball p ε)ᶜ)ᶜ := by
    intro z hzV
    rw [Set.mem_compl_iff, Set.mem_union]
    rintro (h | h)
    · have h1 : z ∈ S.U ∪ S.V := Or.inr hzV
      rw [S.union_eq] at h1
      exact h1 h
    · exact h (hV hzV)
  have hBc : (Metric.ball p ε \ closure S.V) ⊆ (γ.trace ∪ (Metric.ball p ε)ᶜ)ᶜ := by
    rintro z ⟨hzB, hzcl⟩
    rw [Set.mem_compl_iff, Set.mem_union]
    rintro (h | h)
    · exact hzcl (trace_subset_closure_V S h)
    · exact h hzB
  have hcover : (γ.trace ∪ (Metric.ball p ε)ᶜ)ᶜ ⊆ S.V ∪ (Metric.ball p ε \ closure S.V) := by
    intro z hz
    rw [Set.mem_compl_iff, Set.mem_union, not_or] at hz
    obtain ⟨hzT, hzBc⟩ := hz
    have hzB : z ∈ Metric.ball p ε := by
      by_contra h
      exact hzBc (by simpa only [Set.mem_compl_iff] using h)
    have hzUV : z ∈ S.U ∪ S.V := by
      rw [S.union_eq]; exact hzT
    rcases hzUV with hU | hV'
    · refine Or.inr ⟨hzB, ?_⟩
      rw [U_eq_compl_closure_V S] at hU
      exact hU
    · exact Or.inl hV'
  have hunion : (γ.trace ∪ (Metric.ball p ε)ᶜ)ᶜ = S.V ∪ (Metric.ball p ε \ closure S.V) :=
    Subset.antisymm hcover (Set.union_subset hAc hBc)
  have hTeq : (γ.trace ∪ (Metric.ball p ε)ᶜ)ᶜ = Metric.ball p ε \ γ.trace := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_union, not_or, Set.mem_sdiff, not_not]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h2, h1⟩
  intro x y z hx hy hz
  have hx' : x ∈ (γ.trace ∪ (Metric.ball p ε)ᶜ)ᶜ := by rw [hTeq]; exact hx
  have hy' : y ∈ (γ.trace ∪ (Metric.ball p ε)ᶜ)ᶜ := by rw [hTeq]; exact hy
  have hz' : z ∈ (γ.trace ∪ (Metric.ball p ε)ᶜ)ᶜ := by rw [hTeq]; exact hz
  rcases atMostTwo_of_union_of_two_preconnected hunion S.preconn_V hBpre hAc hBc hx' hy' hz'
    with h | h | h
  · exact Or.inl (by rw [hTeq] at h; exact h)
  · exact Or.inr (Or.inl (by rw [hTeq] at h; exact h))
  · exact Or.inr (Or.inr (by rw [hTeq] at h; exact h))

end

end Work.SphereJordan
