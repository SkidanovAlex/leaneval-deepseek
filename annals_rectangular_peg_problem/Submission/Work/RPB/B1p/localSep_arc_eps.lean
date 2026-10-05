import Mathlib
import Submission.Work.RPB.Port.Drive.SeparationBase
import Submission.Work.RPB.Port.Drive.curve_straightening
import Submission.Work.RPB.Port.Drive.curve_localSep
import Submission.Work.RPB.B1p.arc_cover_Icc_gen

namespace Work.RPB.B1p

open Set Metric
open scoped Topology

/-- Membership in the ball of radius `ρ` around the origin of `ℝ × ℝ` (which carries the
supremum norm) in coordinates. -/
private lemma mem_ball_zero_prod_iff {ρ : ℝ} {z : ℝ × ℝ} :
    z ∈ Metric.ball (0 : ℝ × ℝ) ρ ↔ |z.1| < ρ ∧ |z.2| < ρ := by
  rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs,
    max_lt_iff]

/-- The distance of `(x.1, c)` from `(x.1, 0)` is `|c|`. -/
private lemma dist_mk_fst (x : ℝ × ℝ) (c : ℝ) : dist (x.1, c) (x.1, 0) = |c| := by
  simp [Prod.dist_eq]

/-- Local separation of the image of a smooth arc `G '' [a,b]` at an interior regular point:
there is an arbitrarily small neighbourhood of `G s₀` that the arc splits into two nonempty open
path connected pieces, each accumulating at every point of `arc ∩ U`.

This is the arc version of `Work.RPB.Port.Drive.curve_localSep`; the proof is the same
straighten-the-curve argument, with the compactness input supplied by
`Work.RPB.B1p.arc_cover_Icc_gen` instead of the periodic `curve_arc_cover`. -/
theorem localSep_arc_eps {G : ℝ → ℝ × ℝ} (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) {a b s₀ : ℝ}
    (ha : a < s₀) (hb : s₀ < b) (hinj : Set.InjOn G (Set.Icc a b)) (hder : deriv G s₀ ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U U₁ U₂ : Set (ℝ × ℝ), Work.RPB.Port.Drive.LocalSep (G '' Set.Icc a b) U U₁ U₂ ∧
      G s₀ ∈ U ∧ U ⊆ Metric.ball (G s₀) ε := by
  -- reparametrise the arc so that its base point sits at parameter `0`
  set Gs : ℝ → ℝ × ℝ := fun t => G (s₀ + t) with hGsdef
  have hGs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Gs := by
    rw [hGsdef]
    exact hG.comp (by fun_prop)
  have hGs0 : Gs 0 = G s₀ := by simp [hGsdef]
  have hGsder : deriv Gs 0 ≠ 0 := by
    have h : deriv Gs 0 = deriv G s₀ := by
      rw [hGsdef, deriv_comp_const_add, add_zero]
    rwa [h]
  -- straightening of the reparametrised curve at the origin
  obtain ⟨r, Φ, hrpos, hsrc, hΦ⟩ :=
    Work.RPB.Port.Drive.curve_straightening Gs hGs hGsder
  -- the straightening map
  set H : ℝ × ℝ → ℝ × ℝ :=
    fun z => Gs z.1 + z.2 • Work.RPB.Port.Drive.rot90 (deriv Gs 0) with hHdef
  have hHpair : ∀ c d : ℝ, H (c, d) = Gs c + d • Work.RPB.Port.Drive.rot90 (deriv Gs 0) := by
    intro c d
    simp only [hHdef]
  have hHcont : Continuous H := by
    rw [hHdef]
    exact (hGs.continuous.comp continuous_fst).add (continuous_snd.smul continuous_const)
  have hH0 : H 0 = G s₀ := by
    rw [show (0 : ℝ × ℝ) = (0, 0) from rfl, hHpair 0 0, zero_smul, add_zero, hGs0]
  have hHΦ : ∀ z : ℝ × ℝ, Φ z = H z := by
    intro z
    simp only [hHdef]
    exact hΦ z
  -- the compactness input: points of the arc close to `G s₀` have parameters close to `s₀`
  have hr2pos : 0 < r / 2 := by linarith
  obtain ⟨η, hηpos, hη⟩ := arc_cover_Icc_gen (G := G) hG.continuous ha hb hinj hr2pos
  -- shrink so that the straightening sends a ball into the `η`-ball around `G s₀`
  have hballH : Metric.ball (H 0) (min η ε) ∈ 𝓝 (H 0) :=
    Metric.ball_mem_nhds _ (lt_min hηpos hε)
  have hpre : H ⁻¹' Metric.ball (H 0) (min η ε) ∈ 𝓝 (0 : ℝ × ℝ) :=
    hHcont.continuousAt.preimage_mem_nhds hballH
  rw [hH0] at hpre
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.mem_nhds_iff.mp hpre
  -- the radius of the straightened ball
  set ρ' : ℝ := min (min ρ (r / 2)) (min (s₀ - a) (b - s₀)) with hρ'def
  have hρ'pos : 0 < ρ' := by
    rw [hρ'def]
    exact lt_min (lt_min hρpos hr2pos) (lt_min (by linarith) (by linarith))
  have hρ'ρ : ρ' ≤ ρ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρ'r : ρ' ≤ r / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρ'a : ρ' ≤ s₀ - a := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ'b : ρ' ≤ b - s₀ := le_trans (min_le_right _ _) (min_le_right _ _)
  set B : Set (ℝ × ℝ) := Metric.ball (0 : ℝ × ℝ) ρ' with hBdef
  have hBopen : IsOpen B := by rw [hBdef]; exact Metric.isOpen_ball
  have hBsub : B ⊆ Φ.source := by
    intro z hz
    apply hsrc
    rw [Metric.mem_ball, dist_zero_right]
    rw [hBdef, Metric.mem_ball, dist_zero_right] at hz
    linarith
  have hHB : H '' B ⊆ Metric.ball (G s₀) (min η ε) := by
    rintro _ ⟨z, hz, rfl⟩
    exact hρsub (by
      rw [Metric.mem_ball, dist_zero_right]
      rw [hBdef, Metric.mem_ball, dist_zero_right] at hz
      linarith)
  have hHBeps : H '' B ⊆ Metric.ball (G s₀) ε :=
    fun z hz => Metric.ball_subset_ball (min_le_right _ _) (hHB hz)
  -- injectivity of the straightening on its source
  have hinjH : Set.InjOn H Φ.source := by
    intro z hz z' hz' h
    exact Φ.injOn hz hz' (by rw [hHΦ z, hHΦ z', h])
  -- **the key point**: the arc meets the straightened ball only where the normal coordinate vanishes
  have key : ∀ z ∈ B, z.2 ≠ 0 → H z ∉ G '' Set.Icc a b := by
    intro z hzB hz2 hmem
    obtain ⟨t, htI, htG⟩ := hmem
    have hmem' : dist (H z) (G s₀) < min η ε :=
      Metric.mem_ball.mp (hHB ⟨z, hzB, rfl⟩)
    have hdist : dist (G t) (G s₀) < η := by
      rw [htG]
      exact lt_of_lt_of_le hmem' (min_le_left η ε)
    have htδ : dist t s₀ < r / 2 := hη t htI hdist
    have hsrc1 : (t - s₀, (0 : ℝ)) ∈ Φ.source := by
      apply hsrc
      rw [Metric.mem_ball, dist_zero_right]
      have h1 : ‖((t - s₀, (0 : ℝ)) : ℝ × ℝ)‖ = |t - s₀| := by
        simp [Prod.norm_def, Real.norm_eq_abs]
      rw [h1]
      have h2 : |t - s₀| = dist t s₀ := by simp [Real.dist_eq]
      rw [h2]
      linarith
    have heq : (t - s₀, (0 : ℝ)) = z := by
      refine hinjH hsrc1 (hBsub hzB) ?_
      rw [hHpair (t - s₀) 0, zero_smul, add_zero]
      have h1 : Gs (t - s₀) = G t := by
        simp only [hGsdef]
        have : s₀ + (t - s₀) = t := by ring
        rw [this]
      rw [h1, htG]
    exact hz2 (by rw [← heq])
  -- the two pieces: the two sides of the straightened ball
  set P : Set (ℝ × ℝ) := {z : ℝ × ℝ | 0 < z.2} with hPdef
  set Q : Set (ℝ × ℝ) := {z : ℝ × ℝ | z.2 < 0} with hQdef
  set U : Set (ℝ × ℝ) := H '' B with hUdef
  set U₁ : Set (ℝ × ℝ) := H '' (B ∩ P) with hU₁def
  set U₂ : Set (ℝ × ℝ) := H '' (B ∩ Q) with hU₂def
  have himg : ∀ S : Set (ℝ × ℝ), H '' S = Φ '' S := by
    intro S
    exact Set.image_congr (fun z _ => (hHΦ z).symm)
  have hPopen : IsOpen P := by rw [hPdef]; exact isOpen_lt continuous_const continuous_snd
  have hQopen : IsOpen Q := by rw [hQdef]; exact isOpen_lt continuous_snd continuous_const
  have hPconv : Convex ℝ P := by
    have h : P = (Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ) := by rw [hPdef]; ext z; simp
    rw [h]; exact convex_univ.prod (convex_Ioi 0)
  have hQconv : Convex ℝ Q := by
    have h : Q = (Set.univ : Set ℝ) ×ˢ Set.Iio (0 : ℝ) := by rw [hQdef]; ext z; simp
    rw [h]; exact convex_univ.prod (convex_Iio 0)
  have hsubP : B ∩ P ⊆ Φ.source := fun z hz => hBsub hz.1
  have hsubQ : B ∩ Q ⊆ Φ.source := fun z hz => hBsub hz.1
  have hUopen : IsOpen U := by
    rw [hUdef, himg B]
    exact Φ.isOpen_image_of_subset_source hBopen hBsub
  have hU₁open : IsOpen U₁ := by
    rw [hU₁def, himg (B ∩ P)]
    exact Φ.isOpen_image_of_subset_source (hBopen.inter hPopen) hsubP
  have hU₂open : IsOpen U₂ := by
    rw [hU₂def, himg (B ∩ Q)]
    exact Φ.isOpen_image_of_subset_source (hBopen.inter hQopen) hsubQ
  have hpc₁ : IsPathConnected U₁ := by
    rw [hU₁def]
    refine IsPathConnected.image ?_ hHcont
    have hconv : Convex ℝ (B ∩ P) := by
      rw [hBdef]
      exact (convex_ball (0 : ℝ × ℝ) ρ').inter hPconv
    refine hconv.isPathConnected ⟨(0, ρ' / 2), ?_, ?_⟩
    · rw [mem_ball_zero_prod_iff]
      exact ⟨by simp; linarith,
        by rw [abs_of_pos (by linarith : (0 : ℝ) < ρ' / 2)]; linarith⟩
    · show (0 : ℝ) < ρ' / 2
      linarith
  have hpc₂ : IsPathConnected U₂ := by
    rw [hU₂def]
    refine IsPathConnected.image ?_ hHcont
    have hconv : Convex ℝ (B ∩ Q) := by
      rw [hBdef]
      exact (convex_ball (0 : ℝ × ℝ) ρ').inter hQconv
    refine hconv.isPathConnected ⟨(0, -ρ' / 2), ?_, ?_⟩
    · rw [mem_ball_zero_prod_iff]
      exact ⟨by simp; linarith,
        by rw [abs_of_neg (by linarith : -ρ' / 2 < (0 : ℝ))]; linarith⟩
    · show (-ρ' / 2 : ℝ) < 0
      linarith
  have hdisj : Disjoint U₁ U₂ := by
    rw [Set.disjoint_left]
    intro y hy₁ hy₂
    obtain ⟨z, ⟨hzB, hzP⟩, rfl⟩ := hy₁
    obtain ⟨z', ⟨hz'B, hz'Q⟩, hz'⟩ := hy₂
    have hzz' : z' = z := hinjH (hBsub hz'B) (hBsub hzB) hz'
    subst hzz'
    rw [hPdef] at hzP
    rw [hQdef] at hz'Q
    simp only [Set.mem_ofPred_eq] at hzP hz'Q
    linarith
  have hunion : U₁ ∪ U₂ = U \ G '' Set.Icc a b := by
    apply Set.Subset.antisymm
    · intro y hy
      rcases hy with hy | hy
      · obtain ⟨z, ⟨hzB, hzP⟩, rfl⟩ := hy
        rw [hPdef] at hzP
        simp only [Set.mem_ofPred_eq] at hzP
        exact ⟨⟨z, hzB, rfl⟩, key z hzB (ne_of_gt hzP)⟩
      · obtain ⟨z, ⟨hzB, hzQ⟩, rfl⟩ := hy
        rw [hQdef] at hzQ
        simp only [Set.mem_ofPred_eq] at hzQ
        exact ⟨⟨z, hzB, rfl⟩, key z hzB (ne_of_lt hzQ)⟩
    · rintro y ⟨⟨z, hzB, rfl⟩, hyK⟩
      have hz1 : |z.1| < ρ' := (mem_ball_zero_prod_iff.mp hzB).1
      have hzmem : s₀ + z.1 ∈ Set.Icc a b := by
        have h1 : |z.1| < s₀ - a := lt_of_lt_of_le hz1 hρ'a
        have h2 : |z.1| < b - s₀ := lt_of_lt_of_le hz1 hρ'b
        rw [Set.mem_Icc]
        exact ⟨by have := (abs_lt.mp h1).1; linarith, by have := (abs_lt.mp h2).2; linarith⟩
      have hz2 : z.2 ≠ 0 := by
        intro h2
        refine hyK ?_
        have hHeq : H z = G (s₀ + z.1) := by
          have hz : z = (z.1, (0 : ℝ)) := Prod.ext rfl h2
          rw [hz, hHpair z.1 0, zero_smul, add_zero]
        rw [hHeq]
        exact ⟨s₀ + z.1, hzmem, rfl⟩
      rcases lt_or_gt_of_ne hz2 with h | h
      · refine Or.inr ⟨z, ⟨hzB, ?_⟩, rfl⟩
        rw [hQdef]; exact h
      · refine Or.inl ⟨z, ⟨hzB, ?_⟩, rfl⟩
        rw [hPdef]; exact h
  -- every point of `U ∩ arc` is a limit of points of each piece
  have acc₁ : ∀ q ∈ U ∩ G '' Set.Icc a b, q ∈ closure U₁ := by
    rintro q ⟨⟨x, hxB, rfl⟩, hqK⟩
    have hx2 : x.2 = 0 := by
      by_contra h
      exact key x hxB h hqK
    have hxnorm : ‖x‖ < ρ' := by
      have h := hxB
      rw [hBdef, Metric.mem_ball, dist_zero_right] at h
      exact h
    have hxeq : H x = H (x.1, 0) := by
      congr 1
      exact Prod.ext rfl hx2
    rw [Metric.mem_closure_iff]
    intro ε' hε'
    have hpre' : H ⁻¹' Metric.ball (H (x.1, 0)) ε' ∈ 𝓝 (x.1, 0) :=
      hHcont.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε')
    obtain ⟨ν, hνpos, hνsub⟩ := Metric.mem_nhds_iff.mp hpre'
    set τ : ℝ := min (ν / 2) ((ρ' - ‖x‖) / 2) with hτdef
    have hτpos : 0 < τ := lt_min (by linarith) (by linarith)
    have hτν : τ < ν := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hτρ : τ < ρ' - ‖x‖ := by
      have h1 : τ ≤ (ρ' - ‖x‖) / 2 := min_le_right _ _
      linarith
    have hfst : |x.1| ≤ ‖x‖ := by
      rw [Prod.norm_def, Real.norm_eq_abs]; exact le_max_left _ _
    refine ⟨H (x.1, τ), ⟨(x.1, τ), ⟨?_, ?_⟩, rfl⟩, ?_⟩
    · rw [mem_ball_zero_prod_iff]
      exact ⟨lt_of_le_of_lt hfst hxnorm,
        by rw [abs_of_pos hτpos]; linarith [norm_nonneg x]⟩
    · show (0 : ℝ) < τ
      exact hτpos
    · have hdist : dist ((x.1), τ) ((x.1), (0 : ℝ)) < ν := by
        rw [dist_mk_fst, abs_of_pos hτpos]
        exact hτν
      have h1 : dist (H (x.1, 0)) (H (x.1, τ)) < ε' := by
        rw [dist_comm]
        exact hνsub hdist
      rw [hxeq]
      exact h1
  have acc₂ : ∀ q ∈ U ∩ G '' Set.Icc a b, q ∈ closure U₂ := by
    rintro q ⟨⟨x, hxB, rfl⟩, hqK⟩
    have hx2 : x.2 = 0 := by
      by_contra h
      exact key x hxB h hqK
    have hxnorm : ‖x‖ < ρ' := by
      have h := hxB
      rw [hBdef, Metric.mem_ball, dist_zero_right] at h
      exact h
    have hxeq : H x = H (x.1, 0) := by
      congr 1
      exact Prod.ext rfl hx2
    rw [Metric.mem_closure_iff]
    intro ε' hε'
    have hpre' : H ⁻¹' Metric.ball (H (x.1, 0)) ε' ∈ 𝓝 (x.1, 0) :=
      hHcont.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hε')
    obtain ⟨ν, hνpos, hνsub⟩ := Metric.mem_nhds_iff.mp hpre'
    set τ : ℝ := min (ν / 2) ((ρ' - ‖x‖) / 2) with hτdef
    have hτpos : 0 < τ := lt_min (by linarith) (by linarith)
    have hτν : τ < ν := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hτρ : τ < ρ' - ‖x‖ := by
      have h1 : τ ≤ (ρ' - ‖x‖) / 2 := min_le_right _ _
      linarith
    have hfst : |x.1| ≤ ‖x‖ := by
      rw [Prod.norm_def, Real.norm_eq_abs]; exact le_max_left _ _
    refine ⟨H (x.1, -τ), ⟨(x.1, -τ), ⟨?_, ?_⟩, rfl⟩, ?_⟩
    · rw [mem_ball_zero_prod_iff]
      exact ⟨lt_of_le_of_lt hfst hxnorm,
        by rw [abs_of_neg (by linarith : -τ < (0 : ℝ))]; linarith [norm_nonneg x]⟩
    · show (-τ : ℝ) < 0
      linarith
    · have hdist : dist ((x.1), -τ) ((x.1), (0 : ℝ)) < ν := by
        rw [dist_mk_fst, abs_of_neg (by linarith : -τ < (0 : ℝ))]
        linarith
      have h1 : dist (H (x.1, 0)) (H (x.1, -τ)) < ε' := by
        rw [dist_comm]
        exact hνsub hdist
      rw [hxeq]
      exact h1
  refine ⟨U, U₁, U₂, ⟨hUopen, hU₁open, hU₂open, hpc₁, hpc₂, hdisj, hunion, acc₁, acc₂⟩, ?_, ?_⟩
  · exact ⟨0, by rw [hBdef, Metric.mem_ball, dist_zero_right, norm_zero]; exact hρ'pos, hH0⟩
  · exact fun z hz => hHBeps hz

end Work.RPB.B1p
