import Mathlib
import Submission.Work.SphereJordan.ladder_walk

/-!
# The trace of the ladder walk

The trace of the ladder walk built in `ladder_walk.lean` lies in `U`, provided the balls of radius
`δ` around the ladder points `g (t k)` lie in `U` and the mesh is small enough (`16 * c ≤ δ`).
-/

namespace Work.SphereJordan

open Set Metric
open Work.Smooth.JordanSeparation

noncomputable section

variable {lad : ℕ → ℤ × ℤ} {N : ℕ}
variable {g : unitInterval → ℂ} {t : ℕ → unitInterval} {c δ : ℝ}

/-- The endpoint of the `m`-th edge is still close to the `m`-th ladder point. -/
theorem ladderWalk_pt_succ_le (hc : 0 < c) (hlad : ∀ k ≤ N, lad k = snap (g (t k) / (c : ℂ)))
    (hgstep : ∀ k ≤ N, dist (g (t k)) (g (t (k + 1))) ≤ c)
    {hq : ∀ k ≤ N, |(dl lad k).1| ≤ 6 ∧ |(dl lad k).2| ≤ 6}
    {hp1 : ∀ k ≤ N, (dl lad k).1.natAbs % 2 = 0}
    {hp2 : ∀ k ≤ N, (dl lad k).2.natAbs % 2 = 0}
    {hclosed : lad N = lad 0} {m : ℕ} (hm : m < 12 * N) :
    ‖(ladderWalk N c hc lad hq hp1 hp2 hclosed).pt (m + 1) - g (t (bo m).1)‖ ≤ 16 * c := by
  have hm1 : m + 1 ≤ 12 * N := hm
  have h1 := ladderWalk_pt_le (lad := lad) (N := N) (g := g) (t := t) hc hlad
    (hq := hq) (hp1 := hp1) (hp2 := hp2) (hclosed := hclosed) (m := m + 1) hm1
  have hk : (bo m).1 ≤ N := bo_fst_le_of_le m N (le_of_lt hm)
  have hk1 : (bo (m + 1)).1 ≤ N := bo_fst_le_of_le (m + 1) N hm1
  have hstep : dist (g (t (bo m).1)) (g (t (bo (m + 1)).1)) ≤ c := by
    rcases bo_succ_fst m with h | h
    · rw [h, dist_self]; exact le_of_lt hc
    · rw [h]
      exact hgstep _ hk
  calc ‖(ladderWalk N c hc lad hq hp1 hp2 hclosed).pt (m + 1) - g (t (bo m).1)‖
      ≤ ‖(ladderWalk N c hc lad hq hp1 hp2 hclosed).pt (m + 1) - g (t (bo (m + 1)).1)‖
        + ‖g (t (bo (m + 1)).1) - g (t (bo m).1)‖ := by
        rw [show (ladderWalk N c hc lad hq hp1 hp2 hclosed).pt (m + 1) - g (t (bo m).1)
            = ((ladderWalk N c hc lad hq hp1 hp2 hclosed).pt (m + 1) - g (t (bo (m + 1)).1))
              + (g (t (bo (m + 1)).1) - g (t (bo m).1)) from by ring]
        exact norm_add_le _ _
    _ ≤ 15 * c + c := by
        have : ‖g (t (bo (m + 1)).1) - g (t (bo m).1)‖ ≤ c := by
          rw [← dist_eq_norm]; rw [dist_comm]; exact hstep
        linarith
    _ = 16 * c := by ring

/-- **The trace of the ladder walk lies in `U`.** -/
theorem ladderWalk_trace (hc : 0 < c) (hcle : 16 * c < δ) {U : Set ℂ}
    (hlad : ∀ k ≤ N, lad k = snap (g (t k) / (c : ℂ)))
    (hgstep : ∀ k ≤ N, dist (g (t k)) (g (t (k + 1))) ≤ c)
    (hball : ∀ k ≤ N, Metric.ball (g (t k)) δ ⊆ U)
    {hq : ∀ k ≤ N, |(dl lad k).1| ≤ 6 ∧ |(dl lad k).2| ≤ 6}
    {hp1 : ∀ k ≤ N, (dl lad k).1.natAbs % 2 = 0}
    {hp2 : ∀ k ≤ N, (dl lad k).2.natAbs % 2 = 0}
    {hclosed : lad N = lad 0} :
    ∀ s, (ladderWalk N c hc lad hq hp1 hp2 hclosed).path s ∈ U := by
  intro s
  have hmem : (ladderWalk N c hc lad hq hp1 hp2 hclosed).path s
      ∈ Set.range (ladderWalk N c hc lad hq hp1 hp2 hclosed).path := ⟨s, rfl⟩
  rw [LWalk.range_path] at hmem
  rcases hmem with hmem | hmem
  · rw [Set.mem_iUnion] at hmem
    obtain ⟨k, hmem⟩ := hmem
    rw [Set.mem_iUnion] at hmem
    obtain ⟨hk, hmem⟩ := hmem
    rw [Set.mem_range] at hmem
    obtain ⟨u, hu⟩ := hmem
    rw [← hu]
    have hk' : k ≤ 12 * N := le_of_lt hk
    refine hball ((bo k).1) (bo_fst_le_of_le k N hk') ?_
    have ha : (ladderWalk N c hc lad hq hp1 hp2 hclosed).pt k
        ∈ Metric.ball (g (t (bo k).1)) δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h := ladderWalk_pt_le (lad := lad) (N := N) (g := g) (t := t) hc hlad
        (hq := hq) (hp1 := hp1) (hp2 := hp2) (hclosed := hclosed) (m := k) hk'
      linarith
    have hb : (ladderWalk N c hc lad hq hp1 hp2 hclosed).pt (k + 1)
        ∈ Metric.ball (g (t (bo k).1)) δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h := ladderWalk_pt_succ_le (lad := lad) (N := N) (g := g) (t := t) hc hlad hgstep
        (hq := hq) (hp1 := hp1) (hp2 := hp2) (hclosed := hclosed) (m := k) hk
      linarith
    exact (convex_ball _ _).segment_subset ha hb (by
      rw [← Path.range_segment]; exact ⟨u, rfl⟩)
  · rw [Set.mem_singleton_iff] at hmem
    rw [hmem]
    have h := ladderV_zero lad
    have hpt : (ladderWalk N c hc lad hq hp1 hp2 hclosed).pt 0 = c * gpt (lad 0) := by
      show c * gpt (ladderV lad 0) = c * gpt (lad 0)
      rw [h]
    rw [hpt]
    exact hball 0 (Nat.zero_le N) (by
      rw [Metric.mem_ball, dist_eq_norm]
      have h2 := ladderWalk_pt_le (lad := lad) (N := N) (g := g) (t := t) hc hlad
        (hq := hq) (hp1 := hp1) (hp2 := hp2) (hclosed := hclosed) (m := 0) (Nat.zero_le _)
      rw [bo_zero] at h2
      rw [hpt] at h2
      linarith)

end

end Work.SphereJordan
