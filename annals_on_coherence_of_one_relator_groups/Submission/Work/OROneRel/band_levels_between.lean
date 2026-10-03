import Mathlib
import Submission.Work.OROneRel.gauge_walk_defs
import Submission.Work.OROneRel.winBandDefs
import Submission.Work.OROneRel.band_of_winE_decor

namespace Work.OROneRel

universe u

/-- **The running levels are the levels of the prefixes.**  Every entry of `running c i L` is
`i + lsig c (L.take k)` for some `k ≤ L.length`: the walk started at the level `i` visits exactly the
levels reached after reading a prefix of `L`. -/
theorem exists_lsig_take_of_mem_running {α : Type u} (c : α → ℤ) (L : List (α × Bool)) :
    ∀ (i v : ℤ), v ∈ running c i L → ∃ k ≤ L.length, i + lsig c (L.take k) = v := by
  induction L with
  | nil =>
      intro i v hv
      rw [running_nil', List.mem_singleton] at hv
      exact ⟨0, le_refl 0, by rw [hv, List.take_nil, lsig_nil', add_zero]⟩
  | cons p L ih =>
      intro i v hv
      rw [running_cons', List.mem_cons] at hv
      rcases hv with hv | hv
      · exact ⟨0, Nat.zero_le _, by rw [hv, List.take_zero, lsig_nil', add_zero]⟩
      · obtain ⟨k, hk, hk'⟩ := ih (i + linc c p) v hv
        refine ⟨k + 1, by simp only [List.length_cons]; omega, ?_⟩
        rw [List.take_succ_cons, lsig_cons']
        rw [show i + (linc c p + lsig c (L.take k)) = (i + linc c p) + lsig c (L.take k)
            from by ring]
        exact hk'

/-- If every edge of the decorated walk `decor c 0 w` lies in the window `winE c lo hi` and the word
is nonempty, then every level of the running-level list `running c 0 w` lies in `[lo,hi]`. -/
theorem band_levels_between {α : Type u} {c : α → ℤ} {lo hi : ℤ} {w : List (α × Bool)}
    (hwin : ∀ p ∈ decor c 0 w, coverEdge p ∈ winE c lo hi) (hwne : w ≠ []) :
    ∀ l ∈ running c 0 w, lo ≤ l ∧ l ≤ hi := by
  -- the walk of `w` lies in the band `[lo,hi]` at the level of every prefix
  have hband : ∀ k : ℕ, k ≤ w.length → lo ≤ lsig c (w.take k) ∧ lsig c (w.take k) ≤ hi :=
    band_of_winE_decor c lo hi w hwne hwin
  intro l hl
  obtain ⟨k, hk, hk'⟩ := exists_lsig_take_of_mem_running c w 0 l hl
  have hk'' : lsig c (w.take k) = l := by simpa using hk'
  rw [← hk'']
  exact hband k hk

end Work.OROneRel
