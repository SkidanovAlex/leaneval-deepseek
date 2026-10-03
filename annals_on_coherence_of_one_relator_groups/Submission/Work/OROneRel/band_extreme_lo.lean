import Mathlib
import Submission.Work.OROneRel.gauge_walk_defs
import Submission.Work.OROneRel.winBandDefs

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **The source level of a decorated letter is a running level of the walk.**  The source levels of
the decorated letters are the levels `(running c i L).dropLast`, hence in particular running levels
(`gauge_walk_defs`). -/
theorem coverSrc_mem_running {c : α → ℤ} {i : ℤ} {L : List (α × Bool)}
    {p : (α × ℤ) × Bool} (hp : p ∈ decor c i L) : coverSrc c p ∈ running c i L := by
  have h : coverSrc c p ∈ (decor c i L).map (coverSrc c) := List.mem_map.mpr ⟨p, hp, rfl⟩
  rw [decor_map_coverSrc] at h
  exact List.mem_of_mem_dropLast h

/-- **The target level of a decorated letter is a running level of the walk.**  The target levels of
the decorated letters are the levels `(running c i L).tail`. -/
theorem coverTgt_mem_running {c : α → ℤ} {i : ℤ} {L : List (α × Bool)}
    {p : (α × ℤ) × Bool} (hp : p ∈ decor c i L) : coverTgt c p ∈ running c i L := by
  have h : coverTgt c p ∈ (decor c i L).map (coverTgt c) := List.mem_map.mpr ⟨p, hp, rfl⟩
  rw [decor_map_coverTgt] at h
  exact List.mem_of_mem_tail h

/-- **Both endpoints of the edge of a decorated letter, read from its decoration level, are running
levels.**  The decoration level `p.1.2` of a decorated letter is its source (positive letter) or its
target (negative letter), and `p.1.2 + c p.1.1` is the other one, so both lie in the walk. -/
theorem decor_level_mem_running {c : α → ℤ} {i : ℤ} {L : List (α × Bool)}
    {p : (α × ℤ) × Bool} (hp : p ∈ decor c i L) :
    p.1.2 ∈ running c i L ∧ p.1.2 + c p.1.1 ∈ running c i L := by
  obtain ⟨⟨x, j⟩, b⟩ := p
  cases b
  · exact ⟨by simpa [coverTgt] using coverTgt_mem_running (c := c) (i := i) hp,
      by simpa [coverSrc] using coverSrc_mem_running (c := c) (i := i) hp⟩
  · exact ⟨by simpa [coverSrc] using coverSrc_mem_running (c := c) (i := i) hp,
      by simpa [coverTgt] using coverTgt_mem_running (c := c) (i := i) hp⟩

/-- If the walk of `w` fits in the window `[lo,hi]` and no non-zero translate of it does, then the
bottom level `lo` is a running level of the walk. -/
theorem band_extreme_lo {α : Type u} {c : α → ℤ} {lo hi : ℤ} {w : List (α × Bool)}
    (hwin : ∀ p ∈ decor c 0 w, coverEdge p ∈ winE c lo hi)
    (hone : ∀ k : ℤ, k ≠ 0 → ¬ (∀ p ∈ decor c 0 w,
      lo ≤ p.1.2 + k ∧ lo ≤ p.1.2 + c p.1.1 + k ∧ p.1.2 + k ≤ hi ∧
        p.1.2 + c p.1.1 + k ≤ hi)) :
    lo ∈ running c 0 w := by
  classical
  by_contra hlo
  -- Shifting the walk down by one keeps it inside `[lo,hi]`, because no level is as low as `lo`.
  refine hone (-1) (by norm_num) (fun p hp => ?_)
  obtain ⟨hm1, hm2⟩ := decor_level_mem_running (c := c) (i := 0) hp
  have hb : lo ≤ p.1.2 ∧ p.1.2 ≤ hi ∧ lo ≤ p.1.2 + c p.1.1 ∧ p.1.2 + c p.1.1 ≤ hi := by
    simpa [mem_winE, coverEdge] using hwin p hp
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  have key1 : lo + 1 ≤ p.1.2 := by
    have hne : p.1.2 ≠ lo := fun h => hlo (h ▸ hm1)
    omega
  have key2 : lo + 1 ≤ p.1.2 + c p.1.1 := by
    have hne : p.1.2 + c p.1.1 ≠ lo := fun h => hlo (h ▸ hm2)
    omega
  exact ⟨by omega, by omega, by omega, by omega⟩

end Work.OROneRel
