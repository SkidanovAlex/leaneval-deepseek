import Mathlib

namespace Work.WilG4c

/-- The grid points `j/20`, `j < 16`, cover `(0,1)` by the intervals `(j/20 - 1/4, j/20)`
i.e. every `t ∈ (0,1)` lies above some grid point `c ≤ 3/4` and below `c + 1/4`.

This is the scalar `16`-point covering input: the largest grid point below `t` is still within
`1/4` of `t`, because consecutive grid points are `1/20 < 1/4` apart (and the last one,
`15/20 = 3/4`, already reaches `1`). -/
theorem shiftCover16 (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ c : ℝ, c ∈ (Finset.range 16).image (fun j : ℕ => (j : ℝ) / 20) ∧
      c < t ∧ t < c + 1 / 4 ∧ c ≤ 3 / 4 := by
  classical
  -- Largest grid index whose grid point still lies strictly below `t`.
  set S : Finset ℕ := (Finset.range 16).filter (fun j : ℕ => (j : ℝ) / 20 < t) with hS
  have hne : S.Nonempty := by
    refine ⟨0, ?_⟩
    rw [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by norm_num, by simpa using ht0⟩
  let m : ℕ := S.max' hne
  have hmS : m ∈ S := Finset.max'_mem S hne
  have hmS' : m ∈ (Finset.range 16).filter (fun j : ℕ => (j : ℝ) / 20 < t) := by rwa [hS] at hmS
  obtain ⟨hmr, hmt⟩ := Finset.mem_filter.mp hmS'
  have hm16 : m < 16 := Finset.mem_range.mp hmr
  -- `m` is the maximum of `S`.
  have key : ∀ x ∈ S, x ≤ m := by
    intro x hx
    have := Finset.le_max' S x hx
    simpa [m] using this
  refine ⟨(m : ℝ) / 20, ?_, hmt, ?_, ?_⟩
  · rw [Finset.mem_image]
    exact ⟨m, hmr, rfl⟩
  · -- `t < m/20 + 1/4`: otherwise `m + 1` would also lie in `S`, contradicting maximality.
    by_contra hcon
    rw [not_lt] at hcon
    have hmle : m ≤ 15 := by omega
    rcases lt_or_eq_of_le hmle with hlt | heq
    · have hmem : m + 1 ∈ S := by
        rw [hS, Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        have hc : ((m + 1 : ℕ) : ℝ) / 20 = (m : ℝ) / 20 + 1 / 20 := by push_cast; ring
        rw [hc]
        linarith
      have hle := key (m + 1) hmem
      omega
    · rw [heq] at hcon
      have h1 : ((15 : ℕ) : ℝ) / 20 + 1 / 4 = 1 := by norm_num
      linarith
  · have hmle : m ≤ 15 := by omega
    have hmle' : (m : ℝ) ≤ 15 := by exact_mod_cast hmle
    linarith

end Work.WilG4c
