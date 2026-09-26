import Mathlib
import Submission.Commons.Analysis.RealIntervals.exists_interior_interval_of_dense_no_full

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

namespace Commons.Analysis.RealIntervals

/-- **Left-full or terminal/clean strip dichotomy**: an open subset `S` of ℝ
whose points are dense in every left-neighbourhood of a point `c ∉ S`
(`0 < c`) either contains the WHOLE interval `(0, c)`, or it contains a
clean strip `(a, b)` (`0 < a < b ≤ c`) entirely inside `S` whose endpoints
lie outside `S`.

Proof: if `(0, c) ⊆ S` we are done.  Otherwise look at the set
`M = {b | 0 ≤ b ∧ b < c ∧ (b, c) ⊆ S}` of left endpoints of full terminal
strips reaching `c`.  If `M` is empty, no such terminal strip exists at
all, and `exists_interior_interval_of_dense_no_full` provides a strip
`(a, b)` with `b < c` (whose endpoints are outside `S`).  If `M` is
nonempty, let `a := sInf M`: openness of `S` together with the defining
property of an infimum shows `(a, c) ⊆ S` (every `x > a` is above some
`b ∈ M`), `a ∉ S` (otherwise an open ball around `a` would extend a strip
`(b, c) ⊆ S` past the infimum, with `b = a − η`), and `0 < a` (if `a = 0`
then `(0, c) ⊆ S`); since `c ∉ S` by hypothesis, `(a, c)` is the desired
clean strip. -/
theorem left_full_or_strip_of_left_dense {S : Set ℝ} (hSopen : IsOpen S) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hcNot : c ∉ S)
    (hdense : ∀ ε : ℝ, 0 < ε → ∃ x : ℝ, x ∈ S ∧ c - ε < x ∧ x < c) :
    Set.Ioo (0 : ℝ) c ⊆ S ∨
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b ≤ c ∧ Set.Ioo a b ⊆ S ∧ a ∉ S ∧ b ∉ S := by
  by_cases hfull : Set.Ioo (0 : ℝ) c ⊆ S
  · exact Or.inl hfull
  · right
    let M : Set ℝ := {b : ℝ | 0 ≤ b ∧ b < c ∧ Set.Ioo b c ⊆ S}
    have hbdd : BddBelow M := ⟨0, by intro b hb; exact hb.1⟩
    by_cases hMne : M.Nonempty
    · let a : ℝ := sInf M
      have hMle : ∀ b ∈ M, a ≤ b := by
        intro b hb
        exact csInf_le hbdd hb
      have hle_a : 0 ≤ a := le_csInf hMne (by intro b hb; exact hb.1)
      have hac_lt : a < c := by
        rcases hMne with ⟨b0, hb0M⟩
        exact lt_of_le_of_lt (hMle b0 hb0M) hb0M.2.1
      have hsub_ac : Set.Ioo a c ⊆ S := by
        intro x hx
        have hxlt : sInf M < x := by simpa [a] using hx.1
        rcases (csInf_lt_iff (s := M) (a := x) hbdd hMne).mp hxlt with ⟨b, hbM, hbx⟩
        have hxbc : x ∈ Set.Ioo b c := ⟨hbx, hx.2⟩
        exact hbM.2.2 hxbc
      have hzero : a ≠ 0 := by
        intro heq
        have hsub0 : Set.Ioo (0 : ℝ) c ⊆ S := by simpa [heq] using hsub_ac
        exact hfull hsub0
      have ha_pos : 0 < a := lt_of_le_of_ne hle_a (by intro heq; exact hzero heq.symm)
      have haS_not : a ∉ S := by
        intro haS
        rcases Metric.isOpen_iff.mp hSopen a haS with ⟨ε, hε0, hball⟩
        let η : ℝ := min (ε / 2) (a / 2)
        have hη0 : 0 < η := by
          simpa [η] using (lt_min (half_pos hε0) (half_pos ha_pos))
        have hη_lt_ε : η < ε := by
          have h1 : min (ε / 2) (a / 2) < ε :=
            lt_of_le_of_lt (min_le_left (ε / 2) (a / 2)) (half_lt_self hε0)
          simpa [η] using h1
        have hη_lt_a : η < a := by
          have h1 : min (ε / 2) (a / 2) < a :=
            lt_of_le_of_lt (min_le_right (ε / 2) (a / 2)) (half_lt_self ha_pos)
          simpa [η] using h1
        let b : ℝ := a - η
        have hb_lt_a : b < a := by dsimp [b]; linarith
        have hb_ge0 : 0 ≤ b := by dsimp [b]; linarith
        have hb_lt_c : b < c := lt_trans hb_lt_a hac_lt
        have hsub_bc : Set.Ioo b c ⊆ S := by
          intro z hz
          by_cases hz_lt_a : z < a
          · have hz_ball : z ∈ Metric.ball a ε := by
              rw [Metric.mem_ball, Real.dist_eq]
              have hzn : z - a < 0 := sub_neg.mpr hz_lt_a
              rw [abs_of_neg hzn]
              have hlt1 : a - ε < z := by
                have hbe : a - ε < b := by
                  dsimp [b]
                  linarith
                exact lt_trans hbe hz.1
              linarith
            exact hball hz_ball
          · have haz : a ≤ z := le_of_not_gt hz_lt_a
            by_cases heq : z = a
            · rw [heq]
              exact haS
            · have haz_lt : a < z := lt_of_le_of_ne haz (by intro h; exact heq h.symm)
              exact hsub_ac ⟨haz_lt, hz.2⟩
        have hbM : b ∈ M := ⟨hb_ge0, hb_lt_c, hsub_bc⟩
        have ha_le_b : a ≤ b := hMle b hbM
        exact (not_le_of_gt hb_lt_a) ha_le_b
      refine ⟨a, c, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact ha_pos
      · exact hac_lt
      · exact le_rfl
      · exact hsub_ac
      · exact haS_not
      · exact hcNot
    · have hMempty : M = ∅ := Set.not_nonempty_iff_eq_empty.mp hMne
      have hnoFull : ¬ ∃ b : ℝ, b < c ∧ 0 ≤ b ∧ Set.Ioo b c ⊆ S := by
        intro h
        rcases h with ⟨b, hbc, hb0, hsub⟩
        have hbM : b ∈ M := ⟨hb0, hbc, hsub⟩
        exact (Set.mem_empty_iff_false b).mp (hMempty ▸ hbM)
      rcases exists_interior_interval_of_dense_no_full (S := S) (c := c) hSopen hc0 hdense
          hnoFull with ⟨a, b, ha0pos, hab, hbc_lt, hsub_ab, ha_nS, hb_nS⟩
      refine ⟨a, b, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact ha0pos
      · exact hab
      · exact le_of_lt hbc_lt
      · exact hsub_ab
      · exact ha_nS
      · exact hb_nS

end Commons.Analysis.RealIntervals
