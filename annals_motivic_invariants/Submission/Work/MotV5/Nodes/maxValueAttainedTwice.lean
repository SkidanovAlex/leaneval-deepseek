import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.Nodes

theorem maxValueAttainedTwice {R Γ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation R Γ) {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → R)
    (hne : ∃ i, w (u i) ≠ 0) (hsum : ∑ i, u i = 0) :
    ∃ i j : ι, i ≠ j ∧ w (u i) ≠ 0 ∧ w (u i) = w (u j) ∧
      ∀ k, w (u k) ≠ 0 → w (u k) ≤ w (u i) := by
  classical
  -- An index at which the valuation of `u` attains its (nonzero) maximum.
  obtain ⟨i₀, hi₀⟩ := hne
  have hpos : 0 < w (u i₀) := lt_of_le_of_ne (zero_le) (Ne.symm hi₀)
  obtain ⟨i, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) (fun k => w (u k))
      ⟨i₀, Finset.mem_univ i₀⟩
  have hmax' : ∀ k, w (u k) ≤ w (u i) := fun k => hmax k (Finset.mem_univ k)
  have hi : w (u i) ≠ 0 := ne_of_gt (lt_of_lt_of_le hpos (hmax' i₀))
  by_cases hsecond : ∃ j, j ≠ i ∧ w (u j) = w (u i)
  · -- the maximum is attained at a second index
    obtain ⟨j, hji, hj⟩ := hsecond
    exact ⟨i, j, Ne.symm hji, hi, hj.symm, fun k _ => hmax' k⟩
  · -- otherwise the maximum is attained only at `i`; sum the remaining terms
    exfalso
    have hsecond' : ∀ j, j ≠ i → w (u j) ≠ w (u i) := by
      intro j hj hw
      exact hsecond ⟨j, hj, hw⟩
    -- there is at least one index different from `i`, else `u i = 0`
    have hsne : (Finset.univ.erase i).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      have hsub : ∀ k : ι, k = i := by
        intro k
        by_contra hk
        have hmem : k ∈ (Finset.univ.erase i : Finset ι) :=
          Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩
        rw [hemp] at hmem
        simp at hmem
      have hsum_i : ∑ k, u k = u i :=
        Finset.sum_eq_single i (fun b _ hb => absurd (hsub b) hb)
          (fun h => absurd (Finset.mem_univ i) h)
      rw [hsum_i] at hsum
      exact hi (by rw [hsum, Valuation.map_zero])
    -- all other terms have valuation strictly smaller than `w (u i)`
    have hsup : (Finset.univ.erase i).sup' hsne (fun k => w (u k)) < w (u i) := by
      rw [Finset.sup'_lt_iff]
      intro b hb
      have hbi : b ≠ i := Finset.ne_of_mem_erase hb
      exact lt_of_le_of_ne (hmax' b) (hsecond' b hbi)
    have hsum_erase : ∑ k ∈ Finset.univ.erase i, u k = - u i := by
      have h := Finset.sum_erase_add (Finset.univ : Finset ι) u (Finset.mem_univ i)
      rw [hsum] at h
      exact eq_neg_of_add_eq_zero_left h
    -- but the sum of those terms equals `-u i`, whose valuation is `w (u i)`
    have hle : w (u i) ≤ (Finset.univ.erase i).sup' hsne (fun k => w (u k)) :=
      calc w (u i) = w (-(u i)) := (Valuation.map_neg w (u i)).symm
        _ = w (∑ k ∈ Finset.univ.erase i, u k) := by rw [hsum_erase]
        _ ≤ _ := Valuation.map_sum_le w (fun k hk => Finset.le_sup' (fun k => w (u k)) hk)
    exact absurd hle (not_le.mpr hsup)

end Work.MotV5.Nodes
