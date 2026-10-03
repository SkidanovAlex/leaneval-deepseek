import Mathlib

namespace Work.Repel

/-- A Lipschitz sequence `t` (with step bound `δ`) that runs from `t j₀ ≤ -a` to
`t J ≥ a` must spend at least `2a/δ - 1` indices inside the window `|t j| ≤ a`.

The proof picks the last index `s ≤ J` with `t s ≤ -a` and the first index `r > s`
with `t r ≥ a`.  Every index strictly between them lies in the window, and the
telescoping inequality `2a ≤ t r - t s ≤ (r - s) δ` gives `r - s ≥ 2a/δ`. -/
theorem lipschitz_window_card (t : ℕ → ℝ) (δ a : ℝ) (hδ : 0 < δ)
    (hlip : ∀ j, |t (j + 1) - t j| ≤ δ)
    {j₀ J : ℕ} (hJ : j₀ ≤ J) (hlo : t j₀ ≤ -a) (hhi : a ≤ t J) :
    2 * a / δ - 1 ≤ (((Finset.Icc j₀ J).filter (fun j => |t j| ≤ a)).card : ℝ) := by
  set S : Finset ℕ := (Finset.Icc j₀ J).filter (fun j => |t j| ≤ a) with hS
  by_cases ha : a ≤ 0
  · have h1 : 2 * a / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hδ)
    have h2 : (0 : ℝ) ≤ (S.card : ℝ) := by positivity
    linarith
  · have ha' : 0 < a := lt_of_not_ge ha
    set A : Finset ℕ := (Finset.Icc j₀ J).filter (fun j => t j ≤ -a) with hA
    have hAne : A.Nonempty := by
      refine ⟨j₀, ?_⟩
      rw [hA, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨le_refl _, hJ⟩, hlo⟩
    set s : ℕ := A.max' hAne with hs
    have hs_mem : s ∈ A := by rw [hs]; exact Finset.max'_mem A hAne
    have hs_Icc : s ∈ Finset.Icc j₀ J := (Finset.mem_filter.mp hs_mem).1
    have hs_le : t s ≤ -a := (Finset.mem_filter.mp hs_mem).2
    have hs_j0 : j₀ ≤ s := (Finset.mem_Icc.mp hs_Icc).1
    have hs_J : s ≤ J := (Finset.mem_Icc.mp hs_Icc).2
    have hs_max : ∀ j ∈ A, j ≤ s := by
      intro j hj
      rw [hs]
      exact Finset.le_max' A j hj
    have hs_lt_J : s < J := by
      rcases lt_or_eq_of_le hs_J with h | h
      · exact h
      · exfalso
        have hJle : t J ≤ -a := h ▸ hs_le
        linarith
    set B : Finset ℕ := (Finset.Icc (s + 1) J).filter (fun j => a ≤ t j) with hB
    have hBne : B.Nonempty := by
      refine ⟨J, ?_⟩
      rw [hB, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, le_refl _⟩, hhi⟩
    set r : ℕ := B.min' hBne with hr
    have hr_mem : r ∈ B := by rw [hr]; exact Finset.min'_mem B hBne
    have hr_Icc : r ∈ Finset.Icc (s + 1) J := (Finset.mem_filter.mp hr_mem).1
    have hr_ge_a : a ≤ t r := (Finset.mem_filter.mp hr_mem).2
    have hr_s1 : s + 1 ≤ r := (Finset.mem_Icc.mp hr_Icc).1
    have hr_J : r ≤ J := (Finset.mem_Icc.mp hr_Icc).2
    have hr_min : ∀ j ∈ B, r ≤ j := by
      intro j hj; rw [hr]; exact Finset.min'_le B j hj
    have hsub : Finset.Ico (s + 1) r ⊆ S := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      obtain ⟨hj1, hj2⟩ := hj
      rw [hS, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have hgt : -a < t j := by
        by_contra hcon
        have hcon' : t j ≤ -a := le_of_not_gt hcon
        have hmem : j ∈ A := by
          rw [hA, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, hcon'⟩
        have := hs_max j hmem
        omega
      have hlt : t j < a := by
        by_contra hcon
        have hcon' : a ≤ t j := le_of_not_gt hcon
        have hmem : j ∈ B := by
          rw [hB, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, hcon'⟩
        have := hr_min j hmem
        omega
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hcard_ge : ((Finset.Ico (s + 1) r).card : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hsr : s ≤ r := by omega
    have htel : ∑ i ∈ Finset.Ico s r, (t (i + 1) - t i) = t r - t s :=
      Finset.sum_Ico_sub t hsr
    have habs : |t r - t s| ≤ ((Finset.Ico s r).card : ℝ) * δ := by
      calc |t r - t s| = |∑ i ∈ Finset.Ico s r, (t (i + 1) - t i)| := by rw [htel]
        _ ≤ ∑ i ∈ Finset.Ico s r, |t (i + 1) - t i| :=
            Finset.abs_sum_le_sum_abs (fun i => t (i + 1) - t i) (Finset.Ico s r)
        _ ≤ ∑ i ∈ Finset.Ico s r, δ := Finset.sum_le_sum (fun i _ => hlip i)
        _ = ((Finset.Ico s r).card : ℝ) * δ := by simp [Finset.sum_const, nsmul_eq_mul]
    have htr_ts : 2 * a ≤ t r - t s := by linarith
    have hpos : 0 ≤ t r - t s := by linarith
    have hdiff : t r - t s ≤ ((r - s : ℕ) : ℝ) * δ := by
      have h := habs
      rw [abs_of_nonneg hpos] at h
      rwa [Nat.card_Ico s r] at h
    have h2a : 2 * a ≤ ((r - s : ℕ) : ℝ) * δ := by linarith
    have hrs_real : 2 * a / δ ≤ ((r - s : ℕ) : ℝ) := by
      rw [div_le_iff₀ hδ]
      exact h2a
    have hcast : ((r - s : ℕ) : ℝ) = ((r - (s + 1) : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub hsr, Nat.cast_sub hr_s1]
      push_cast
      ring
    have htarget : 2 * a / δ - 1 ≤ ((r - (s + 1) : ℕ) : ℝ) := by linarith
    have hcard_ge2 : ((r - (s + 1) : ℕ) : ℝ) ≤ (S.card : ℝ) := by
      have h := hcard_ge
      rwa [Nat.card_Ico (s + 1) r] at h
    linarith

end Work.Repel
