import Mathlib

namespace Work.Pert.LCH

/-- Counting lemma: if a sequence `m : ℕ → ℝ` grows by at least `c₀ > 0` at every step
`j < n`, and a finite set `T ⊆ {0, …, n-1}` has all its values `m j` inside `[a, b]`,
then `#T ≤ (b - a) / c₀ + 1`.

Indeed, if `j₀` and `j₁` are the smallest and largest elements of `T`, telescoping gives
`c₀ * (j₁ - j₀) ≤ m j₁ - m j₀ ≤ b - a`, while `T ⊆ Icc j₀ j₁` gives
`#T ≤ j₁ - j₀ + 1`. -/
theorem card_le_of_gap {m : ℕ → ℝ} {c₀ : ℝ} {n : ℕ} (hc0 : 0 < c₀)
    (hstep : ∀ j < n, c₀ ≤ m (j + 1) - m j) {T : Finset ℕ} (hTn : ∀ j ∈ T, j < n)
    {a b : ℝ} (hab : a ≤ b) (hmem : ∀ j ∈ T, a ≤ m j ∧ m j ≤ b) :
    (T.card : ℝ) ≤ (b - a) / c₀ + 1 := by
  rcases T.eq_empty_or_nonempty with hT | hT
  · subst hT
    simp only [Finset.card_empty, Nat.cast_zero]
    have h1 : 0 ≤ (b - a) / c₀ := div_nonneg (sub_nonneg.mpr hab) (le_of_lt hc0)
    linarith
  · set j0 := T.min' hT with hj0def
    set j1 := T.max' hT with hj1def
    have hj0mem : j0 ∈ T := by rw [hj0def]; exact T.min'_mem hT
    have hj1mem : j1 ∈ T := by rw [hj1def]; exact T.max'_mem hT
    have hj1n : j1 < n := hTn j1 hj1mem
    have hle0 : ∀ j ∈ T, j0 ≤ j := by intro j hj; rw [hj0def]; exact T.min'_le j hj
    have hle1 : ∀ j ∈ T, j ≤ j1 := by intro j hj; rw [hj1def]; exact T.le_max' j hj
    have h01 : j0 ≤ j1 := hle0 j1 hj1mem
    -- Telescoping: `m` grows by at least `c₀` on the whole interval from `j0` to `j1`.
    have htel : ((j1 - j0 : ℕ) : ℝ) * c₀ ≤ m j1 - m j0 := by
      have key : ∀ d j, j + d ≤ n → (d : ℝ) * c₀ ≤ m (j + d) - m j := by
        intro d
        induction d with
        | zero => intro j _; simp
        | succ d ih =>
          intro j hjd
          have hlt : j + d < n := by omega
          have hd := ih j (by omega)
          have hs := hstep (j + d) hlt
          have hstep' : c₀ ≤ m (j + (d + 1)) - m (j + d) := by
            simpa [Nat.add_assoc] using hs
          have hcast : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; ring
          rw [hcast]
          nlinarith [hd, hstep']
      have hj0j1 : j0 + (j1 - j0) = j1 := Nat.add_sub_of_le h01
      have hkey := key (j1 - j0) j0 (by omega)
      rwa [hj0j1] at hkey
    have hbj : m j1 - m j0 ≤ b - a := by
      have h1 := (hmem j1 hj1mem).2
      have h0 := (hmem j0 hj0mem).1
      linarith
    have hdiv : ((j1 - j0 : ℕ) : ℝ) ≤ (b - a) / c₀ := by
      rw [le_div_iff₀ hc0]
      linarith
    -- `T` sits inside the integer interval `[j0, j1]`.
    have hcard : T.card ≤ j1 - j0 + 1 := by
      have hsub : T ⊆ Finset.Icc j0 j1 := by
        intro j hj
        simp only [Finset.mem_Icc]
        exact ⟨hle0 j hj, hle1 j hj⟩
      have h1 := Finset.card_le_card hsub
      rw [Nat.card_Icc] at h1
      omega
    have hcastcard : (T.card : ℝ) ≤ (j1 : ℝ) - (j0 : ℝ) + 1 := by
      have h1 : (T.card : ℝ) ≤ ((j1 - j0 + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
      rwa [Nat.cast_add, Nat.cast_sub h01, Nat.cast_one] at h1
    have hsubc : ((j1 - j0 : ℕ) : ℝ) = (j1 : ℝ) - (j0 : ℝ) := Nat.cast_sub h01
    linarith

end Work.Pert.LCH
