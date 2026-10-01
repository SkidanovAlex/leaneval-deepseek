import Mathlib

namespace Work.LinnikAreas.Density4

open Finset

/-- Partial sums of `1/(j+Q+1)²` are bounded by `1/Q`, by comparison with the
telescoping series `1/(j+Q) - 1/(j+Q+1) = 1/((j+Q)(j+Q+1)) ≥ 1/(j+Q+1)²`. -/
lemma sum_range_inv_sq_shift_le (Q N : ℕ) (hQ : 1 ≤ Q) :
    ∑ j ∈ Finset.range N, (1 : ℝ) / ((j + (Q + 1) : ℕ) : ℝ) ^ 2 ≤ 1 / (Q : ℝ) := by
  have hterm : ∀ j ∈ Finset.range N,
      (1 : ℝ) / ((j + (Q + 1) : ℕ) : ℝ) ^ 2
        ≤ (1 : ℝ) / ((j + Q : ℕ) : ℝ) - 1 / ((j + Q + 1 : ℕ) : ℝ) := by
    intro j _
    have hcast : ((j + (Q + 1) : ℕ) : ℝ) = ((j + Q : ℕ) : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((j + Q + 1 : ℕ) : ℝ) = ((j + Q : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hcast, hcast2]
    have hkey : (1 : ℝ) / (((j + Q : ℕ) : ℝ) + 1) ^ 2
        ≤ 1 / (((j + Q : ℕ) : ℝ) * (((j + Q : ℕ) : ℝ) + 1)) := by
      apply one_div_le_one_div_of_le (by positivity) _
      nlinarith [show (0 : ℝ) ≤ ((j + Q : ℕ) : ℝ) by positivity]
    have hsub : (1 : ℝ) / ((j + Q : ℕ) : ℝ) - 1 / (((j + Q : ℕ) : ℝ) + 1)
        = 1 / (((j + Q : ℕ) : ℝ) * (((j + Q : ℕ) : ℝ) + 1)) := by
      field_simp
      ring
    rw [hsub]
    exact hkey
  have htel : ∑ j ∈ Finset.range N,
        ((1 : ℝ) / ((j + Q : ℕ) : ℝ) - 1 / ((j + Q + 1 : ℕ) : ℝ))
      = 1 / (Q : ℝ) - 1 / ((N + Q : ℕ) : ℝ) := by
    have hcongr : ∑ j ∈ Finset.range N,
          ((1 : ℝ) / ((j + Q : ℕ) : ℝ) - 1 / ((j + Q + 1 : ℕ) : ℝ))
        = ∑ j ∈ Finset.range N, ((fun m : ℕ => (1 : ℝ) / ((m + Q : ℕ) : ℝ)) j
            - (fun m : ℕ => (1 : ℝ) / ((m + Q : ℕ) : ℝ)) (j + 1)) := by
      apply Finset.sum_congr rfl
      intro j _
      have h1 : ((j + 1 + Q : ℕ) : ℝ) = ((j + Q + 1 : ℕ) : ℝ) := by push_cast; ring
      show (1 : ℝ) / ((j + Q : ℕ) : ℝ) - 1 / ((j + Q + 1 : ℕ) : ℝ)
          = (1 : ℝ) / ((j + Q : ℕ) : ℝ) - 1 / (((j + 1) + Q : ℕ) : ℝ)
      rw [h1]
    rw [hcongr, Finset.sum_range_sub']
    simp
  calc ∑ j ∈ Finset.range N, (1 : ℝ) / ((j + (Q + 1) : ℕ) : ℝ) ^ 2
      ≤ ∑ j ∈ Finset.range N,
          ((1 : ℝ) / ((j + Q : ℕ) : ℝ) - 1 / ((j + Q + 1 : ℕ) : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = 1 / (Q : ℝ) - 1 / ((N + Q : ℕ) : ℝ) := htel
    _ ≤ 1 / (Q : ℝ) := by
        have hpos : (0 : ℝ) < ((N + Q : ℕ) : ℝ) := by
          exact_mod_cast (by omega : 0 < N + Q)
        have : (0 : ℝ) ≤ 1 / ((N + Q : ℕ) : ℝ) := by positivity
        linarith

/-- **Tail bound for a summable Möbius-type series.**  If `|g n| ≤ 1/n²` for all `n`
(so in particular `g 0 = 0`), then `g` is summable and
`|∑' n, g n − ∑_{1 ≤ n ≤ Q} g n| ≤ 1/Q` for `Q ≥ 1`.

Hint: `Summable.sum_add_tsum_nat_add`, then bound the tail by
`∑'_j 1/(j+Q+1)² ≤ 1/Q` via `1/a² ≤ 1/(a-1) − 1/a` and telescoping. -/
theorem tsum_tail_bound (Q : ℕ) (hQ : 1 ≤ Q) (g : ℕ → ℝ)
    (hbound : ∀ n : ℕ, |g n| ≤ 1 / (n : ℝ) ^ 2) :
    Summable g ∧ |(∑' n : ℕ, g n) - ∑ n ∈ Finset.Icc 1 Q, g n| ≤ 1 / (Q : ℝ) := by
  -- `g 0 = 0` from the bound at `n = 0`
  have hg0 : g 0 = 0 := by
    have h : |g 0| ≤ 0 := by simpa using hbound 0
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have hg : Summable g :=
    Summable.of_norm_bounded hbase (fun n => by rw [Real.norm_eq_abs]; exact hbound n)
  refine ⟨hg, ?_⟩
  -- the partial sum over `Icc 1 Q` is the one over `range (Q+1)`, since `g 0 = 0`
  have hIcc : ∑ n ∈ Finset.Icc 1 Q, g n = ∑ n ∈ Finset.range (Q + 1), g n := by
    apply Finset.sum_subset ?_ ?_
    · intro x hx
      simp only [Finset.mem_Icc] at hx
      simp only [Finset.mem_range]
      omega
    · intro x hxr hxi
      simp only [Finset.mem_range] at hxr
      simp only [Finset.mem_Icc] at hxi
      have hx0 : x = 0 := by omega
      rw [hx0]; exact hg0
  -- the remaining tail of the series is `∑' i, g (i + (Q+1))`
  have hshift : ∑' i : ℕ, g (i + (Q + 1))
      = (∑' n : ℕ, g n) - ∑ n ∈ Finset.range (Q + 1), g n := by
    have h := hg.sum_add_tsum_nat_add (Q + 1)
    linarith
  rw [hIcc, ← hshift]
  -- summability of the shifted comparison series
  have hsq : Summable (fun i : ℕ => (1 : ℝ) / ((i + (Q + 1) : ℕ) : ℝ) ^ 2) := by
    have hb : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have := (summable_nat_add_iff (Q + 1)).mpr hb
    simpa using this
  have hSshift : Summable (fun i : ℕ => g (i + (Q + 1))) :=
    (summable_nat_add_iff (Q + 1)).mpr hg
  have h1 : |∑' i : ℕ, g (i + (Q + 1))| ≤ ∑' i : ℕ, |g (i + (Q + 1))| := by
    have h := norm_tsum_le_tsum_norm (f := fun i : ℕ => g (i + (Q + 1)))
      (by simpa [Real.norm_eq_abs] using hSshift.abs)
    simpa [Real.norm_eq_abs] using h
  have h2 : ∑' i : ℕ, |g (i + (Q + 1))|
      ≤ ∑' i : ℕ, (1 : ℝ) / ((i + (Q + 1) : ℕ) : ℝ) ^ 2 := by
    apply Summable.tsum_le_tsum _ hSshift.abs hsq
    intro i
    exact hbound (i + (Q + 1))
  have h3 : ∑' i : ℕ, (1 : ℝ) / ((i + (Q + 1) : ℕ) : ℝ) ^ 2 ≤ 1 / (Q : ℝ) := by
    apply Summable.tsum_le_of_sum_le hsq
    intro s
    have hsub : s ⊆ Finset.range (s.sup id + 1) := by
      intro x hx
      simp only [Finset.mem_range]
      have hxs : x ≤ s.sup id := by simpa using (Finset.le_sup (f := id) hx)
      omega
    calc ∑ i ∈ s, (1 : ℝ) / ((i + (Q + 1) : ℕ) : ℝ) ^ 2
        ≤ ∑ i ∈ Finset.range (s.sup id + 1),
            (1 : ℝ) / ((i + (Q + 1) : ℕ) : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro x _ _; positivity)
      _ ≤ 1 / (Q : ℝ) := sum_range_inv_sq_shift_le Q _ hQ
  linarith [h1, h2, h3]

end Work.LinnikAreas.Density4
