import Mathlib

namespace Work.Pert.PinLogDev

/-- Quantitative monotonicity: if `x` increases by at least `c` at every step `< n`, then
`x i + c * (j - i) ≤ x j` for `i ≤ j ≤ n`. -/
lemma step_le_mono {n : ℕ} {x : ℕ → ℝ} {c : ℝ}
    (hstep : ∀ j, j < n → x j + c ≤ x (j + 1)) :
    ∀ i j, i ≤ j → j ≤ n → x i + c * ((j - i : ℕ) : ℝ) ≤ x j := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; simp
  | succ j hij ih =>
      intro hjn
      have hj : j < n := by omega
      have ih' := ih (by omega : j ≤ n)
      have hs : x j + c ≤ x (j + 1) := hstep j hj
      have hcast : ((j + 1 - i : ℕ) : ℝ) = ((j - i : ℕ) : ℝ) + 1 := by
        rw [Nat.succ_sub hij]
        push_cast
        ring
      rw [hcast]
      nlinarith [hs, ih']

/-- The counting lemma: for a sequence increasing by at least `c > 0` and bounded above by `d` on
`[0, n)`, the number of indices `j < n` with `k < x j` is at most `(d - k)/c + 1`.  (The `max 0`
only guards against a negative right-hand side when the set is empty and `d < k`.) -/
lemma card_lt_le_of_mono {n : ℕ} {x : ℕ → ℝ} {c d k : ℝ} (hc : 0 < c)
    (hstep : ∀ j, j < n → x j + c ≤ x (j + 1))
    (hd : ∀ j, j < n → x j ≤ d) :
    (((Finset.range n).filter (fun j => k < x j)).card : ℝ) ≤ max 0 ((d - k) / c) + 1 := by
  set S : Finset ℕ := (Finset.range n).filter (fun j => k < x j) with hS
  rcases Finset.eq_empty_or_nonempty S with h0 | hne
  · rw [h0]
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith [le_max_left (0 : ℝ) ((d - k) / c)]
  · set a : ℕ := S.min' hne with ha
    have haS : a ∈ S := Finset.min'_mem S hne
    have han : a < n := Finset.mem_range.mp (Finset.mem_filter.mp haS).1
    have hka : k < x a := (Finset.mem_filter.mp haS).2
    have hsub : S ⊆ Finset.Ico a n := by
      intro j hj
      exact Finset.mem_Ico.mpr
        ⟨Finset.min'_le S j hj, Finset.mem_range.mp (Finset.mem_filter.mp hj).1⟩
    have hcard : S.card ≤ n - a := by
      calc S.card ≤ (Finset.Ico a n).card := Finset.card_le_card hsub
        _ = n - a := Nat.card_Ico a n
    have hpos : 1 ≤ S.card := Finset.card_pos.mpr hne
    have hn1 : n - 1 < n := by omega
    have hmono := step_le_mono hstep a (n - 1) (by omega) (by omega)
    have haux : x (n - 1) ≤ d := hd (n - 1) hn1
    have hsc : ((S.card - 1 : ℕ) : ℝ) ≤ ((n - 1 - a : ℕ) : ℝ) := by
      have h : S.card - 1 ≤ n - 1 - a := by omega
      exact_mod_cast h
    have hstepc : c * ((S.card - 1 : ℕ) : ℝ) ≤ d - x a := by
      have h1 : c * ((S.card - 1 : ℕ) : ℝ) ≤ c * ((n - 1 - a : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hsc hc.le
      linarith
    have hlt : c * ((S.card - 1 : ℕ) : ℝ) < d - k := by linarith
    have hdiv : ((S.card - 1 : ℕ) : ℝ) < (d - k) / c :=
      (lt_div_iff₀ hc).mpr (by linarith [hlt])
    have hcast : ((S.card : ℕ) : ℝ) = ((S.card - 1 : ℕ) : ℝ) + 1 := by
      have h : S.card = S.card - 1 + 1 := by omega
      rw [h]
      push_cast
      ring
    rw [hcast]
    have : (d - k) / c + 1 ≤ max 0 ((d - k) / c) + 1 := by
      linarith [le_max_right (0 : ℝ) ((d - k) / c)]
    linarith

set_option linter.unusedVariables false in
theorem sum_shallow_indicator_le {n : ℕ} {ζ : ℕ → ℂ} {T Bn X₁ M : ℝ}
    (hT : 0 ≤ T) (hX₁ : 0 < X₁)
    (hstep : ∀ j : ℕ, j < n → ‖ζ (j + 1) - (ζ j + 1)‖ ≤ 1 / 32)
    (hn : ‖ζ n + (((M - (n : ℝ)) : ℝ) : ℂ)‖ ≤ Bn)
    (hXn : X₁ ≤ M - (n : ℝ)) (hnX : M - (n : ℝ) ≤ X₁ + 1) :
    ∑ j ∈ Finset.range n, (if ‖ζ j‖ < T then (1 : ℝ) else 0) ≤
      (32 / 31) * (T + X₁ + 1 + Bn) + 1 := by
  have hBn : 0 ≤ Bn := le_trans (norm_nonneg _) hn
  -- the real parts increase by at least `31/32` at each step
  have hstepx : ∀ j, j < n → (ζ j).re + 31 / 32 ≤ (ζ (j + 1)).re := by
    intro j hj
    have h2 : |(ζ (j + 1)).re - ((ζ j).re + 1)| ≤ 1 / 32 := by
      have h := le_trans (Complex.abs_re_le_norm (ζ (j + 1) - (ζ j + 1))) (hstep j hj)
      simpa [Complex.sub_re, Complex.add_re] using h
    have hb := abs_le.mp h2
    linarith [hb.1]
  -- every index `j < n` has real part at most `Bn - X₁`
  have hd : ∀ j, j < n → (ζ j).re ≤ Bn - X₁ := by
    intro j hj
    have h1 : (ζ j).re < (ζ n).re := by
      have h := step_le_mono hstepx j n (le_of_lt hj) (le_refl n)
      have hc' : 0 < (31 / 32 : ℝ) * ((n - j : ℕ) : ℝ) :=
        mul_pos (by norm_num) (by exact_mod_cast Nat.sub_pos_of_lt hj)
      linarith
    have h2 : (ζ n).re ≤ Bn - X₁ := by
      have h := le_trans (Complex.abs_re_le_norm (ζ n + (((M - (n : ℝ)) : ℝ) : ℂ))) hn
      have hre : (ζ n + (((M - (n : ℝ)) : ℝ) : ℂ)).re = (ζ n).re + (M - (n : ℝ)) := by
        simp [Complex.add_re]
      rw [hre] at h
      have hb := (abs_le.mp h).2
      linarith
    linarith
  have hcount := card_lt_le_of_mono (x := fun j => (ζ j).re) (c := 31 / 32)
    (d := Bn - X₁) (k := -T) (by norm_num) hstepx hd
  -- pointwise comparison of the indicators
  have step1 : ∑ j ∈ Finset.range n, (if ‖ζ j‖ < T then (1 : ℝ) else 0)
      ≤ ∑ j ∈ Finset.range n, (if -T < (ζ j).re then (1 : ℝ) else 0) := by
    apply Finset.sum_le_sum
    intro j hj
    by_cases h : ‖ζ j‖ < T
    · have hre : -T < (ζ j).re := by
        have hh := Complex.abs_re_le_norm (ζ j)
        have hlt' : |(ζ j).re| < T := lt_of_le_of_lt hh h
        have := (abs_lt.mp hlt').1
        linarith
      simp only [h, hre, ite_true]
      norm_num
    · simp only [h, ite_false]
      split_ifs <;> norm_num
  have step2 : ∑ j ∈ Finset.range n, (if -T < (ζ j).re then (1 : ℝ) else 0)
      = (((Finset.range n).filter (fun j => -T < (ζ j).re)).card : ℝ) :=
    Finset.sum_boole _ _
  have harith : max 0 (((Bn - X₁) - (-T)) / (31 / 32)) + 1
      ≤ (32 / 31) * (T + X₁ + 1 + Bn) + 1 := by
    have h1 : ((Bn - X₁) - (-T)) / (31 / 32) = (T - X₁ + Bn) * (32 / 31) := by
      field_simp
      ring
    rw [h1]
    have h2 : (T - X₁ + Bn) * (32 / 31) ≤ (T + X₁ + 1 + Bn) * (32 / 31) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    have h3 : max 0 ((T - X₁ + Bn) * (32 / 31)) ≤ (T + X₁ + 1 + Bn) * (32 / 31) := by
      apply max_le
      · nlinarith
      · exact h2
    linarith
  linarith [step1, step2, hcount, harith]

end Work.Pert.PinLogDev
