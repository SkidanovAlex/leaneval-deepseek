import Mathlib

namespace Work.FIArea1

open Finset

attribute [local instance] Classical.propDecidable

/-! ## Auxiliary lemmas for the dyadic/Abel bound of `Work.FIArea1.sum_inv_sq_quad_le` -/

/-- Telescoping of a difference along an integer interval:
`∑_{j=a}^{b} (g j - g (j+1)) = g a - g (b+1)`. -/
lemma telescope_Icc_sub (g : ℕ → ℝ) (a b : ℕ) (h : a ≤ b) :
    ∑ j ∈ Finset.Icc a b, (g j - g (j + 1)) = g a - g (b + 1) := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
      rw [Finset.sum_Icc_succ_top (Nat.le_succ_of_le hb), ih]
      ring

/-- **Lattice point count.** The number of pairs `(m,n)` with `1 ≤ m,n ≤ N` and
`m² + n² ≤ X` is at most `X`. -/
lemma card_pair_sq_add_sq_le (N X : ℕ) :
    (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
      (fun p : ℕ × ℕ => p.1 ^ 2 + p.2 ^ 2 ≤ X)).card ≤ X := by
  set k := Nat.floor (Real.sqrt (X : ℝ)) with hk
  have hk_le : (k : ℝ) ≤ Real.sqrt (X : ℝ) := Nat.floor_le (Real.sqrt_nonneg _)
  have hk2 : k ^ 2 ≤ X := by
    have h1 : ((k : ℝ)) ^ 2 ≤ (X : ℝ) := by
      calc ((k : ℝ)) ^ 2 ≤ (Real.sqrt (X : ℝ)) ^ 2 := by
            exact pow_le_pow_left₀ (by positivity) hk_le 2
        _ = (X : ℝ) := Real.sq_sqrt (by positivity)
    exact_mod_cast h1
  have hsub : ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
        (fun p : ℕ × ℕ => p.1 ^ 2 + p.2 ^ 2 ≤ X) ⊆ (Finset.Icc 1 k) ×ˢ (Finset.Icc 1 k) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
    obtain ⟨⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩, hle⟩ := hp
    have haX : p.1 ^ 2 ≤ X := by omega
    have hbX : p.2 ^ 2 ≤ X := by omega
    have ha : p.1 ≤ k := Nat.le_floor (Real.le_sqrt_of_sq_le (by exact_mod_cast haX))
    have hb : p.2 ≤ k := Nat.le_floor (Real.le_sqrt_of_sq_le (by exact_mod_cast hbX))
    exact ⟨⟨ha1, ha⟩, ⟨hb1, hb⟩⟩
  calc (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
          (fun p : ℕ × ℕ => p.1 ^ 2 + p.2 ^ 2 ≤ X)).card
      ≤ ((Finset.Icc 1 k) ×ˢ (Finset.Icc 1 k)).card := Finset.card_le_card hsub
    _ = k * k := by simp [Finset.card_product, Nat.card_Icc]
    _ = k ^ 2 := by ring
    _ ≤ X := hk2

/-- The telescoping weight `1/j² - 1/(j+1)²`. -/
noncomputable def wt (j : ℕ) : ℝ := ((j : ℝ)⁻¹) ^ 2 - (((j + 1 : ℕ) : ℝ)⁻¹) ^ 2

lemma wt_nonneg {j : ℕ} (hj : 1 ≤ j) : 0 ≤ wt j := by
  rw [wt]
  have h1 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have h2 : (((j + 1 : ℕ) : ℝ))⁻¹ ≤ ((j : ℝ))⁻¹ := by
    apply inv_anti₀ h1
    push_cast; linarith
  have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (((j + 1 : ℕ) : ℝ))⁻¹) h2 2
  linarith [this]

lemma wt_mul_self_le {j : ℕ} (hj : 1 ≤ j) :
    wt j * (j : ℝ) ≤ 3 * ((((j + 1 : ℕ) : ℝ))⁻¹) ^ 2 := by
  have hx : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hy : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  rw [wt, hy]
  have h1 : (0 : ℝ) < (j : ℝ) := by linarith
  have h2 : (0 : ℝ) < (j : ℝ) + 1 := by linarith
  have key : (((j : ℝ)⁻¹) ^ 2 - ((((j : ℝ) + 1)⁻¹)) ^ 2) * (j : ℝ)
      ≤ 3 * ((((j : ℝ) + 1)⁻¹)) ^ 2 := by
    field_simp
    nlinarith [hx]
  exact key

/-- **Abel/telescoping step.** For `1 ≤ r ≤ M`,
`1/r² ≤ ∑_{j=1}^{M} [r ≤ j]·(1/j² - 1/(j+1)²) + 1/(M+1)²`. -/
lemma inv_sq_le_sum_wt (r M : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ M) :
    ((r : ℝ)⁻¹) ^ 2 ≤ (∑ j ∈ Finset.Icc 1 M, (if r ≤ j then wt j else 0))
      + (((M + 1 : ℕ) : ℝ)⁻¹) ^ 2 := by
  have hfilter : (Finset.Icc 1 M).filter (fun j => r ≤ j) = Finset.Icc r M := by
    ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  have hsum : (∑ j ∈ Finset.Icc 1 M, (if r ≤ j then wt j else 0))
      = ∑ j ∈ Finset.Icc r M, wt j := by
    rw [← Finset.sum_filter, hfilter]
  rw [hsum]
  have htel := telescope_Icc_sub (fun j : ℕ => ((j : ℝ)⁻¹) ^ 2) r M h2
  have htsum : (∑ j ∈ Finset.Icc r M, wt j) = ((r : ℝ)⁻¹) ^ 2 - (((M + 1 : ℕ) : ℝ)⁻¹) ^ 2 := by
    rw [← htel]
    apply Finset.sum_congr rfl
    intro j hj
    rw [wt]
  rw [htsum]
  linarith

/-- The final elementary sum estimate: `∑_{j=P+1}^{M} (1/j² - 1/(j+1)²)·j ≤ 3/P`. -/
lemma sum_wt_mul_le (P M : ℕ) (hP : 1 ≤ P) (hMP : P + 1 ≤ M) :
    (∑ j ∈ Finset.Icc (P + 1) M, wt j * (j : ℝ)) ≤ 3 / (P : ℝ) := by
  have hpt : ∀ j ∈ Finset.Icc (P + 1) M, wt j * (j : ℝ) ≤ 3 * ((((j + 1 : ℕ) : ℝ))⁻¹) ^ 2 := by
    intro j hj
    have hj1 : 1 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
    exact wt_mul_self_le hj1
  have hpt2 : ∀ j ∈ Finset.Icc (P + 1) M,
      ((((j + 1 : ℕ) : ℝ))⁻¹) ^ 2 ≤ ((j : ℝ)⁻¹) - ((((j + 1 : ℕ) : ℝ))⁻¹) := by
    intro j hj
    have hj1 : 1 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
    have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
    have hstep : ((((j + 1 : ℕ) : ℝ))⁻¹) ^ 2 ≤ ((j : ℝ)⁻¹) * ((((j + 1 : ℕ) : ℝ))⁻¹) := by
      rw [pow_two]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply inv_anti₀ hj0
      push_cast; linarith
    have heq : ((j : ℝ)⁻¹) * ((((j + 1 : ℕ) : ℝ))⁻¹) = ((j : ℝ)⁻¹) - ((((j + 1 : ℕ) : ℝ))⁻¹) := by
      have h2 : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
      rw [h2]
      field_simp
      ring
    rw [← heq]
    exact hstep
  calc (∑ j ∈ Finset.Icc (P + 1) M, wt j * (j : ℝ))
      ≤ ∑ j ∈ Finset.Icc (P + 1) M, 3 * ((((j + 1 : ℕ) : ℝ))⁻¹) ^ 2 := Finset.sum_le_sum hpt
    _ = 3 * ∑ j ∈ Finset.Icc (P + 1) M, ((((j + 1 : ℕ) : ℝ))⁻¹) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 3 * ∑ j ∈ Finset.Icc (P + 1) M, (((j : ℝ)⁻¹) - ((((j + 1 : ℕ) : ℝ))⁻¹)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Finset.sum_le_sum hpt2
    _ = 3 * ((((P + 1 : ℕ) : ℝ)⁻¹) - ((((M + 1 : ℕ) : ℝ)⁻¹))) := by
          rw [telescope_Icc_sub (fun j : ℕ => ((j : ℝ)⁻¹)) (P + 1) M hMP]
    _ ≤ 3 / (P : ℝ) := by
          have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
          have h1 : ((((P + 1 : ℕ) : ℝ)⁻¹) - ((((M + 1 : ℕ) : ℝ)⁻¹))) ≤ ((P : ℝ)⁻¹) := by
            have hM0 : (0 : ℝ) ≤ (((M + 1 : ℕ) : ℝ)⁻¹) := by positivity
            have h2 : (((P + 1 : ℕ) : ℝ)⁻¹) ≤ ((P : ℝ)⁻¹) := by
              apply inv_anti₀ hP0
              push_cast; linarith
            linarith
          rw [div_eq_mul_inv]
          linarith

theorem sum_inv_sq_quad_le (P N : ℕ) (hP : 1 ≤ P) :
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (if (P : ℝ) < (m : ℝ) ^ 2 + (n : ℝ) ^ 2
          then (((m : ℝ) ^ 2 + (n : ℝ) ^ 2)⁻¹ ^ 2) else 0)) ≤ 8 / (P : ℝ) := by
  classical
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
  set M : ℕ := max (2 * N * N + 1) (P + 1) with hMdef
  have hM_P : P + 1 ≤ M := by rw [hMdef]; exact le_max_right _ _
  have hM_2N : 2 * N * N + 1 ≤ M := by rw [hMdef]; exact le_max_left _ _
  set Pset : Finset (ℕ × ℕ) := (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) with hPsetdef
  set r : ℕ × ℕ → ℕ := fun p => p.1 ^ 2 + p.2 ^ 2 with hrdef
  set F : ℕ × ℕ → ℝ := fun p => (if (P : ℝ) < (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2
      then (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)⁻¹) ^ 2 else 0) with hFdef
  set X : ℕ × ℕ → ℝ := fun p => ∑ j ∈ Finset.Icc 1 M,
      (if P < r p ∧ r p ≤ j then wt j else 0) with hXdef
  set Y : ℕ × ℕ → ℝ := fun p => if P < r p then (((M + 1 : ℕ) : ℝ)⁻¹) ^ 2 else 0 with hYdef
  set cnt : ℕ → ℕ := fun j => (Pset.filter (fun p => P < r p ∧ r p ≤ j)).card with hcntdef
  set cnt0 : ℕ := (Pset.filter (fun p => P < r p)).card with hcnt0def
  -- membership facts
  have hmem : ∀ p ∈ Pset, 1 ≤ p.1 ∧ p.1 ≤ N ∧ 1 ≤ p.2 ∧ p.2 ≤ N := by
    intro p hp
    rw [hPsetdef, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩
  have hr_le_M : ∀ p ∈ Pset, r p ≤ M := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hmem p hp
    have h1sq : p.1 ^ 2 ≤ N * N := by
      simpa [pow_two] using Nat.pow_le_pow_left h2 2
    have h2sq : p.2 ^ 2 ≤ N * N := by
      simpa [pow_two] using Nat.pow_le_pow_left h4 2
    have hsum : p.1 ^ 2 + p.2 ^ 2 ≤ 2 * N * N := by
      calc p.1 ^ 2 + p.2 ^ 2 ≤ N * N + N * N := add_le_add h1sq h2sq
        _ = 2 * N * N := by ring
    have hfin : p.1 ^ 2 + p.2 ^ 2 ≤ M := by omega
    simpa [hrdef] using hfin
  have hr_ge1 : ∀ p ∈ Pset, 1 ≤ r p := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hmem p hp
    have hfin : 1 ≤ p.1 ^ 2 + p.2 ^ 2 := by nlinarith
    simpa [hrdef] using hfin
  have hcast : ∀ p : ℕ × ℕ, ((r p : ℕ) : ℝ) = (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
    intro p; simp only [hrdef]; push_cast; ring
  have hFform : ∀ p : ℕ × ℕ, F p = (if P < r p then (((r p : ℝ)⁻¹)) ^ 2 else 0) := by
    intro p
    simp only [hFdef]
    by_cases h : P < r p
    · have h' : (P : ℝ) < (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
        rw [← hcast p]; exact_mod_cast h
      rw [if_pos h', if_pos h, ← hcast p]
    · have h' : ¬ (P : ℝ) < (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := by
        rw [← hcast p]; exact_mod_cast h
      rw [if_neg h', if_neg h]
  -- Step 1: pointwise domination
  have hpoint : ∀ p ∈ Pset, F p ≤ X p + Y p := by
    intro p hp
    have hr1 : 1 ≤ r p := hr_ge1 p hp
    have hrM : r p ≤ M := hr_le_M p hp
    simp only [hFform p, hXdef, hYdef]
    by_cases h : P < r p
    · rw [if_pos h, if_pos h]
      have hsimp : (∑ j ∈ Finset.Icc 1 M, (if P < r p ∧ r p ≤ j then wt j else 0))
          = ∑ j ∈ Finset.Icc 1 M, (if r p ≤ j then wt j else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h2 : r p ≤ j
        · rw [if_pos ⟨h, h2⟩, if_pos h2]
        · rw [if_neg (fun hh => h2 hh.2), if_neg h2]
      rw [hsimp]
      exact inv_sq_le_sum_wt (r p) M hr1 hrM
    · rw [if_neg h, if_neg h]
      have hXnn : 0 ≤ X p := by
        rw [hXdef]
        apply Finset.sum_nonneg
        intro j hj
        by_cases hh : P < r p ∧ r p ≤ j
        · rw [if_pos hh]; exact wt_nonneg (Finset.mem_Icc.mp hj).1
        · rw [if_neg hh]
      linarith
  have hFA : (∑ p ∈ Pset, F p) ≤ (∑ p ∈ Pset, X p) + (∑ p ∈ Pset, Y p) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hpoint
  -- Step 2: the X-sum as a sum over the level variable `j`
  have hXs : (∑ p ∈ Pset, X p) = ∑ j ∈ Finset.Icc 1 M, wt j * ((cnt j : ℕ) : ℝ) := by
    simp only [hXdef, hcntdef]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    have hiff : ∀ p : ℕ × ℕ, (if P < r p ∧ r p ≤ j then wt j else 0)
        = wt j * (if P < r p ∧ r p ≤ j then (1 : ℝ) else 0) := by
      intro p; by_cases h : (P < r p ∧ r p ≤ j) <;> simp [h]
    simp only [hiff]
    rw [← Finset.mul_sum, Finset.sum_boole]
  have hYs : (∑ p ∈ Pset, Y p) = ((((M + 1 : ℕ) : ℝ)⁻¹) ^ 2) * ((cnt0 : ℕ) : ℝ) := by
    simp only [hYdef, hcnt0def]
    have hiff : ∀ p : ℕ × ℕ, (if P < r p then (((M + 1 : ℕ) : ℝ)⁻¹) ^ 2 else 0)
        = ((((M + 1 : ℕ) : ℝ)⁻¹) ^ 2) * (if P < r p then (1 : ℝ) else 0) := by
      intro p; by_cases h : P < r p <;> simp [h]
    simp only [hiff]
    rw [← Finset.mul_sum, Finset.sum_boole]
  -- Step 3: bound the level sum
  have hXb : (∑ j ∈ Finset.Icc 1 M, wt j * ((cnt j : ℕ) : ℝ)) ≤ 3 / (P : ℝ) := by
    have step1 : ∀ j ∈ Finset.Icc 1 M,
        wt j * ((cnt j : ℕ) : ℝ) ≤ wt j * (if P < j then (j : ℝ) else 0) := by
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      apply mul_le_mul_of_nonneg_left _ (wt_nonneg hj1)
      by_cases h : P < j
      · rw [if_pos h]
        have hsub : Pset.filter (fun p => P < r p ∧ r p ≤ j) ⊆ Pset.filter (fun p => r p ≤ j) := by
          intro p hp
          rw [Finset.mem_filter] at hp ⊢
          exact ⟨hp.1, hp.2.2⟩
        have h1 := Finset.card_le_card hsub
        have h2 : (Pset.filter (fun p => r p ≤ j)).card ≤ j := by
          simpa [hPsetdef, hrdef] using card_pair_sq_add_sq_le N j
        have h3 : cnt j ≤ j := by rw [hcntdef]; exact le_trans h1 h2
        exact_mod_cast h3
      · rw [if_neg h]
        have hempty : Pset.filter (fun p => P < r p ∧ r p ≤ j) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro p hp hpp
          omega
        have : cnt j = 0 := by simp only [hcntdef]; rw [hempty]; simp
        rw [this]; simp
    have step2 : (∑ j ∈ Finset.Icc 1 M, wt j * (if P < j then (j : ℝ) else 0))
        = ∑ j ∈ Finset.Icc (P + 1) M, wt j * (j : ℝ) := by
      have hf : (Finset.Icc 1 M).filter (fun j => P < j) = Finset.Icc (P + 1) M := by
        ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
      have hpt : ∀ j, wt j * (if P < j then (j : ℝ) else 0)
          = (if P < j then wt j * (j : ℝ) else 0) := by
        intro j; by_cases h : P < j <;> simp [h]
      rw [← hf]
      simp only [hpt]
      rw [← Finset.sum_filter]
    calc (∑ j ∈ Finset.Icc 1 M, wt j * ((cnt j : ℕ) : ℝ))
        ≤ ∑ j ∈ Finset.Icc 1 M, wt j * (if P < j then (j : ℝ) else 0) := Finset.sum_le_sum step1
      _ = ∑ j ∈ Finset.Icc (P + 1) M, wt j * (j : ℝ) := step2
      _ ≤ 3 / (P : ℝ) := sum_wt_mul_le P M hP hM_P
  -- Step 4: bound the correction sum
  have hYb : ((((M + 1 : ℕ) : ℝ)⁻¹) ^ 2) * ((cnt0 : ℕ) : ℝ) ≤ 1 / (P : ℝ) := by
    have hcard : cnt0 ≤ M := by
      have hsub : Pset.filter (fun p => P < r p) ⊆ Pset.filter (fun p => r p ≤ M) := by
        intro p hp
        rw [Finset.mem_filter] at hp ⊢
        exact ⟨hp.1, hr_le_M p hp.1⟩
      have h1 := Finset.card_le_card hsub
      have h2 : (Pset.filter (fun p => r p ≤ M)).card ≤ M := by
        simpa [hPsetdef, hrdef] using card_pair_sq_add_sq_le N M
      rw [hcnt0def]
      exact le_trans h1 h2
    have hM1 : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by push_cast; positivity
    have h3 : ((cnt0 : ℕ) : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by
      have hc : ((cnt0 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hcard
      push_cast; linarith
    have h4 : ((((M + 1 : ℕ) : ℝ)⁻¹) ^ 2) * (((M + 1 : ℕ) : ℝ)) = (((M + 1 : ℕ) : ℝ)⁻¹) := by
      field_simp
    have h5 : (((M + 1 : ℕ) : ℝ)⁻¹) ≤ ((P : ℝ)⁻¹) := by
      apply inv_anti₀ hPR
      have hPM : ((P : ℝ)) ≤ (M : ℝ) := by exact_mod_cast (by omega : P ≤ M)
      push_cast
      linarith
    calc ((((M + 1 : ℕ) : ℝ)⁻¹) ^ 2) * ((cnt0 : ℕ) : ℝ)
        ≤ ((((M + 1 : ℕ) : ℝ)⁻¹) ^ 2) * (((M + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (((M + 1 : ℕ) : ℝ)⁻¹) := h4
      _ ≤ ((P : ℝ)⁻¹) := h5
      _ = 1 / (P : ℝ) := by rw [one_div]
  -- conclusion
  have hsum_eq : (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (if (P : ℝ) < (m : ℝ) ^ 2 + (n : ℝ) ^ 2
          then (((m : ℝ) ^ 2 + (n : ℝ) ^ 2)⁻¹ ^ 2) else 0)) = ∑ p ∈ Pset, F p := by
    rw [hPsetdef, Finset.sum_product]
  rw [hsum_eq]
  calc (∑ p ∈ Pset, F p)
      ≤ (∑ p ∈ Pset, X p) + (∑ p ∈ Pset, Y p) := hFA
    _ = (∑ j ∈ Finset.Icc 1 M, wt j * ((cnt j : ℕ) : ℝ))
          + ((((M + 1 : ℕ) : ℝ)⁻¹) ^ 2) * ((cnt0 : ℕ) : ℝ) := by rw [hXs, hYs]
    _ ≤ 3 / (P : ℝ) + 1 / (P : ℝ) := add_le_add hXb hYb
    _ = 4 / (P : ℝ) := by ring
    _ ≤ 8 / (P : ℝ) := by
        apply div_le_div_of_nonneg_right (by norm_num) (le_of_lt hPR)

end Work.FIArea1
