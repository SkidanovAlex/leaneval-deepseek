import Mathlib
import Submission.Commons.NumberTheory.ZMod.sum_minrep_weight_le

open scoped BigOperators

namespace Commons.NumberTheory.ZMod

theorem zmod_window_eq_Ioc (W p : ℕ) [NeZero p] (ε : ℝ) (g : ℕ → ℝ)
    (hW : 1 ≤ W) (hε : 0 < ε) (h2ε : 2 * ε < 1) :
    (∑ x : ZMod p, (if ε * (p : ℝ) ≤ (x.val : ℝ) ∧ (x.val : ℝ) ≤ 2 * ε * (p : ℝ) ∧
        Nat.Prime (W * x.val + 1) then g (W * x.val + 1) else 0))
      = ∑ n ∈ Finset.Ioc (W * ⌈ε * (p : ℝ)⌉₊) (W * ⌊2 * ε * (p : ℝ)⌋₊ + 1),
          (if n % W = 1 % W ∧ Nat.Prime n then g n else 0) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have h2εpos : (0 : ℝ) < 2 * ε := by linarith
  have h2εp_pos : (0 : ℝ) < 2 * ε * (p : ℝ) := mul_pos h2εpos hpR
  have hlt : 2 * ε * (p : ℝ) < (p : ℝ) := by
    have := mul_lt_mul_of_pos_right h2ε hpR
    simpa using this
  have hd_lt : ⌊2 * ε * (p : ℝ)⌋₊ < p := by
    rw [Nat.floor_lt (le_of_lt h2εp_pos)]
    exact hlt
  have hwin : ∀ j : ℕ, (ε * (p : ℝ) ≤ (j : ℝ) ∧ (j : ℝ) ≤ 2 * ε * (p : ℝ)) ↔
      j ∈ Finset.Icc ⌈ε * (p : ℝ)⌉₊ ⌊2 * ε * (p : ℝ)⌋₊ := by
    intro j
    constructor
    · intro ⟨h1, h2⟩
      exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr h1, Nat.le_floor h2⟩
    · intro hj
      rw [Finset.mem_Icc] at hj
      exact ⟨le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hj.1),
             le_trans (Nat.cast_le.mpr hj.2) (Nat.floor_le (le_of_lt h2εp_pos))⟩
  -- Step 1: reindex the sum over `ZMod p` as a sum over `Finset.range p`.
  have step1 :
      (∑ x : ZMod p, (if ε * (p : ℝ) ≤ (x.val : ℝ) ∧ (x.val : ℝ) ≤ 2 * ε * (p : ℝ) ∧
          Nat.Prime (W * x.val + 1) then g (W * x.val + 1) else 0))
        = ∑ j ∈ Finset.range p, (if ε * (p : ℝ) ≤ (j : ℝ) ∧ (j : ℝ) ≤ 2 * ε * (p : ℝ) ∧
          Nat.Prime (W * j + 1) then g (W * j + 1) else 0) := by
    have := sum_zmod_val_eq_sum_range p (fun j : ℕ =>
      (if ε * (p : ℝ) ≤ (j : ℝ) ∧ (j : ℝ) ≤ 2 * ε * (p : ℝ) ∧
        Nat.Prime (W * j + 1) then g (W * j + 1) else 0))
    simpa using this
  -- Step 2: the range sum restricts to the window `Icc ⌈εp⌉ ⌊2εp⌋`.
  have hsub : Finset.Icc ⌈ε * (p : ℝ)⌉₊ ⌊2 * ε * (p : ℝ)⌋₊ ⊆ Finset.range p := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact Finset.mem_range.mpr (lt_of_le_of_lt hj.2 hd_lt)
  have step2 :
      (∑ j ∈ Finset.range p, (if ε * (p : ℝ) ≤ (j : ℝ) ∧ (j : ℝ) ≤ 2 * ε * (p : ℝ) ∧
          Nat.Prime (W * j + 1) then g (W * j + 1) else 0))
        = ∑ j ∈ Finset.Icc ⌈ε * (p : ℝ)⌉₊ ⌊2 * ε * (p : ℝ)⌋₊,
            (if ε * (p : ℝ) ≤ (j : ℝ) ∧ (j : ℝ) ≤ 2 * ε * (p : ℝ) ∧
          Nat.Prime (W * j + 1) then g (W * j + 1) else 0) := by
    refine (Finset.sum_subset hsub ?_).symm
    intro j _ hjnot
    rw [if_neg (fun hc => hjnot ((hwin j).1 ⟨hc.1, hc.2.1⟩))]
  -- Step 3: on the window the real inequalities can be dropped.
  have step3 :
      (∑ j ∈ Finset.Icc ⌈ε * (p : ℝ)⌉₊ ⌊2 * ε * (p : ℝ)⌋₊,
          (if ε * (p : ℝ) ≤ (j : ℝ) ∧ (j : ℝ) ≤ 2 * ε * (p : ℝ) ∧
          Nat.Prime (W * j + 1) then g (W * j + 1) else 0))
        = ∑ j ∈ Finset.Icc ⌈ε * (p : ℝ)⌉₊ ⌊2 * ε * (p : ℝ)⌋₊,
            (if Nat.Prime (W * j + 1) then g (W * j + 1) else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hw := (hwin j).2 hj
    by_cases hpr : Nat.Prime (W * j + 1)
    · rw [if_pos ⟨hw.1, hw.2, hpr⟩, if_pos hpr]
    · rw [if_neg (fun h => hpr h.2.2), if_neg hpr]
  -- Step 4: the `Ioc` sum reindexes onto the window via `n ↦ W*n+1`.
  have step4 :
      (∑ n ∈ Finset.Ioc (W * ⌈ε * (p : ℝ)⌉₊) (W * ⌊2 * ε * (p : ℝ)⌋₊ + 1),
          (if n % W = 1 % W ∧ Nat.Prime n then g n else 0))
        = ∑ j ∈ Finset.Icc ⌈ε * (p : ℝ)⌉₊ ⌊2 * ε * (p : ℝ)⌋₊,
            (if Nat.Prime (W * j + 1) then g (W * j + 1) else 0) := by
    have hbij : (∑ j ∈ Finset.Icc ⌈ε * (p : ℝ)⌉₊ ⌊2 * ε * (p : ℝ)⌋₊,
            (if Nat.Prime (W * j + 1) then g (W * j + 1) else 0))
        = ∑ n ∈ (Finset.Ioc (W * ⌈ε * (p : ℝ)⌉₊) (W * ⌊2 * ε * (p : ℝ)⌋₊ + 1)).filter
              (fun n => n % W = 1 % W),
            (if n % W = 1 % W ∧ Nat.Prime n then g n else 0) := by
      apply Finset.sum_bij (fun j _ => W * j + 1)
      · intro j hj
        rw [Finset.mem_filter]
        obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
        refine ⟨?_, ?_⟩
        · rw [Finset.mem_Ioc]
          have h1 : W * ⌈ε * (p : ℝ)⌉₊ ≤ W * j := Nat.mul_le_mul_left W hj1
          have h2 : W * j ≤ W * ⌊2 * ε * (p : ℝ)⌋₊ := Nat.mul_le_mul_left W hj2
          omega
        · exact Nat.mul_add_mod W j 1
      · intro j1 _ j2 _ heq
        exact Nat.mul_left_cancel (by omega) (Nat.succ.inj heq)
      · intro n hn
        rw [Finset.mem_filter, Finset.mem_Ioc] at hn
        obtain ⟨⟨han, hnb⟩, hmod⟩ := hn
        have hnc : 1 ≤ n := by omega
        have h1mod : Nat.ModEq W 1 n := hmod.symm
        have hdvd : W ∣ n - 1 := (Nat.modEq_iff_dvd' (n := W) hnc).mp h1mod
        obtain ⟨k, hk⟩ := hdvd
        refine ⟨k, ?_, ?_⟩
        · rw [Finset.mem_Icc]
          have hkn : W * k + 1 = n := by omega
          have h1 : W * ⌈ε * (p : ℝ)⌉₊ ≤ W * k := by omega
          have h2 : W * k ≤ W * ⌊2 * ε * (p : ℝ)⌋₊ := by omega
          exact ⟨Nat.le_of_mul_le_mul_left h1 (by omega),
                 Nat.le_of_mul_le_mul_left h2 (by omega)⟩
        · show W * k + 1 = n
          omega
      · intro j _
        have hmod : (W * j + 1) % W = 1 % W := Nat.mul_add_mod W j 1
        by_cases hpr : Nat.Prime (W * j + 1)
        · rw [if_pos hpr, if_pos ⟨hmod, hpr⟩]
        · rw [if_neg hpr, if_neg (fun hc => hpr hc.2)]
    have ht't : (∑ n ∈ (Finset.Ioc (W * ⌈ε * (p : ℝ)⌉₊) (W * ⌊2 * ε * (p : ℝ)⌋₊ + 1)).filter
              (fun n => n % W = 1 % W),
            (if n % W = 1 % W ∧ Nat.Prime n then g n else 0))
        = ∑ n ∈ Finset.Ioc (W * ⌈ε * (p : ℝ)⌉₊) (W * ⌊2 * ε * (p : ℝ)⌋₊ + 1),
            (if n % W = 1 % W ∧ Nat.Prime n then g n else 0) := by
      refine Finset.sum_subset ?_ ?_
      · intro n hn
        rw [Finset.mem_filter] at hn
        exact hn.1
      · intro n hn hnnot
        rw [if_neg (fun hc => hnnot (Finset.mem_filter.mpr ⟨hn, hc.1⟩))]
    exact ht't.symm.trans hbij.symm
  rw [step1, step2, step3]
  exact step4.symm

end Commons.NumberTheory.ZMod
