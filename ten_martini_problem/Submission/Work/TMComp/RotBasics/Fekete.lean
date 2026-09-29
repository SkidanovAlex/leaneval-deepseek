import Mathlib

/-!
# Fekete's lemma for "almost additive" sequences

If `|s (n+m) - s n - s m| ≤ C` for all `n, m ≥ 1`, then `s n / n` converges, with the
explicit rate `|s n / n - L| ≤ C / n`.

The proof iterates the bound (`|s (k*n) - k s n| ≤ (k-1) C`), deduces the two-index bound
`|s n / n - s m / m| ≤ C/n + C/m`, and then takes `L := inf_j (s (j+1)/(j+1) + C/(j+1))`.
-/

namespace Work.TMComp.RotBasics

theorem fekete_of_almostAdditive {s : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → |s (n + m) - s n - s m| ≤ C) :
    ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => s n / (n : ℝ)) Filter.atTop (nhds L) ∧
      ∀ n : ℕ, 1 ≤ n → |s n / (n : ℝ) - L| ≤ C / (n : ℝ) := by
  have hmul : ∀ (k n : ℕ), 1 ≤ k → 1 ≤ n → |s (k * n) - (k : ℝ) * s n| ≤ ((k : ℝ) - 1) * C := by
    intro k
    induction k with
    | zero => intro n hk _; exact absurd hk (by norm_num)
    | succ k ih =>
      intro n hk hn
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        simp
      · have hrec : |s (k * n) - (k : ℝ) * s n| ≤ ((k : ℝ) - 1) * C := ih n hkpos hn
        have hkn : 1 ≤ k * n :=
          Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp hkpos)
            (Nat.pos_iff_ne_zero.mp hn))
        have hstep : |s (k * n + n) - s (k * n) - s n| ≤ C := h (k * n) n hkn hn
        have hsplit : s ((k + 1) * n) - ((k : ℝ) + 1) * s n
            = (s (k * n + n) - s (k * n) - s n) + (s (k * n) - (k : ℝ) * s n) := by
          rw [Nat.add_mul, one_mul]
          ring
        have hgoal : |s ((k + 1) * n) - ((k : ℝ) + 1) * s n| ≤ ((k : ℝ) + 1 - 1) * C := by
          rw [hsplit]
          calc |(s (k * n + n) - s (k * n) - s n) + (s (k * n) - (k : ℝ) * s n)|
              ≤ |s (k * n + n) - s (k * n) - s n| + |s (k * n) - (k : ℝ) * s n| := abs_add_le _ _
            _ ≤ C + ((k : ℝ) - 1) * C := add_le_add hstep hrec
            _ = ((k : ℝ) + 1 - 1) * C := by ring
        simpa [Nat.cast_add, Nat.cast_one] using hgoal

  have hdiff : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
      |s n / (n : ℝ) - s m / (m : ℝ)| ≤ C / (n : ℝ) + C / (m : ℝ) := by
    intro n m hn hm
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hmn : 1 ≤ m * n :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp hm)
        (Nat.pos_iff_ne_zero.mp hn))
    have h1 := hmul m n hm hn
    have h2 := hmul n m hn hm
    have h2' : |s (m * n) - (n : ℝ) * s m| ≤ ((n : ℝ) - 1) * C := by
      rw [Nat.mul_comm]; exact h2
    have hprod : (0 : ℝ) < (m : ℝ) * (n : ℝ) := mul_pos hmpos hnpos
    have e1 : s (m * n) / ((m * n : ℕ) : ℝ) - s n / (n : ℝ)
        = (s (m * n) - (m : ℝ) * s n) / ((m : ℝ) * (n : ℝ)) := by
      push_cast
      field_simp
    have e2 : s (m * n) / ((m * n : ℕ) : ℝ) - s m / (m : ℝ)
        = (s (m * n) - (n : ℝ) * s m) / ((n : ℝ) * (m : ℝ)) := by
      push_cast
      field_simp
    have b1 : |s (m * n) / ((m * n : ℕ) : ℝ) - s n / (n : ℝ)| ≤ C / (n : ℝ) := by
      rw [e1, abs_div, abs_of_pos hprod, div_le_iff₀ hprod]
      have hle : ((m : ℝ) - 1) * C ≤ C * (m : ℝ) := by nlinarith [hC, hmpos]
      have hmm : (C / (n : ℝ)) * ((m : ℝ) * (n : ℝ)) = C * (m : ℝ) := by
        field_simp
      rw [hmm]
      nlinarith [h1, hle]
    have b2 : |s (m * n) / ((m * n : ℕ) : ℝ) - s m / (m : ℝ)| ≤ C / (m : ℝ) := by
      rw [e2, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) * (m : ℝ)),
        div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) * (m : ℝ))]
      have hle : ((n : ℝ) - 1) * C ≤ C * (n : ℝ) := by nlinarith [hC, hnpos]
      have hmm : (C / (m : ℝ)) * ((n : ℝ) * (m : ℝ)) = C * (n : ℝ) := by
        field_simp
      rw [hmm]
      nlinarith [h2', hle]
    calc |s n / (n : ℝ) - s m / (m : ℝ)|
        ≤ |s n / (n : ℝ) - s (m * n) / ((m * n : ℕ) : ℝ)|
          + |s (m * n) / ((m * n : ℕ) : ℝ) - s m / (m : ℝ)| := abs_sub_le _ _ _
      _ ≤ C / (n : ℝ) + C / (m : ℝ) := by
          refine add_le_add ?_ b2
          rw [abs_sub_comm]
          exact b1
  set f : ℕ → ℝ := fun j => s (j + 1) / ((j + 1 : ℕ) : ℝ) + C / ((j + 1 : ℕ) : ℝ) with hf
  have hbdd : BddBelow (Set.range f) := by
    refine ⟨s 1 / 1 - C / 1, ?_⟩
    rintro x ⟨j, rfl⟩
    have hj : 1 ≤ j + 1 := Nat.succ_le_succ (Nat.zero_le j)
    have h1 := hdiff (j + 1) 1 hj le_rfl
    have h2 := (abs_le.mp h1).1
    simp only [hf]
    norm_num at h2 ⊢
    linarith
  have key : ∀ n : ℕ, 1 ≤ n → |s n / (n : ℝ) - sInf (Set.range f)| ≤ C / (n : ℝ) := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsub : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have hsub' : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      exact_mod_cast hsub
    have hmem : f (n - 1) ∈ Set.range f := ⟨n - 1, rfl⟩
    have h1 : sInf (Set.range f) ≤ s n / (n : ℝ) + C / (n : ℝ) := by
      have h := csInf_le hbdd hmem
      rw [hf] at h
      simp only at h
      rw [hsub] at h
      exact h
    have h2 : s n / (n : ℝ) - C / (n : ℝ) ≤ sInf (Set.range f) := by
      apply le_csInf (⟨f 0, 0, rfl⟩ : (Set.range f).Nonempty)
      rintro x ⟨j, rfl⟩
      have hj : 1 ≤ j + 1 := Nat.succ_le_succ (Nat.zero_le j)
      have h3 := hdiff n (j + 1) hn hj
      have h4 := (abs_le.mp h3).2
      simp only [hf]
      linarith
    rw [abs_le]
    constructor <;> linarith
  refine ⟨sInf (Set.range f), ?_, key⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  have hN1 : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exfalso
      rw [h] at hN
      simp only [Nat.cast_zero] at hN
      have h0 : 0 ≤ C / ε := div_nonneg hC (le_of_lt hε)
      linarith
    · exact h
  refine ⟨N, fun n hn => ?_⟩
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  have hCn : C / (n : ℝ) ≤ C / (N : ℝ) :=
    div_le_div_of_nonneg_left hC hNpos (by exact_mod_cast hn)
  have hlt : C / (N : ℝ) < ε := by
    rw [div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hε] at hN
    linarith
  have hr := key n (le_trans hN1 hn)
  rw [Real.dist_eq]
  linarith

end Work.TMComp.RotBasics
