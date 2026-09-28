import Mathlib

namespace Work.HP.HP2

/-- Existential threshold for the purely Archimedean comparison in `tube_ok_threshold`: for
positive `Cfront, ccone` and `Ksub`, there is an exponent `m > n` and a threshold `A₀ ≥ exp 1` such
that for all `B ≥ A₀` the quantity
`Cfront * ((log B)^{-m/Ksub} + (log B)^{-m}) * (log B)^n` is at most `ccone / 2`.
(The key point is that both exponents `-m/Ksub` and `-m` beat the factor `(log B)^n` once
`m > n max(1, Ksub)`, so the product tends to `0` as `B → ∞`.) -/
lemma log_rpow_threshold (n : ℕ) (Cfront ccone Ksub : ℝ)
    (hCfront : 0 < Cfront) (hKsub : 0 < Ksub) (hccone : 0 < ccone) :
    ∃ m : ℕ, n < m ∧ ∃ A₀ : ℝ, Real.exp 1 ≤ A₀ ∧ ∀ B : ℝ, A₀ ≤ B →
        Cfront * ((Real.log B) ^ (-((m : ℝ) / Ksub)) + (Real.log B) ^ (-(m : ℝ)))
          * (Real.log B) ^ n ≤ ccone / 2 := by
  -- Choose `m` with `(n:ℝ)+1 ≤ m` and `Ksub * ((n:ℝ)+1) ≤ m`, so that `m > n` and `m/Ksub > n`.
  obtain ⟨m, hmn, hmK⟩ : ∃ m : ℕ, (n:ℝ) + 1 ≤ (m:ℝ) ∧ Ksub * ((n:ℝ)+1) ≤ (m:ℝ) := by
    obtain ⟨m, hm⟩ := exists_nat_gt (max ((n:ℝ)+1) (Ksub * ((n:ℝ)+1)))
    exact ⟨m, le_of_lt (lt_of_le_of_lt (le_max_left _ _) hm),
             le_of_lt (lt_of_le_of_lt (le_max_right _ _) hm)⟩
  have hnm : n < m := by
    have h : (n:ℝ) < (m:ℝ) := by linarith
    exact_mod_cast h
  refine ⟨m, hnm, Real.exp (max 1 (4 * Cfront / ccone)),
    Real.exp_le_exp.mpr (le_max_left _ _), ?_⟩
  intro B hB
  set L := Real.log B with hL
  have hA0pos : 0 < Real.exp (max 1 (4*Cfront/ccone)) := Real.exp_pos _
  -- The threshold forces `log B ≥ max 1 (4 Cfront / ccone)`.
  have hlog : max 1 (4*Cfront/ccone) ≤ L := by
    have h1 : Real.log (Real.exp (max 1 (4*Cfront/ccone))) ≤ Real.log B :=
      Real.log_le_log hA0pos hB
    rwa [Real.log_exp] at h1
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hlog
  have hL4 : 4*Cfront/ccone ≤ L := le_trans (le_max_right _ _) hlog
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hn1 : (n:ℝ) + 1 ≤ (m:ℝ)/Ksub := by
    rw [le_div_iff₀ hKsub]; linarith [hmK]
  -- `(log B)^{-m/Ksub} * (log B)^n = (log B)^{n - m/Ksub} ≤ (log B)^{-1}`.
  have hA : L ^ (-((m:ℝ)/Ksub)) * L ^ n ≤ 1 / L := by
    have hexp : -((m:ℝ)/Ksub) + (n:ℝ) ≤ -1 := by linarith [hn1]
    have h1 : L ^ (-((m:ℝ)/Ksub) + (n:ℝ)) ≤ L ^ (-1:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 hexp
    rw [Real.rpow_add hLpos] at h1
    rw [Real.rpow_natCast] at h1
    rw [Real.rpow_neg_one] at h1
    rwa [one_div]
  -- `(log B)^{-m} * (log B)^n = (log B)^{n - m} ≤ (log B)^{-1}`.
  have hB2 : L ^ (-(m:ℝ)) * L ^ n ≤ 1 / L := by
    have hexp : -(m:ℝ) + (n:ℝ) ≤ -1 := by linarith
    have h1 : L ^ (-(m:ℝ) + (n:ℝ)) ≤ L ^ (-1:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 hexp
    rw [Real.rpow_add hLpos] at h1
    rw [Real.rpow_natCast] at h1
    rw [Real.rpow_neg_one] at h1
    rwa [one_div]
  have hsum : (L ^ (-((m:ℝ)/Ksub)) + L ^ (-(m:ℝ))) * L ^ n ≤ 2 / L := by
    have hdist : (L ^ (-((m:ℝ)/Ksub)) + L ^ (-(m:ℝ))) * L ^ n
        = L ^ (-((m:ℝ)/Ksub)) * L ^ n + L ^ (-(m:ℝ)) * L ^ n := by ring
    rw [hdist]
    have h2L : (1:ℝ)/L + 1/L = 2/L := by ring
    linarith [hA, hB2, h2L]
  have hmul : 4 * Cfront ≤ ccone * L := by
    have h := mul_le_mul_of_nonneg_right hL4 (le_of_lt hccone)
    rw [div_mul_cancel₀ _ (ne_of_gt hccone)] at h
    rw [mul_comm L ccone] at h
    exact h
  have hfinal : Cfront * (2 / L) ≤ ccone / 2 := by
    have h2 : Cfront * (2/L) = 2*Cfront/L := by ring
    rw [h2, div_le_div_iff₀ hLpos (by norm_num)]
    linarith
  calc Cfront * (L ^ (-((m:ℝ)/Ksub)) + L ^ (-(m:ℝ))) * L ^ n
      = Cfront * ((L ^ (-((m:ℝ)/Ksub)) + L ^ (-(m:ℝ))) * L ^ n) := by ring
    _ ≤ Cfront * (2 / L) := mul_le_mul_of_nonneg_left hsum (le_of_lt hCfront)
    _ ≤ ccone / 2 := hfinal

end Work.HP.HP2
