import Mathlib
import Submission.Work.KMTPlan.A6.lacunaryCard

namespace Work.KMTPlan.A6

/-- Elementary Bernoulli-type bound for base `2`: `1 + s/2 ≤ 2^s` for `s ≥ 0`.
(Since `2^s = exp (s log 2)` and `log 2 > 1/2`.) -/
lemma one_add_half_le_two_rpow (s : ℝ) (hs : 0 ≤ s) : 1 + s / 2 ≤ (2 : ℝ) ^ s := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h1 : 1 + s * Real.log 2 ≤ (2 : ℝ) ^ s := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm (Real.log 2) s]
    have := Real.add_one_le_exp (s * Real.log 2)
    linarith
  have h2 : 1 + s / 2 ≤ 1 + s * Real.log 2 := by
    have := mul_le_mul_of_nonneg_left hlog hs
    linarith
  linarith

/-- Elementary: `2 * u ≤ 2^u` for `u ≥ 2`. -/
lemma two_mul_le_two_rpow (u : ℝ) (hu : 2 ≤ u) : 2 * u ≤ (2 : ℝ) ^ u := by
  have hs : 0 ≤ u - 2 := by linarith
  have hsplit : (2 : ℝ) ^ u = 4 * (2 : ℝ) ^ (u - 2) := by
    calc (2 : ℝ) ^ u = (2 : ℝ) ^ (2 + (u - 2)) := by congr 1; ring
      _ = (2 : ℝ) ^ (2 : ℝ) * (2 : ℝ) ^ (u - 2) := Real.rpow_add (by norm_num) 2 (u - 2)
      _ = 4 * (2 : ℝ) ^ (u - 2) := by rw [Real.rpow_two]; ring
  rw [hsplit]
  have hb := one_add_half_le_two_rpow (u - 2) hs
  nlinarith

/-- The elementary threshold inequality behind `L_le_of_threshold_fail`: if `b ≥ 4 C₀ + Cρ + 5`
(and `C₀, Cρ ≥ 1`) then `2 C₀ b + Cρ 2^b + 2 ≤ 2^{2b-2}`. -/
lemma two_mul_add_two_le_two_rpow (C₀ Cρ b : ℝ) (hC₀ : 1 ≤ C₀) (hCρ : 1 ≤ Cρ)
    (hb : 4 * C₀ + Cρ + 5 ≤ b) :
    2 * C₀ * b + Cρ * (2 : ℝ) ^ b + 2 ≤ (2 : ℝ) ^ (2 * b - 2) := by
  have hb4 : (4 : ℝ) ≤ b := by linarith
  have hb8 : (8 : ℝ) ≤ b := by linarith
  have hbC : 4 * C₀ ≤ b := by linarith
  have hbCρ : Cρ + 4 ≤ b := by linarith
  have hb0 : (0 : ℝ) ≤ b := by linarith
  -- `2^{2b-4} = 2^b · 2^{b-4}` and `2^{2b-2} = 4 · 2^{2b-4}`
  have h2b : (2 : ℝ) ^ (2 * b - 4) = (2 : ℝ) ^ b * (2 : ℝ) ^ (b - 4) := by
    rw [show 2 * b - 4 = b + (b - 4) by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hrat : (2 : ℝ) ^ (2 * b - 2) = 4 * (2 : ℝ) ^ (2 * b - 4) := by
    rw [show 2 * b - 2 = (2 * b - 4) + 2 by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [Real.rpow_two]; ring
  have hPb : 0 ≤ (2 : ℝ) ^ b := Real.rpow_nonneg (by norm_num) _
  have hP4 : 0 ≤ (2 : ℝ) ^ (b - 4) := Real.rpow_nonneg (by norm_num) _
  -- `b ≤ 2^b`, `2(b-4) ≤ 2^{b-4}`
  have hb_le : b ≤ (2 : ℝ) ^ b := by
    have h1 : (2 : ℝ) * (b / 2) ≤ (2 : ℝ) ^ (b / 2) := two_mul_le_two_rpow (b / 2) (by linarith)
    have h2 : (2 : ℝ) ^ (b / 2) ≤ (2 : ℝ) ^ b :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    linarith
  have hpow4 : 2 * (b - 4) ≤ (2 : ℝ) ^ (b - 4) := two_mul_le_two_rpow (b - 4) (by linarith)
  -- the three individual bounds
  have hterm1 : 2 * C₀ * b ≤ (2 : ℝ) ^ b * (2 : ℝ) ^ (b - 4) := by
    have hp1 : 2 * C₀ * b ≤ b * (b / 2) := by
      have h1 : 4 * C₀ * (b / 2) ≤ b * (b / 2) := mul_le_mul_of_nonneg_right hbC (by linarith)
      linarith
    have hp2 : b * (b / 2) ≤ b * (2 * (b - 4)) := by
      have h1 : b / 2 ≤ 2 * (b - 4) := by linarith
      exact mul_le_mul_of_nonneg_left h1 hb0
    have hp3 : b * (2 * (b - 4)) ≤ (2 : ℝ) ^ b * (2 : ℝ) ^ (b - 4) := by
      have h1 : b * (2 * (b - 4)) ≤ (2 : ℝ) ^ b * (2 * (b - 4)) :=
        mul_le_mul_of_nonneg_right hb_le (by linarith)
      have h2 : (2 : ℝ) ^ b * (2 * (b - 4)) ≤ (2 : ℝ) ^ b * (2 : ℝ) ^ (b - 4) :=
        mul_le_mul_of_nonneg_left hpow4 hPb
      linarith
    linarith
  have hterm2 : Cρ * (2 : ℝ) ^ b ≤ (2 : ℝ) ^ b * (2 : ℝ) ^ (b - 4) := by
    have h1 : Cρ ≤ (2 : ℝ) ^ (b - 4) := by linarith
    calc Cρ * (2 : ℝ) ^ b ≤ (2 : ℝ) ^ (b - 4) * (2 : ℝ) ^ b :=
          mul_le_mul_of_nonneg_right h1 hPb
      _ = (2 : ℝ) ^ b * (2 : ℝ) ^ (b - 4) := by ring
  have hterm3 : 2 ≤ (2 : ℝ) ^ b * (2 : ℝ) ^ (b - 4) := by
    rw [← h2b]
    have h : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ (2 * b - 4) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    rwa [Real.rpow_one] at h
  have hsum : 2 * C₀ * b + Cρ * (2 : ℝ) ^ b + 2 ≤ 3 * ((2 : ℝ) ^ b * (2 : ℝ) ^ (b - 4)) := by
    linarith
  have hfin : 3 * ((2 : ℝ) ^ b * (2 : ℝ) ^ (b - 4)) ≤ (2 : ℝ) ^ (2 * b - 2) := by
    rw [hrat, ← h2b]
    have h0 : 0 ≤ (2 : ℝ) ^ (2 * b - 4) := Real.rpow_nonneg (by norm_num) _
    linarith
  linarith

/-- **Failure of the major-arc threshold bounds the scale.**  If `ρ C₀ ≤ 1/2`, then for all
sufficiently large `L` the inequality
`k₁ + Cρ 2^{ρ l₁} + 2 ≤ 2^{L/C₀ - 2}` holds whenever `k₁, l₁ ≤ L`; hence if it *fails*, `L`
is bounded in terms of `ρ, C₀, Cρ`. -/
theorem L_le_of_threshold_fail (ρ : ℝ) (hρ : 0 < ρ) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (Cρ : ℝ) (hCρ : 1 ≤ Cρ) (hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 2) :
    ∃ L₀ : ℕ, ∀ (L k₁ l₁ : ℕ), k₁ ≤ L → l₁ ≤ L →
      ¬ ((k₁ : ℝ) + Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) + 2 ≤ (2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2)) →
      L ≤ L₀ := by
  refine ⟨Nat.ceil (2 * (C₀ : ℝ) * (4 * (C₀ : ℝ) + Cρ + 5)), ?_⟩
  intro L k₁ l₁ hk hl hfail
  by_contra hcon
  have hconLT : Nat.ceil (2 * (C₀ : ℝ) * (4 * (C₀ : ℝ) + Cρ + 5)) < L := not_le.mp hcon
  have hC₀pos : (0 : ℝ) < (C₀ : ℝ) := by exact_mod_cast (by omega : 0 < C₀)
  have hC₀ne : (C₀ : ℝ) ≠ 0 := ne_of_gt hC₀pos
  set b : ℝ := (L : ℝ) / (2 * (C₀ : ℝ)) with hbdef
  -- `b` is past the threshold
  have hbB : 4 * (C₀ : ℝ) + Cρ + 5 ≤ b := by
    have h1 : (Nat.ceil (2 * (C₀ : ℝ) * (4 * (C₀ : ℝ) + Cρ + 5)) : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast (le_of_lt hconLT)
    have h2 : 2 * (C₀ : ℝ) * (4 * (C₀ : ℝ) + Cρ + 5) ≤ (L : ℝ) :=
      le_trans (Nat.le_ceil _) h1
    rw [hbdef, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (C₀ : ℝ))]
    linarith
  -- `L = 2 C₀ b`
  have hLb : (L : ℝ) = 2 * (C₀ : ℝ) * b := by
    rw [hbdef]
    field_simp
  have hLCb : (L : ℝ) / (C₀ : ℝ) = 2 * b := by
    rw [hLb]
    field_simp
  have hkey := two_mul_add_two_le_two_rpow (C₀ : ℝ) Cρ b (by exact_mod_cast hC₀) hCρ hbB
  -- bound the two variable terms
  have hk' : (k₁ : ℝ) ≤ 2 * (C₀ : ℝ) * b := by
    have h : (k₁ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hk
    linarith
  have hρLb : ρ * (L : ℝ) ≤ b := by
    rw [hbdef, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (C₀ : ℝ))]
    nlinarith [hρC₀, hρ.le]
  have hl₁ : ρ * (l₁ : ℝ) ≤ ρ * (L : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hl) hρ.le
  have hpowl : (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ (2 : ℝ) ^ b := by
    calc (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hl₁
      _ ≤ (2 : ℝ) ^ b := Real.rpow_le_rpow_of_exponent_le (by norm_num) hρLb
  have hCpow : Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ Cρ * (2 : ℝ) ^ b :=
    mul_le_mul_of_nonneg_left hpowl (by linarith)
  have hmain : (k₁ : ℝ) + Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) + 2 ≤ (2 : ℝ) ^ (2 * b - 2) := by
    linarith
  exact hfail (by rw [hLCb]; exact hmain)

end Work.KMTPlan.A6
