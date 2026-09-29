import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.CDT.PureDenom
import Submission.Work.CPull.B2_coeff_bound
import Submission.Work.CPull.norm_coeff_B3_le
import Submission.Work.CPull.B4_coeff_bound
import Submission.Work.B5pull.coeff_bounds

namespace Work.C17I

noncomputable section

/-! ### Toolbox -/

/-- The `ℚ → ℂ` cast is compatible with absolute values. -/
private lemma norm_ratCast_eq (q : ℚ) : ‖((q : ℚ) : ℂ)‖ = ((|q| : ℚ) : ℝ) := by
  rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs, Rat.cast_abs]

/-- A geometric factor `ρ^n` with `0 ≤ ρ ≤ 1` is at most `1`. -/
private lemma pow_le_one_of_mem_Icc {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (n : ℕ) : ρ ^ n ≤ 1 :=
  pow_le_one₀ h0 h1

/-! ### The seven coefficients, each bounded by `16` -/

/-- `B₁ = 1`, so `[yⁿ]B₁ ∈ {0,1}`. -/
private lemma B1_coeff_bound (n : ℕ) :
    ‖((PowerSeries.coeff n Submission.CDTPlan.B1 : ℚ) : ℂ)‖ ≤ 1 := by
  rw [Submission.CDTPlan.B1, PowerSeries.coeff_one]
  by_cases h : n = 0
  · rw [if_pos h, norm_ratCast_eq]
    norm_num
  · rw [if_neg h, Rat.cast_zero, norm_zero]
    norm_num

/-- `B₂`: known geometric bound `3·4^{-n}` (`Work.CPull.B2_coeff_bound`). -/
private lemma B2_coeff_bound_16 (n : ℕ) :
    ‖((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ)‖ ≤ 16 := by
  refine le_trans (Work.CPull.B2_coeff_bound n) ?_
  have h := pow_le_one_of_mem_Icc (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1:ℝ)/4 ≤ 1) n
  have h0 : (0:ℝ) ≤ (1/4:ℝ)^n := by positivity
  nlinarith

/-- `B₃`: known geometric bound `2·4^{-n}` (`Work.CPull.norm_coeff_B3_le`). -/
private lemma B3_coeff_bound_16 (n : ℕ) :
    ‖((PowerSeries.coeff n Submission.CDTPlan.B3 : ℚ) : ℂ)‖ ≤ 16 := by
  refine le_trans (Work.CPull.norm_coeff_B3_le n) ?_
  have h := pow_le_one_of_mem_Icc (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1:ℝ)/4 ≤ 1) n
  have h0 : (0:ℝ) ≤ (1/4:ℝ)^n := by positivity
  nlinarith

/-- `B₄`: known geometric bound `16·2^{-n}` (`Work.CPull.B4_coeff_bound`). -/
private lemma B4_coeff_bound_16 (n : ℕ) :
    ‖((PowerSeries.coeff n Submission.CDTPlan.B4 : ℚ) : ℂ)‖ ≤ 16 := by
  refine le_trans (Work.CPull.B4_coeff_bound n) ?_
  have h := pow_le_one_of_mem_Icc (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 ≤ 1) n
  have h0 : (0:ℝ) ≤ (1/2:ℝ)^n := by positivity
  nlinarith

/-- `B₅`: known geometric bound `4·4^{-n}` (`Work.B5pull.coeff_bounds`). -/
private lemma B5_coeff_bound_16 (n : ℕ) :
    ‖((PowerSeries.coeff n Submission.CDTPlan.B5 : ℚ) : ℂ)‖ ≤ 16 := by
  refine le_trans (Work.B5pull.coeff_bounds.1 n) ?_
  have h := pow_le_one_of_mem_Icc (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1:ℝ)/4 ≤ 1) n
  have h0 : (0:ℝ) ≤ (1/4:ℝ)^n := by positivity
  nlinarith

/-! ### `B₆` -/

/-- `[yⁿ]B₆` is the pure-denominator coefficient `b6 n`. -/
private lemma coeff_B6_eq (n : ℕ) :
    PowerSeries.coeff n Submission.CDTPlan.B6 = Submission.CDT.PureDenom.b6 n := by
  rw [Submission.CDTPlan.B6, PowerSeries.coeff_mk, Submission.CDT.PureDenom.b6]

private lemma b6_nonneg (n : ℕ) : (0:ℚ) ≤ Submission.CDT.PureDenom.b6 n := by
  rw [Submission.CDT.PureDenom.b6]
  split_ifs with h
  · norm_num
  · positivity

/-- `[yⁿ]B₆ = 1/(n³ C(2n,n)) ≤ 1`: the identity `n²·b6 n = 1/(n·C(2n,n))` of
`PureDenom`, with `C(2n,n) ≥ 1`. -/
private lemma B6_coeff_bound_16 (n : ℕ) :
    ‖((PowerSeries.coeff n Submission.CDTPlan.B6 : ℚ) : ℂ)‖ ≤ 16 := by
  rw [coeff_B6_eq, norm_ratCast_eq]
  have hnn := b6_nonneg n
  have hle : Submission.CDT.PureDenom.b6 n ≤ 1 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      rw [Submission.CDT.PureDenom.b6, if_pos rfl]
      norm_num
    · have hn1 : (1:ℚ) ≤ (n:ℚ) := by exact_mod_cast h
      have hC1 : (1:ℚ) ≤ (Nat.choose (2*n) n : ℚ) := by
        exact_mod_cast Nat.choose_pos (by omega : n ≤ 2*n)
      have hden : (0:ℚ) < (n:ℚ) * (Nat.choose (2*n) n : ℚ) := by positivity
      have hkey : (n:ℚ)^2 * Submission.CDT.PureDenom.b6 n ≤ 1 := by
        rw [Submission.CDT.PureDenom.n_sq_mul_b6_eq n h, div_le_one hden]
        nlinarith
      have hn2 : (1:ℚ) ≤ (n:ℚ)^2 := by nlinarith
      calc Submission.CDT.PureDenom.b6 n = 1 * Submission.CDT.PureDenom.b6 n := by ring
        _ ≤ (n:ℚ)^2 * Submission.CDT.PureDenom.b6 n :=
              mul_le_mul_of_nonneg_right hn2 hnn
        _ ≤ 1 := hkey
  rw [abs_of_nonneg hnn]
  have : ((Submission.CDT.PureDenom.b6 n : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hle
  linarith

/-! ### `B₇ = ∫B₄/y` -/

/-- `[yⁿ]B₇ = [yⁿ]B₄ / n`, bounded by `|[yⁿ]B₄|`. -/
private lemma B7_coeff_bound_16 (n : ℕ) :
    ‖((PowerSeries.coeff n Submission.CDTPlan.B7 : ℚ) : ℂ)‖ ≤ 16 := by
  rw [Submission.CDTPlan.B7, PowerSeries.coeff_mk]
  by_cases h : n = 0
  · rw [if_pos h, Rat.cast_zero, norm_zero]
    norm_num
  · rw [if_neg h]
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
    have hcast : ((PowerSeries.coeff n Submission.CDTPlan.B4 / (n:ℚ) : ℚ) : ℂ)
        = ((PowerSeries.coeff n Submission.CDTPlan.B4 : ℚ) : ℂ) / ((n:ℚ) : ℂ) := by
      push_cast; ring
    rw [hcast, norm_div]
    have hden : (1:ℝ) ≤ ‖((n:ℚ) : ℂ)‖ := by
      rw [norm_ratCast_eq, abs_of_nonneg (by positivity : (0:ℚ) ≤ (n:ℚ))]
      exact_mod_cast hn1
    have hB4 : ‖((PowerSeries.coeff n Submission.CDTPlan.B4 : ℚ) : ℂ)‖ ≤ 16 :=
      B4_coeff_bound_16 n
    have hpos : (0:ℝ) < ‖((n:ℚ) : ℂ)‖ := by linarith
    have h1 : ‖((PowerSeries.coeff n Submission.CDTPlan.B4 : ℚ) : ℂ)‖ / ‖((n:ℚ):ℂ)‖
        ≤ ‖((PowerSeries.coeff n Submission.CDTPlan.B4 : ℚ) : ℂ)‖ := by
      rw [div_le_iff₀ hpos]
      nlinarith [norm_nonneg ((PowerSeries.coeff n Submission.CDTPlan.B4 : ℚ) : ℂ)]
    linarith

/-! ### Assembly -/

/-- Every coefficient of every one of the seven pure series is bounded by `16`. -/
private lemma pureB_coeff_bound_16 (i : Fin 7) (n : ℕ) :
    ‖((PowerSeries.coeff n (Submission.CDTPlan.pureB i) : ℚ) : ℂ)‖ ≤ 16 := by
  fin_cases i
  · exact le_trans (B1_coeff_bound n) (by norm_num)
  · exact B2_coeff_bound_16 n
  · exact B3_coeff_bound_16 n
  · exact B4_coeff_bound_16 n
  · exact B5_coeff_bound_16 n
  · exact B6_coeff_bound_16 n
  · exact B7_coeff_bound_16 n

/-- Guidance from the requester (area C17, input for `Work.C17.relation_to_LC`).

# Geometric coefficient bound for the seven pure series `B₁,…,B₇`

`Submission.CDTPlan.pureB` is the family `B₁ = 1`,
`B₂ = Σ_{n≥2} 2 (n-2)! n! / (2n)! y^n`, `B₃ = Σ_{n≥1} (n-1)!² / (2n)! y^n`,
`B₄ = Σ_{n≥1} 4/16^{n-1} Σ_k C(2k,k) C(2n-2-2k, n-1-k) / ((2k-1)(2n-2k+1)²) y^n`,
`B₅ = Σ_{n≥1} (n-1)!²/((2n-1)!(2n-1)) y^n`, `B₆ = Σ_{n≥1} (n-1)!²/(n (2n)!) y^n`,
`B₇ = Σ_{n≥1} coeff_n B₄ / n`.

All these coefficient sequences decay at least like `poly(n) · 4^{-n}` (the `(2n)!`-denominators
and the `16^n` in `B₄`), so a bound `C · 2^n` is comfortable.  Ingredients:
`Nat.factorial_le_pow`/`Nat.factorial_pos`, `Nat.centralBinom_le` (or `Nat.choose_le_pow`:
`C(2k,k) ≤ 4^k`), `Finset.sum` estimates (`Finset.sum_le_sum`), and `Nat.cast` bookkeeping over
`ℚ → ℂ`.

This is a standalone arithmetic result about the explicit series; no workspace-specific material
beyond `Submission.CDTPlan.pureB` and its seven components is used. -/

theorem pureB_coeff_bound (i : Fin 7) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖((PowerSeries.coeff n (Submission.CDTPlan.pureB i) : ℚ) : ℂ)‖ ≤ C * 2 ^ n := by
  refine ⟨16, by norm_num, fun n => ?_⟩
  refine le_trans (pureB_coeff_bound_16 i n) ?_
  have h2 : (1:ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
  calc (16:ℝ) = 16 * 1 := by ring
    _ ≤ 16 * 2 ^ n := by gcongr

end

end Work.C17I
