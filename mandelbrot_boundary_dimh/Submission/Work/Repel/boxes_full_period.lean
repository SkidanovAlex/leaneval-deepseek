import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.counting

/-!
# REPEL: the full-period level-0 box window

Shishikura §6, Step 3, level-0 count with **full real period**.  The box

`B η n = {z | n < Re z < n + 1, η + log(1/2)/2π < Im z < η + log(3/2)/2π}`

has real width `1` (so that `π(z) = exp(2πiz)` is injective on it) and imaginary height
`< 1/8`.  We show that at least `η/8` of its integer translates `n` sit inside the counting
disc `Dflat η = closedBall (iη) (|η|/8)`.

The estimate is sharp for the constant in the statement: `B η n ⊆ Dflat η` as soon as
`max(|n|, |n+1|)² + (log 2/2π)² ≤ (η/8)²`, i.e. for `|n| ≲ η/16`; taking the `2⌊η/16⌋ + 2`
integers `n ∈ [-M, M-1]` with `M = ⌊η/16⌋ + 1` gives `card = 2M ≥ η/8`.
-/

namespace Work.Repel

open Complex Set Metric

theorem boxes_full_period (η : ℝ) (hη : 100 ≤ η) :
    ∃ S : Finset ℤ, η / 8 ≤ (S.card : ℝ) ∧
      ∀ n ∈ S, ({z : ℂ | (n : ℝ) < z.re ∧ z.re < (n : ℝ) + 1 ∧
          η + Real.log (1 / 2) / (2 * Real.pi) < z.im ∧
          z.im < η + Real.log (3 / 2) / (2 * Real.pi)} ⊆ Work.Repel.Dflat η) := by
  classical
  -- the imaginary half-height `c = log 2 / 2π`
  set c : ℝ := Real.log 2 / (2 * Real.pi) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hcle : c ≤ 1 / 8 := by
    rw [hcdef]
    have h4 : 4 * Real.log 2 < Real.pi := by
      have h1 := Real.log_two_lt_d9
      have h2 := Real.pi_gt_d6
      linarith
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
    linarith
  have hc2 : c ^ 2 ≤ 1 / 64 := by nlinarith [hcpos, hcle]
  -- the two logarithmic endpoints, in terms of `c`
  have hloghalf : Real.log (1 / 2 : ℝ) / (2 * Real.pi) = -c := by
    have h : Real.log (1 / 2 : ℝ) = -(Real.log 2) := by
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
    rw [h, hcdef]; ring
  have hlog32 : Real.log (3 / 2 : ℝ) / (2 * Real.pi) < c := by
    rw [hcdef]
    exact div_lt_div_of_pos_right (Real.log_lt_log (by norm_num) (by norm_num)) (by positivity)
  -- the integer half-width `M = ⌊η/16⌋ + 1 ≥ η/16`
  set M : ℤ := ⌊η / 16⌋ + 1 with hMdef
  have hMge : η / 16 ≤ (M : ℝ) := by
    rw [hMdef]; have h := Int.lt_floor_add_one (η / 16); push_cast; linarith
  have hMle : (M : ℝ) ≤ η / 16 + 1 := by
    rw [hMdef]; have h := Int.floor_le (η / 16); push_cast; linarith
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := by linarith [hMge, hη]
  have hM0 : (0 : ℤ) ≤ M := by exact_mod_cast hMnn
  -- the key numeric inequality `M² + c² ≤ (η/8)²`
  have hkey : (M : ℝ) ^ 2 + c ^ 2 ≤ (η / 8) ^ 2 := by
    have h1 : (M : ℝ) ^ 2 ≤ (η / 16 + 1) ^ 2 := by nlinarith [hMle, hMnn]
    have h2 : (η / 16 + 1) ^ 2 + 1 / 64 ≤ (η / 8) ^ 2 := by nlinarith [hη]
    linarith
  refine ⟨Finset.Icc (-M) (M - 1), ?_, ?_⟩
  · -- the cardinality is `2M ≥ η/8`
    have hcardZ : ((Finset.Icc (-M) (M - 1)).card : ℤ) = 2 * M := by
      have h := Int.card_Icc_of_le (-M) (M - 1) (by omega)
      calc (Finset.Icc (-M) (M - 1)).card = (M - 1) + 1 - (-M) := h
        _ = 2 * M := by ring
    have hcard : ((Finset.Icc (-M) (M - 1)).card : ℝ) = 2 * (M : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hcardZ
      push_cast at this
      exact this
    rw [hcard]; linarith [hMge]
  · -- each box sits in the disc
    intro n hn z hz
    obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hn
    obtain ⟨hre1, hre2, him1, him2⟩ := hz
    rw [Work.Repel.Dflat, Metric.mem_closedBall, dist_eq_norm,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ η)]
    -- real part: `|Re z| < M`
    have hreb : |z.re| < (M : ℝ) := by
      by_cases hn0 : (0 : ℤ) ≤ n
      · have hlt : z.re < (M : ℝ) := by
          have h2 : (n : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast (show n + 1 ≤ M by omega)
          linarith
        rw [abs_of_nonneg (show (0 : ℝ) ≤ z.re by
          have hn0r : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
          linarith)]
        exact hlt
      · have hle0 : z.re ≤ 0 := by
          have h2 : (n : ℝ) + 1 ≤ (0 : ℝ) := by
            have hn1 : n + 1 ≤ 0 := by omega
            exact_mod_cast hn1
          linarith
        have hlt : -(z.re) < (M : ℝ) := by
          have h2 : -(n : ℝ) ≤ (M : ℝ) := by
            have : (-n : ℤ) ≤ M := by omega
            exact_mod_cast this
          linarith
        rw [abs_of_nonpos hle0]; exact hlt
    have hre : z.re ^ 2 < (M : ℝ) ^ 2 := by
      have h := pow_lt_pow_left₀ hreb (abs_nonneg z.re) (by norm_num : (2 : ℕ) ≠ 0)
      rwa [sq_abs] at h
    -- imaginary part: `|Im z - η| < c`
    have himb : |z.im - η| < c := by
      rw [abs_lt]
      refine ⟨?_, ?_⟩
      · rw [hloghalf] at him1; linarith
      · linarith [him2, hlog32]
    have him : (z.im - η) ^ 2 < c ^ 2 := by
      have h := pow_lt_pow_left₀ himb (abs_nonneg (z.im - η)) (by norm_num : (2 : ℕ) ≠ 0)
      rwa [sq_abs] at h
    -- assemble
    have hnorm : ‖z - Complex.I * η‖ ^ 2 = z.re ^ 2 + (z.im - η) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [Complex.sub_re, Complex.sub_im]
      ring
    have hgoal : ‖z - Complex.I * η‖ ^ 2 < (η / 8) ^ 2 := by
      rw [hnorm]; linarith [hre, him, hkey]
    have hlt : ‖z - Complex.I * η‖ < η / 8 := by
      have hh := sq_lt_sq.mp hgoal
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by linarith : (0 : ℝ) ≤ η / 8)] at hh
      exact hh
    exact le_of_lt hlt

end Work.Repel
