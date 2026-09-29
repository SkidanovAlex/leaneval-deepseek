import Mathlib
import Submission.Work.Basic.UniNonres.Defs

/-!
# The final arithmetic estimate `arith`

This is the final numerical estimate in the AJ §9 non-resonant uniformity argument.  Writing
`S = s`, `Λ = L`, `Q = qn` for the real casts, and `K = s - 2`, `M = 2s-1`, the claim compares the
separation/Stirling bound `sepB c δ M + sepB δ δ M` with the uniform error term

`(2 S Λ - 1) * (2 log (Q/S)/Λ + 200 log Λ/Λ + 2 log (1/c)/(S Λ) + 200/Λ)`.

The proof unfolds `sepB`, uses

* `log (1/(2 min c δ)) ≤ log (1/(2c)) + max 0 (log (1/(2δ)))`,
* `log (1/(2δ)) ≤ log (16 qn)` (from `δ ≥ 1/(32 qn)`), hence
  `(4S-4) log (1/(2δ)) + 2 max 0 (log (1/(2δ))) ≤ (4S-2) log (16 qn)`,
* the weak Stirling bound `log (k!) ≥ k log k - k`,

to dominate the left-hand side by the purely logarithmic expression `finCmp`, which is then
compared with the right-hand side using `rhsBound`.
-/

namespace Work.TMC16Core.NrFinal

open Work.Basic.UniNonres

/-- `sepB` in the degenerate case `M ≤ 1` (at most one point, crude bound). -/
theorem sepB_le_one {c δ : ℝ} {M : ℕ} (h : M ≤ 1) :
    sepB c δ M = (M : ℝ) * Real.log (1 / (2 * c)) := by
  rw [Work.Basic.UniNonres.sepB]; simp [h]

/-- `sepB` in the genuine case `2 ≤ M` (separation + Stirling). -/
theorem sepB_of_two_le {c δ : ℝ} {M : ℕ} (h : 2 ≤ M) :
    sepB c δ M = 2 * Real.log (1 / (2 * min c δ)) + ((M : ℝ) - 2) * Real.log (1 / (2 * δ))
      - 2 * Real.log ((((M - 2) / 2).factorial : ℕ) : ℝ) := by
  rw [Work.Basic.UniNonres.sepB]; simp only [if_neg (by omega : ¬ M ≤ 1)]

/-- The sum of the two `sepB` terms occurring in `arith`, for `M = 2s-1`, `s ≥ 2`. -/
theorem sepB_sum_pair {s : ℕ} (hs : 2 ≤ s) {c δ : ℝ} :
    sepB c δ (2 * s - 1) + sepB δ δ (2 * s - 1)
      = 2 * Real.log (1 / (2 * min c δ)) + (4 * (s : ℝ) - 4) * Real.log (1 / (2 * δ))
        - 4 * Real.log (((s - 2).factorial : ℕ) : ℝ) := by
  have h2 : 2 ≤ 2 * s - 1 := by omega
  rw [sepB_of_two_le (c := c) (δ := δ) h2, sepB_of_two_le (c := δ) (δ := δ) h2, min_self]
  have hK : (2 * s - 1 - 2) / 2 = s - 2 := by omega
  have hcast : ((2 * s - 1 : ℕ) : ℝ) - 2 = 2 * (s : ℝ) - 3 := by
    have h1 : (1 : ℕ) ≤ 2 * s := by omega
    push_cast [Nat.cast_sub h1]; ring
  rw [hK, hcast]
  ring

/-- The weak Stirling lower bound `log (k !) ≥ k log k - k`, with Lean's convention `log 0 = 0`
covering `k = 0`. -/
theorem log_factorial_lower (k : ℕ) :
    (k : ℝ) * Real.log (k : ℝ) - (k : ℝ) ≤ Real.log (((k.factorial : ℕ) : ℝ)) := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp
  · have hne : k ≠ 0 := Nat.pos_iff_ne_zero.mp h
    have hst := Stirling.le_log_factorial_stirling hne
    have h1 : 0 ≤ Real.log (k : ℝ) / 2 :=
      div_nonneg (Real.log_nonneg (by exact_mod_cast h)) (by norm_num)
    have h2 : 0 ≤ Real.log (2 * Real.pi) / 2 := by
      apply div_nonneg
      · apply Real.log_nonneg
        nlinarith [Real.pi_gt_three]
      · norm_num
    linarith

/-- `log (1/(2 min c δ)) ≤ log (1/(2c)) + max 0 (log (1/(2δ)))` for `0 < c ≤ 1/2`, `δ > 0`. -/
theorem log_min_le {c δ : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) (hδ : 0 < δ) :
    Real.log (1 / (2 * min c δ)) ≤ Real.log (1 / (2 * c)) + max 0 (Real.log (1 / (2 * δ))) := by
  have hA : 0 ≤ Real.log (1 / (2 * c)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * c)]
    linarith
  by_cases h : c ≤ δ
  · rw [min_eq_left h]
    exact le_add_of_nonneg_right (le_max_left 0 _)
  · rw [min_eq_right (le_of_lt (not_le.mp h))]
    by_cases hB : 0 ≤ Real.log (1 / (2 * δ))
    · rw [max_eq_right hB]
      exact le_add_of_nonneg_left hA
    · rw [max_eq_left (le_of_lt (not_le.mp hB)), add_zero]
      linarith

/-- `log (1/(2δ)) ≤ log (16 qn)` when `δ ≥ 1/(32 qn)`. -/
theorem log_inv_two_le {qn : ℕ} {δ : ℝ} (hqn : 0 < qn) (hδ : 1 / (32 * (qn : ℝ)) ≤ δ) :
    Real.log (1 / (2 * δ)) ≤ Real.log (16 * (qn : ℝ)) := by
  have hQ : (0 : ℝ) < (qn : ℝ) := by exact_mod_cast hqn
  have hδpos : 0 < δ := lt_of_lt_of_le (by positivity) hδ
  apply Real.log_le_log (by positivity)
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * δ)]
  have h32 : 32 * (qn : ℝ) * (1 / (32 * (qn : ℝ))) ≤ 32 * (qn : ℝ) * δ :=
    mul_le_mul_of_nonneg_left hδ (by positivity)
  have h32' : 32 * (qn : ℝ) * (1 / (32 * (qn : ℝ))) = 1 := by
    rw [mul_one_div, div_self (by positivity : (32 * (qn : ℝ)) ≠ 0)]
  nlinarith [h32, h32']

/-- The right-hand side of `arith` dominates the expanded expression; the `c`-terms cancel and the
gain is `2 (1 - 1/L) log (qn/s) + 200 (1 - 1/L) (log L + 1)`. -/
theorem rhsBound {s L qn : ℕ} {c : ℝ} (hs : 1 ≤ s) (hL : 1 ≤ L) (hQ : 2 * s * L ≤ qn)
    (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    (4 * (s : ℝ) - 2) * Real.log ((qn : ℝ) / (s : ℝ))
      + (400 * (s : ℝ) - 200) * Real.log (L : ℝ)
      + (4 - 2 / ((s : ℝ) * (L : ℝ))) * Real.log (1 / c)
      + 400 * (s : ℝ) - 200
    ≤ (2 * (s : ℝ) * (L : ℝ) - 1) *
        (2 * Real.log ((qn : ℝ) / (s : ℝ)) / (L : ℝ)
          + 200 * Real.log (L : ℝ) / (L : ℝ)
          + 2 * Real.log (1 / c) / ((s : ℝ) * (L : ℝ))
          + 200 / (L : ℝ)) := by
  have hSR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hLR1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hP : 0 ≤ Real.log ((qn : ℝ) / (s : ℝ)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hSR]
    have hsle : s ≤ qn := by
      have h1 : s ≤ 2 * s * L := by
        calc s = s * 1 := (mul_one s).symm
          _ ≤ s * (2 * L) := Nat.mul_le_mul_left s (by omega)
          _ = 2 * s * L := by ring
      exact le_trans h1 hQ
    have : (s : ℝ) ≤ (qn : ℝ) := by exact_mod_cast hsle
    linarith
  have hLlog : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg hLR1
  have h1 : 0 ≤ 2 * (1 - 1 / (L : ℝ)) * Real.log ((qn : ℝ) / (s : ℝ)) := by
    apply mul_nonneg
    · apply mul_nonneg (by norm_num)
      rw [sub_nonneg, div_le_iff₀ hLR]
      linarith
    · exact hP
  have h2 : 0 ≤ 200 * (1 - 1 / (L : ℝ)) * (Real.log (L : ℝ) + 1) := by
    apply mul_nonneg
    · apply mul_nonneg (by norm_num)
      rw [sub_nonneg, div_le_iff₀ hLR]
      linarith
    · linarith
  have key : (2 * (s : ℝ) * (L : ℝ) - 1) *
        (2 * Real.log ((qn : ℝ) / (s : ℝ)) / (L : ℝ)
          + 200 * Real.log (L : ℝ) / (L : ℝ)
          + 2 * Real.log (1 / c) / ((s : ℝ) * (L : ℝ))
          + 200 / (L : ℝ))
      - ((4 * (s : ℝ) - 2) * Real.log ((qn : ℝ) / (s : ℝ))
        + (400 * (s : ℝ) - 200) * Real.log (L : ℝ)
        + (4 - 2 / ((s : ℝ) * (L : ℝ))) * Real.log (1 / c)
        + 400 * (s : ℝ) - 200)
      = 2 * (1 - 1 / (L : ℝ)) * Real.log ((qn : ℝ) / (s : ℝ))
        + 200 * (1 - 1 / (L : ℝ)) * (Real.log (L : ℝ) + 1) := by
    first | (field_simp; ring) | field_simp
  linarith [h1, h2, key]

/-- The final comparison, `s ≥ 2`. -/
theorem finCmp {s L qn : ℕ} {c : ℝ} (hs : 2 ≤ s) (hL : 1 ≤ L) (hQ : 2 * s * L ≤ qn)
    (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    256 * (s : ℝ) * Real.log (L : ℝ) + 3 * Real.log (1 / (2 * c))
      + (4 * (s : ℝ) - 2) * Real.log (16 * (qn : ℝ))
      - 4 * ((s - 2 : ℕ) : ℝ) * Real.log ((s - 2 : ℕ) : ℝ) + 4 * ((s - 2 : ℕ) : ℝ)
    < (2 * (s : ℝ) * (L : ℝ) - 1) *
        (2 * Real.log ((qn : ℝ) / (s : ℝ)) / (L : ℝ)
          + 200 * Real.log (L : ℝ) / (L : ℝ)
          + 2 * Real.log (1 / c) / ((s : ℝ) * (L : ℝ))
          + 200 / (L : ℝ)) := by
  have hsR : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hSR : (0 : ℝ) < (s : ℝ) := by linarith
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hQR : (0 : ℝ) < (qn : ℝ) := by
    have h2sL : 0 < 2 * s * L := by
      have hs0 : 0 < s := by omega
      have hL0 : 0 < L := by omega
      positivity
    have : 0 < qn := by omega
    exact_mod_cast this
  have hP0 : 0 ≤ Real.log ((qn : ℝ) / (s : ℝ)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hSR]
    have hsle : s ≤ qn := by
      have h1 : s ≤ 2 * s * L := by
        calc s = s * 1 := (mul_one s).symm
          _ ≤ s * (2 * L) := Nat.mul_le_mul_left s (by omega)
          _ = 2 * s * L := by ring
      exact le_trans h1 hQ
    have : (s : ℝ) ≤ (qn : ℝ) := by exact_mod_cast hsle
    linarith
  have hLlog : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg hLR
  have hClog : 0 ≤ Real.log (1 / c) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hc]; linarith
  have hlog1 : Real.log (1 / (2 * c)) = Real.log (1 / c) - Real.log 2 := by
    have hsplit : (1 : ℝ) / (2 * c) = (1 / c) * (1 / 2) := by
      first | (field_simp; ring) | field_simp
    rw [hsplit, Real.log_mul (by positivity) (by norm_num)]
    have hhalf : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
    rw [hhalf]; ring
  have hlog16 : Real.log (16 * (qn : ℝ))
      = Real.log ((qn : ℝ) / (s : ℝ)) + Real.log (s : ℝ) + 4 * Real.log 2 := by
    have hlogQ : Real.log (qn : ℝ) = Real.log ((qn : ℝ) / (s : ℝ)) + Real.log (s : ℝ) := by
      rw [← Real.log_mul (by positivity : ((qn : ℝ) / (s : ℝ)) ≠ 0) (by positivity : (s : ℝ) ≠ 0)]
      congr 1
      field_simp
    rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (ne_of_gt hQR), hlogQ]
    have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; ring
    rw [h16]; ring
  rw [hlog1, hlog16]
  have hKcast : ((s - 2 : ℕ) : ℝ) = (s : ℝ) - 2 := by
    rw [Nat.cast_sub hs]; norm_num
  have b1 : 0 ≤ (144 * (s : ℝ) - 200) * Real.log (L : ℝ) :=
    mul_nonneg (by nlinarith [hsR]) hLlog
  have b2 : 0 ≤ (1 - 2 / ((s : ℝ) * (L : ℝ))) * Real.log (1 / c) := by
    apply mul_nonneg _ hClog
    rw [sub_nonneg, div_le_iff₀ (by positivity : (0 : ℝ) < (s : ℝ) * (L : ℝ))]
    nlinarith [hsR, hLR]
  have b3 : -8 - 6 * Real.log (s : ℝ)
      ≤ 4 * ((s - 2 : ℕ) : ℝ) * Real.log ((s - 2 : ℕ) : ℝ)
        - (4 * (s : ℝ) - 2) * Real.log (s : ℝ) := by
    rcases eq_or_lt_of_le hsR with h2 | h2
    · have hs2 : s = 2 := by exact_mod_cast h2.symm
      subst hs2
      have h0 : ((2 - 2 : ℕ) : ℝ) = 0 := by norm_num
      rw [h0, Real.log_zero]
      push_cast
      linarith
    · have hKpos : 0 < (s : ℝ) - 2 := by linarith
      have hSpos : 0 < (s : ℝ) := hSR
      have hKne : (s : ℝ) - 2 ≠ 0 := ne_of_gt hKpos
      have hratio : (s : ℝ) / ((s : ℝ) - 2) = 1 + 2 / ((s : ℝ) - 2) := by
        first | (field_simp; ring) | field_simp
      have hdiv : Real.log ((s : ℝ) / ((s : ℝ) - 2)) = Real.log (s : ℝ) - Real.log ((s : ℝ) - 2) :=
        Real.log_div (ne_of_gt hSpos) hKne
      have hx : 0 < 1 + 2 / ((s : ℝ) - 2) := by
        have : 0 < 2 / ((s : ℝ) - 2) := div_pos (by norm_num) hKpos
        linarith
      have hle : Real.log ((s : ℝ) / ((s : ℝ) - 2)) ≤ 2 / ((s : ℝ) - 2) := by
        rw [hratio]
        have h := Real.log_le_sub_one_of_pos hx
        linarith
      have hkey : 4 * ((s : ℝ) - 2) * (Real.log (s : ℝ) - Real.log ((s : ℝ) - 2)) ≤ 8 := by
        have h4 : (0 : ℝ) ≤ 4 * ((s : ℝ) - 2) := by linarith
        have h1 := mul_le_mul_of_nonneg_left hle h4
        have h8 : 4 * ((s : ℝ) - 2) * (2 / ((s : ℝ) - 2)) = 8 := by
          first | (field_simp; ring) | field_simp
        rw [hdiv, h8] at h1
        exact h1
      rw [hKcast]
      nlinarith [hkey]
  have b4 : 11 - 16 * (s : ℝ) ≤ (11 - 16 * (s : ℝ)) * Real.log 2 := by
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have hneg : 11 - 16 * (s : ℝ) ≤ 0 := by nlinarith [hsR]
    nlinarith [hlog2, hneg]
  have b5 : 6 * Real.log (s : ℝ) ≤ 6 * (s : ℝ) - 6 := by
    have := Real.log_le_sub_one_of_pos hSR
    linarith
  have hY := rhsBound (s := s) (L := L) (qn := qn) (c := c) (by omega) hL hQ hc hc2
  have hid : (4 * (s : ℝ) - 2) * Real.log ((qn : ℝ) / (s : ℝ))
        + (400 * (s : ℝ) - 200) * Real.log (L : ℝ)
        + (4 - 2 / ((s : ℝ) * (L : ℝ))) * Real.log (1 / c) + 400 * (s : ℝ) - 200
      - (256 * (s : ℝ) * Real.log (L : ℝ) + 3 * (Real.log (1 / c) - Real.log 2)
        + (4 * (s : ℝ) - 2) * (Real.log ((qn : ℝ) / (s : ℝ)) + Real.log (s : ℝ) + 4 * Real.log 2)
        - 4 * ((s - 2 : ℕ) : ℝ) * Real.log ((s - 2 : ℕ) : ℝ) + 4 * ((s - 2 : ℕ) : ℝ))
      = (144 * (s : ℝ) - 200) * Real.log (L : ℝ)
        + (1 - 2 / ((s : ℝ) * (L : ℝ))) * Real.log (1 / c)
        + (11 - 16 * (s : ℝ)) * Real.log 2
        + (4 * ((s - 2 : ℕ) : ℝ) * Real.log ((s - 2 : ℕ) : ℝ) - (4 * (s : ℝ) - 2) * Real.log (s : ℝ))
        - 4 * ((s - 2 : ℕ) : ℝ) + 400 * (s : ℝ) - 200 := by
    rw [hKcast]; ring
  have hpos : 0 < (144 * (s : ℝ) - 200) * Real.log (L : ℝ)
        + (1 - 2 / ((s : ℝ) * (L : ℝ))) * Real.log (1 / c)
        + (11 - 16 * (s : ℝ)) * Real.log 2
        + (4 * ((s - 2 : ℕ) : ℝ) * Real.log ((s - 2 : ℕ) : ℝ) - (4 * (s : ℝ) - 2) * Real.log (s : ℝ))
        - 4 * ((s - 2 : ℕ) : ℝ) + 400 * (s : ℝ) - 200 := by
    nlinarith [b1, b2, b3, b4, b5, hKcast, hsR]
  linarith [hY, hid, hpos]

/-- The case `s = 1`. -/
theorem arith_one {L qn : ℕ} {c δ : ℝ} (hL : 1 ≤ L) (hQ : 2 * L ≤ qn)
    (hc : 0 < c) (hc2 : c ≤ 1 / 2) (hδ : 1 / (32 * (qn : ℝ)) ≤ δ) :
    256 * Real.log (L : ℝ) - Real.log (2 * c) + Real.log (1 / (2 * c)) + Real.log (1 / (2 * δ))
      < (2 * (L : ℝ) - 1) *
          (2 * Real.log (qn : ℝ) / (L : ℝ)
            + 200 * Real.log (L : ℝ) / (L : ℝ)
            + 2 * Real.log (1 / c) / (L : ℝ)
            + 200 / (L : ℝ)) := by
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hLR1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hqnpos : 0 < qn := by omega
  have hQnpos : (0 : ℝ) < (qn : ℝ) := by exact_mod_cast hqnpos
  have hqn2 : (2 : ℝ) ≤ (qn : ℝ) := by
    have h2 : 2 ≤ qn := by omega
    exact_mod_cast h2
  have hδ16 := log_inv_two_le (qn := qn) (δ := δ) hqnpos hδ
  have hA1 : Real.log (1 / (2 * c)) ≤ Real.log (1 / c) := by
    apply Real.log_le_log (by positivity)
    exact one_div_le_one_div_of_le hc (by linarith : c ≤ 2 * c)
  have hA2 : -Real.log (2 * c) = Real.log (1 / (2 * c)) := by rw [one_div, Real.log_inv]
  have hlq2 : Real.log 2 ≤ Real.log (qn : ℝ) := Real.log_le_log (by norm_num) hqn2
  have hlq0 : 0 ≤ Real.log (qn : ℝ) := Real.log_nonneg (by linarith)
  have hlogL0 : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg hLR1
  have hClog0 : 0 ≤ Real.log (1 / c) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hc]; linarith
  have hlog2le1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hlog16qn : Real.log (16 * (qn : ℝ)) = 4 * Real.log 2 + Real.log (qn : ℝ) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hQnpos)]
    have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; ring
    rw [h16]
  have hLHSbound : 256 * Real.log (L : ℝ) - Real.log (2 * c) + Real.log (1 / (2 * c))
        + Real.log (1 / (2 * δ))
      ≤ 256 * Real.log (L : ℝ) + 2 * Real.log (1 / c) + (4 * Real.log 2 + Real.log (qn : ℝ)) := by
    rw [← hlog16qn]
    linarith [hA2, hδ16, hA1]
  have hgoalml : (L : ℝ) * (256 * Real.log (L : ℝ) + 2 * Real.log (1 / c)
        + (4 * Real.log 2 + Real.log (qn : ℝ)))
      < (2 * (L : ℝ) - 1) * (2 * Real.log (qn : ℝ) + 200 * Real.log (L : ℝ)
        + 2 * Real.log (1 / c) + 200) := by
    have e1 : Real.log 2 ≤ (3 * (L : ℝ) - 2) * Real.log (qn : ℝ) := by
      have h3 : (1 : ℝ) ≤ 3 * (L : ℝ) - 2 := by linarith
      nlinarith [hlq2, h3, hlq0]
    have e2 : 0 ≤ (144 * (L : ℝ) - 200) * Real.log (L : ℝ) := by
      rcases eq_or_lt_of_le hL with hL1 | hL2
      · subst hL1; simp
      · apply mul_nonneg _ hlogL0
        have h2 : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL2
        nlinarith
    have e3 : 0 ≤ (2 * (L : ℝ) - 2) * Real.log (1 / c) := by
      apply mul_nonneg _ hClog0; linarith
    have e4 : 0 < 400 * (L : ℝ) - 200 - 4 * (L : ℝ) * Real.log 2 := by
      nlinarith [hLR1, hlog2le1]
    nlinarith [e1, e2, e3, e4, hLR]
  have hB : (2 * Real.log (qn : ℝ) / (L : ℝ) + 200 * Real.log (L : ℝ) / (L : ℝ)
        + 2 * Real.log (1 / c) / (L : ℝ) + 200 / (L : ℝ))
      = (2 * Real.log (qn : ℝ) + 200 * Real.log (L : ℝ) + 2 * Real.log (1 / c) + 200) / (L : ℝ) := by
    first | (field_simp; ring) | field_simp
  rw [hB, ← mul_div_assoc, lt_div_iff₀ hLR]
  have hmul := mul_le_mul_of_nonneg_left hLHSbound (le_of_lt hLR)
  linarith [hmul, hgoalml]

/-- **The requested arithmetic estimate.** -/
theorem arith {s L qn : ℕ} {c δ : ℝ} (hs : 1 ≤ s) (hL : 1 ≤ L) (hQ : 2 * s * L ≤ qn)
    (hc : 0 < c) (hc2 : c ≤ 1 / 2) (hδ : 1 / (32 * (qn : ℝ)) ≤ δ) :
    256 * (s : ℝ) * Real.log (L : ℝ) - Real.log (2 * c)
      + Work.Basic.UniNonres.sepB c δ (2 * s - 1) + Work.Basic.UniNonres.sepB δ δ (2 * s - 1)
    < (2 * (s : ℝ) * (L : ℝ) - 1) *
        (2 * Real.log ((qn : ℝ) / (s : ℝ)) / (L : ℝ)
          + 200 * Real.log (L : ℝ) / (L : ℝ)
          + 2 * Real.log (1 / c) / ((s : ℝ) * (L : ℝ))
          + 200 / (L : ℝ)) := by
  have hqnpos : 0 < qn := by
    have h2sL : 0 < 2 * s * L := by
      have hs0 : 0 < s := by omega
      have hL0 : 0 < L := by omega
      positivity
    omega
  have hδpos : 0 < δ := by
    apply lt_of_lt_of_le _ hδ
    have : (0 : ℝ) < (qn : ℝ) := by exact_mod_cast hqnpos
    positivity
  rcases eq_or_lt_of_le hs with h1 | hs2
  · subst h1
    have hM1 : (2 * 1 - 1 : ℕ) = 1 := by norm_num
    rw [hM1, sepB_le_one (c := c) (δ := δ) (M := 1) le_rfl,
      sepB_le_one (c := δ) (δ := δ) (M := 1) le_rfl]
    push_cast
    simp only [one_mul, mul_one, div_one]
    exact arith_one hL (by simpa using hQ) hc hc2 hδ
  · have hs2' : 2 ≤ s := by omega
    have hAeq : -Real.log (2 * c) = Real.log (1 / (2 * c)) := by rw [one_div, Real.log_inv]
    rw [show 256 * (s : ℝ) * Real.log (L : ℝ) - Real.log (2 * c)
          + Work.Basic.UniNonres.sepB c δ (2 * s - 1) + Work.Basic.UniNonres.sepB δ δ (2 * s - 1)
        = 256 * (s : ℝ) * Real.log (L : ℝ) - Real.log (2 * c)
          + (Work.Basic.UniNonres.sepB c δ (2 * s - 1) + Work.Basic.UniNonres.sepB δ δ (2 * s - 1))
        by ring,
      sepB_sum_pair (s := s) (c := c) (δ := δ) hs2']
    have hsR : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs2'
    have hP1 : (0 : ℝ) ≤ 4 * (s : ℝ) - 2 := by linarith
    have hδ16 := log_inv_two_le (qn := qn) (δ := δ) hqnpos hδ
    have hmin := log_min_le (c := c) (δ := δ) hc hc2 hδpos
    have h16nonneg : 0 ≤ Real.log (16 * (qn : ℝ)) := by
      apply Real.log_nonneg
      have h1' : (1 : ℝ) ≤ 16 * (qn : ℝ) := by
        have h1n : (1 : ℕ) ≤ qn := by omega
        have : (1 : ℝ) ≤ (qn : ℝ) := by exact_mod_cast h1n
        linarith
      linarith
    have hstep2 : 2 * max 0 (Real.log (1 / (2 * δ))) + (4 * (s : ℝ) - 4) * Real.log (1 / (2 * δ))
        ≤ (4 * (s : ℝ) - 2) * Real.log (16 * (qn : ℝ)) := by
      by_cases hB : 0 ≤ Real.log (1 / (2 * δ))
      · rw [max_eq_right hB]
        have := mul_le_mul_of_nonneg_left hδ16 hP1
        nlinarith [this]
      · rw [max_eq_left (le_of_lt (not_le.mp hB))]
        have h1' : (4 * (s : ℝ) - 4) * Real.log (1 / (2 * δ)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_lt (not_le.mp hB))
        nlinarith [h1', h16nonneg, hP1]
    have hstep3 : -4 * Real.log (((s - 2).factorial : ℕ) : ℝ)
        ≤ -4 * ((s - 2 : ℕ) : ℝ) * Real.log ((s - 2 : ℕ) : ℝ) + 4 * ((s - 2 : ℕ) : ℝ) := by
      have := log_factorial_lower (s - 2)
      nlinarith [this]
    have hbound : 256 * (s : ℝ) * Real.log (L : ℝ) - Real.log (2 * c)
          + (2 * Real.log (1 / (2 * min c δ)) + (4 * (s : ℝ) - 4) * Real.log (1 / (2 * δ))
            - 4 * Real.log (((s - 2).factorial : ℕ) : ℝ))
        ≤ 256 * (s : ℝ) * Real.log (L : ℝ) + 3 * Real.log (1 / (2 * c))
          + (4 * (s : ℝ) - 2) * Real.log (16 * (qn : ℝ))
          - 4 * ((s - 2 : ℕ) : ℝ) * Real.log ((s - 2 : ℕ) : ℝ) + 4 * ((s - 2 : ℕ) : ℝ) := by
      nlinarith [hmin, hstep2, hstep3, hAeq]
    have hfin := finCmp (s := s) (L := L) (qn := qn) (c := c) hs2' hL hQ hc hc2
    linarith [hbound, hfin]

end Work.TMC16Core.NrFinal
