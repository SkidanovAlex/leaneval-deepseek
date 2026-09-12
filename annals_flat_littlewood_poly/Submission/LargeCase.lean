import Mathlib
import ChallengeDeps
import Submission.S6_Flat
import Submission.QCover
import Submission.FinalTrunc

/-! Large-degree reduction: from `Submission.Flat.flat_deg4q` (degrees `4q`)
to ALL degrees `n ≥ N0 := 2^402`.

For `n ≥ N0`, set `q := (n + 3) / 4` (so `4q − 3 ≤ n ≤ 4q`; `QCover.ceil_div_four`)
and pick an odd `t` via `QCover.exists_odd_t_tile q`; this gives
`2^43·m_t ≤ q` and `q ≤ 2^(t+60)` (`QCover.tile_consequences`), so
`Flat.flat_deg4q` supplies a degree-`4q` Littlewood polynomial `Q` with
`2^(-170)√q ≤ |Q| ≤ 2^14√q`.  Truncating to degree `n` (removing ≤ 3
monomials) gives a Littlewood polynomial `P` of degree exactly `n` with

    2^(-174)·√n ≤ |P(z)|  and   |P(z)| ≤ 2^15·√n

for every |z| = 1 (use `4q − n ≤ 3`, `√q ≥ √n/2`, `n ≥ N0 = 2^402`;
all numerical inequalities by `nlinarith`/`norm_num` with slack). -/

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

set_option autoImplicit false

open FlatLittlewoodPoly

namespace Submission
namespace Large

/-- Large-degree threshold. -/
def N0 : ℕ := 2 ^ 402

/-- Large degrees: a flat Littlewood polynomial of degree exactly `n`. -/
theorem large_case :
    ∀ n : ℕ, N0 ≤ n →
      ∃ P : ℂ[X], IsLittlewoodPolynomial P ∧ P.natDegree = n ∧
        ∀ z : ℂ, ‖z‖ = 1 →
          ((2 : ℝ) ^ 174)⁻¹ * Real.sqrt (n : ℝ) ≤ ‖P.eval z‖ ∧
          ‖P.eval z‖ ≤ (2 ^ 15 : ℝ) * Real.sqrt (n : ℝ) := by
  intro n hn
  let q : ℕ := (n + 3) / 4
  have hqceil := ceil_div_four n
  have hqlolo : 4 * q - 3 ≤ n := by simpa [q] using hqceil.1
  have hqlo : n ≤ 4 * q := by simpa [q] using hqceil.2
  have hq4mn3 : 4 * q - n ≤ 3 := by omega
  have hq400 : 2 ^ 400 ≤ q := by
    dsimp [q]
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 4)]
    have h402eq : 2 ^ 400 * 4 = 2 ^ 402 := by
      rw [mul_comm, show 4 = 2 ^ 2 by norm_num, ← pow_add]
    rw [h402eq]
    have hnn : 2 ^ 402 ≤ n := by simpa [N0] using hn
    omega
  have hq1 : 1 ≤ q := by
    exact le_trans (Nat.one_le_pow 400 2 (by norm_num)) hq400
  have hq_le_n : q ≤ n := by omega
  have hqbig : 2 ^ 43 * mt 1 ≤ q := by
    have h1 : 2 ^ 43 * mt 1 ≤ 2 ^ 43 * 2 ^ 13 := by
      have hmt : mt 1 ≤ 2 ^ 13 := by
        unfold mt
        norm_num
      exact Nat.mul_le_mul_left _ hmt
    have h2 : 2 ^ 43 * 2 ^ 13 ≤ 2 ^ 400 := by
      rw [← pow_add]
      exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
    exact le_trans (le_trans h1 h2) hq400
  rcases exists_odd_t_tile q hqbig with ⟨t, htodd, htlo, hthi⟩
  have htcons := tile_consequences htodd htlo hthi
  have hlo' : 2 ^ 43 * Sec3.m_t t ≤ q := by
    simpa [Flat.mt_eq_mt] using htcons.1
  have hhi' : q ≤ 2 ^ (t + 60) := htcons.2
  rcases Flat.flat_deg4q t q htodd hq400 hlo' hhi' with ⟨Q, hQlw, hQdeg, hQbd⟩
  let P : ℂ[X] := Trunc.trunc Q n
  have hPtr := Trunc.trunc_littlewood_degree Q (4 * q) n hQlw hQdeg hqlo
  refine ⟨P, hPtr.1, hPtr.2, ?_⟩
  intro z hz
  have hQlo : ((2 : ℝ) ^ 170)⁻¹ * Real.sqrt (q : ℝ) ≤ ‖Q.eval z‖ := (hQbd z hz).1
  have hQup : ‖Q.eval z‖ ≤ (2 ^ 14 : ℝ) * Real.sqrt (q : ℝ) := (hQbd z hz).2
  have htr3 : ‖P.eval z - Q.eval z‖ ≤ 3 := by
    exact Trunc.trunc_sub_le_three Q (4 * q) n hQlw hQdeg hq4mn3 z hz
  have hP_le_Q : ‖P.eval z‖ ≤ ‖Q.eval z‖ + ‖P.eval z - Q.eval z‖ := by
    calc
      ‖P.eval z‖ = ‖Q.eval z + (P.eval z - Q.eval z)‖ := by
        congr 1
        ring
      _ ≤ ‖Q.eval z‖ + ‖P.eval z - Q.eval z‖ := norm_add_le _ _
  have hu_le : ‖P.eval z‖ ≤ (2 ^ 14 : ℝ) * Real.sqrt (q : ℝ) + 3 := by
    linarith [hP_le_Q, hQup, htr3]
  have hQ_le_P : ‖Q.eval z‖ ≤ ‖P.eval z‖ + ‖Q.eval z - P.eval z‖ := by
    calc
      ‖Q.eval z‖ = ‖P.eval z + (Q.eval z - P.eval z)‖ := by
        congr 1
        ring
      _ ≤ ‖P.eval z‖ + ‖Q.eval z - P.eval z‖ := norm_add_le _ _
  have hQP_le : ‖Q.eval z - P.eval z‖ ≤ 3 := by
    rw [norm_sub_rev]
    exact htr3
  have hu_ge : ((2 : ℝ) ^ 170)⁻¹ * Real.sqrt (q : ℝ) - 3 ≤ ‖P.eval z‖ := by
    have h1 : ((2 : ℝ) ^ 170)⁻¹ * Real.sqrt (q : ℝ) ≤ ‖P.eval z‖ + 3 := by
      calc
        ((2 : ℝ) ^ 170)⁻¹ * Real.sqrt (q : ℝ) ≤ ‖Q.eval z‖ := hQlo
        _ ≤ ‖P.eval z‖ + ‖Q.eval z - P.eval z‖ := hQ_le_P
        _ ≤ ‖P.eval z‖ + 3 := by linarith [hQP_le]
    linarith
  -- sqrt facts
  have hq_le_n' : (q : ℝ) ≤ (n : ℝ) := by exact_mod_cast hq_le_n
  have hsq_le_sn : Real.sqrt (q : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hq_le_n'
  have hn_le_hq : (n : ℝ) ≤ 4 * (q : ℝ) := by exact_mod_cast hqlo
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by norm_num)]
  have hsn_le_2sq : Real.sqrt (n : ℝ) ≤ 2 * Real.sqrt (q : ℝ) := by
    have hs := Real.sqrt_le_sqrt hn_le_hq
    have h4q : Real.sqrt ((4 : ℝ) * (q : ℝ)) = 2 * Real.sqrt (q : ℝ) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hsqrt4]
    rwa [h4q] at hs
  have hpow402 : (2 : ℝ) ^ 402 ≤ (n : ℝ) := by
    exact_mod_cast (by simpa [N0] using hn)
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hbig : (2 : ℝ) ^ 201 ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by positivity) hn_nonneg]
    have hsq : ((2 : ℝ) ^ 201) ^ 2 = (2 : ℝ) ^ 402 := by
      rw [← pow_mul]
    rw [hsq]
    exact hpow402
  have h3_le_14s : (3 : ℝ) ≤ (2 ^ 14 : ℝ) * Real.sqrt (n : ℝ) := by
    calc
      (3 : ℝ) ≤ (2 ^ 14 : ℝ) * (2 : ℝ) ^ 201 := by norm_num
      _ ≤ (2 ^ 14 : ℝ) * Real.sqrt (n : ℝ) := by
        exact mul_le_mul_of_nonneg_left hbig (by positivity)
  have h3_le_slack : (3 : ℝ) ≤ (7 : ℝ) * ((2 : ℝ) ^ 174)⁻¹ * Real.sqrt (n : ℝ) := by
    calc
      (3 : ℝ) ≤ (7 : ℝ) * (((2 : ℝ) ^ 174)⁻¹) * (2 : ℝ) ^ 201 := by norm_num
      _ ≤ (7 : ℝ) * (((2 : ℝ) ^ 174)⁻¹) * Real.sqrt (n : ℝ) := by
        have hc : 0 ≤ (7 : ℝ) * (((2 : ℝ) ^ 174)⁻¹) := by positivity
        exact mul_le_mul_of_nonneg_left hbig hc
  constructor
  · have hmain : ((2 : ℝ) ^ 174)⁻¹ * Real.sqrt (n : ℝ) ≤
        ((2 : ℝ) ^ 170)⁻¹ * Real.sqrt (q : ℝ) - 3 := by
      nlinarith only [hsn_le_2sq, h3_le_slack]
    exact le_trans hmain hu_ge
  · have hmain : (2 ^ 14 : ℝ) * Real.sqrt (q : ℝ) + 3 ≤ (2 ^ 15 : ℝ) * Real.sqrt (n : ℝ) := by
      nlinarith only [hsq_le_sn, h3_le_14s]
    exact le_trans hu_le hmain

end Large
end Submission
