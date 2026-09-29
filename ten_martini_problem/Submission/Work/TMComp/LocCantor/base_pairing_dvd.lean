import Mathlib
import Submission.Work.TMComp.C7Aux.basePairing
import Submission.Work.TMComp.LocCantor.dyadic_level_pairing

namespace Work.TMComp.LocCantor

open Work.TMC7Core

/-- **The base scale of the [BJ] tower, in multiples of `q`.**

If the true exponent at `E` is large (`100κ < lyap`), then for every `q ≥ 1` there is a scale
`N₀ ≥ Cκ⁻²q`, divisible by `q`, carrying the level `100κ < L_{N₀}` and the pairing
`(9/10)·L_{N₀} < L_{2N₀}`.

This is `C7Aux.exists_base_pairing` with the dyadic chain `t, 2t, 4t, …` started at a multiple
`t` of `q` (so that every scale of the chain, in particular the good one, is a multiple of `q`),
the divisibility being what the rational-approximant bookkeeping of the tower needs. -/
theorem base_pairing_dvd {lam : ℝ} {K : Set ℝ} {C₀ C κ : ℝ}
    (hC₀ : Work.TMC7Core.HasLEBound lam K C₀) (hκ : 0 < κ)
    {α : ℝ} {q : ℕ} (hq : 1 ≤ q) (hqC : C * (κ ^ 2)⁻¹ ≤ (q : ℝ))
    {E : ℝ} (hE : E ∈ K) (hL : 100 * κ < Work.TMC7Core.lyap α lam (E : ℂ)) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ q ∣ N₀ ∧
      C * (κ ^ 2)⁻¹ * (q : ℝ) ≤ (N₀ : ℝ) ∧
      100 * κ < Work.TMC7Core.lyapAvg α lam (E : ℂ) N₀ ∧
      (9 / 10) * Work.TMC7Core.lyapAvg α lam (E : ℂ) N₀
        < Work.TMC7Core.lyapAvg α lam (E : ℂ) (2 * N₀) := by
  classical
  have hqge1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  set t : ℕ := q * max 1 (Nat.ceil (C * (κ ^ 2)⁻¹)) with ht
  have ht1 : 1 ≤ t := by
    rw [ht]
    have h1 : (1 : ℕ) ≤ max 1 (Nat.ceil (C * (κ ^ 2)⁻¹)) := le_max_left _ _
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ q * max 1 (Nat.ceil (C * (κ ^ 2)⁻¹)) := Nat.mul_le_mul hq h1
  have htq : q ∣ t := by
    rw [ht]; exact dvd_mul_right q _
  have htC : C * (κ ^ 2)⁻¹ * (q : ℝ) ≤ (t : ℝ) := by
    have hceil : C * (κ ^ 2)⁻¹ ≤ ((max 1 (Nat.ceil (C * (κ ^ 2)⁻¹))) : ℝ) := by
      have h1 : C * (κ ^ 2)⁻¹ ≤ (Nat.ceil (C * (κ ^ 2)⁻¹) : ℝ) := Nat.le_ceil _
      have h2 : (Nat.ceil (C * (κ ^ 2)⁻¹) : ℝ)
          ≤ ((max 1 (Nat.ceil (C * (κ ^ 2)⁻¹))) : ℝ) := by
        exact_mod_cast le_max_right _ _
      linarith
    have hcast : (t : ℝ) = (q : ℝ) * ((max 1 (Nat.ceil (C * (κ ^ 2)⁻¹))) : ℝ) := by
      rw [ht]; push_cast; ring
    rw [hcast]
    nlinarith [hceil, hqpos]
  set J : ℕ := Nat.ceil (Real.log (C₀ / (100 * κ)) / Real.log (10 / 9)) + 1 with hJ
  have hJcond : Real.log (C₀ / (100 * κ)) / Real.log (10 / 9) < (J : ℝ) := by
    rw [hJ]; push_cast
    linarith [Nat.le_ceil (Real.log (C₀ / (100 * κ)) / Real.log (10 / 9))]
  have ht1' : 1 ≤ t * 2 ^ J :=
    le_trans ht1 (Nat.le_mul_of_pos_right t (pow_pos (by norm_num) J))
  have htop : 100 * κ < lyapAvg α lam (E : ℂ) (t * 2 ^ J) :=
    lt_of_lt_of_le hL (Work.TMC7Core.Scale.lyap_le_lyapAvg α lam (E : ℂ) ht1')
  obtain ⟨j, hjJ, hp⟩ := dyadic_level_pairing (fun n => lyapAvg α lam (E : ℂ) n) t J C₀ κ
    hκ ht1 (fun m _ => Work.TMC7Core.Scale.lyapAvg_two_le α lam (E : ℂ) m)
    (fun m => Work.TMComp.C7Aux.lyapAvg_le_of_hasLEBound hC₀ hE α m) htop hJcond
  have hj1 : 1 ≤ t * 2 ^ j :=
    le_trans ht1 (Nat.le_mul_of_pos_right t (pow_pos (by norm_num) j))
  refine ⟨t * 2 ^ j, hj1, ?_, ?_, ?_, ?_⟩
  · exact dvd_trans htq (dvd_mul_right t (2 ^ j))
  · calc C * (κ ^ 2)⁻¹ * (q : ℝ) ≤ (t : ℝ) := htC
      _ ≤ ((t * 2 ^ j : ℕ) : ℝ) := by
          have h : t ≤ t * 2 ^ j := Nat.le_mul_of_pos_right t (pow_pos (by norm_num) j)
          exact_mod_cast h
  · exact lt_of_lt_of_le hL (Work.TMC7Core.Scale.lyap_le_lyapAvg α lam (E : ℂ) hj1)
  · have h2N : 2 * (t * 2 ^ j) = t * 2 ^ (j + 1) := by rw [pow_succ]; ring
    rw [h2N]
    exact hp

end Work.TMComp.LocCantor
