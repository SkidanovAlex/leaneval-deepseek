import Mathlib
import Submission.Work.TMComp.LocCantor.base_pairing_dvd
import Submission.Work.TMComp.LocCantor.dyadic_level_pairing
import Submission.Work.TMC7Core.LDT

namespace Work.TMC7Core.Scale

/-- **The base scale of the [BJ] tower, with an explicit upper bound.**

Same construction as `Work.TMComp.LocCantor.base_pairing_dvd`: with `t = q·max 1 ⌈Cκ⁻²⌉`
and `J = ⌈log(C₀/(100κ))/log(10/9)⌉ + 1`, the dyadic pigeonhole
`Work.TMComp.LocCantor.dyadic_level_pairing` produces an index `j < J` such that `N₀ = t·2^j`
carries the level `100κ < L_{N₀}` and the pairing `(9/10)L_{N₀} < L_{2N₀}`.  Because the
pigeonhole index is confined to `[0, J)`, the scale additionally obeys the upper bound
`N₀ ≤ (max 1 ⌈Cκ⁻²⌉ · 2^J)·q = (max 1 ⌈Cκ⁻²⌉ · 2^(⌈log(C₀/(100κ))/log(10/9)⌉+1))·q`,
which the rational-approximant bookkeeping of the tower consumes. -/
theorem base_pairing_bd {lam : ℝ} {K : Set ℝ} {C₀ C κ : ℝ}
    (hC₀ : HasLEBound lam K C₀) (hκ : 0 < κ) (hC₀pos : 0 < C₀)
    {α : ℝ} {q : ℕ} (hq : 1 ≤ q) (hqC : C * (κ ^ 2)⁻¹ ≤ (q : ℝ))
    {E : ℝ} (hE : E ∈ K) (hL : 100 * κ < lyap α lam (E : ℂ)) :
    ∃ N₀ : ℕ, q ∣ N₀ ∧ 1 ≤ N₀ ∧
      C * (κ ^ 2)⁻¹ * (q : ℝ) ≤ (N₀ : ℝ) ∧
      (N₀ : ℝ) ≤ ((max 1 (Nat.ceil (C * (κ ^ 2)⁻¹))
          * 2 ^ (Nat.ceil (Real.log (C₀ / (100 * κ)) / Real.log (10 / 9)) + 1) : ℕ) : ℝ)
        * (q : ℝ) ∧
      100 * κ < lyapAvg α lam (E : ℂ) N₀ ∧
      (9 / 10) * lyapAvg α lam (E : ℂ) N₀ < lyapAvg α lam (E : ℂ) (2 * N₀) := by
  classical
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  set M : ℕ := max 1 (Nat.ceil (C * (κ ^ 2)⁻¹)) with hM
  set t : ℕ := q * M with ht
  have hM1 : 1 ≤ M := by rw [hM]; exact le_max_left 1 _
  have ht1 : 1 ≤ t := by
    rw [ht]
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ q * M := Nat.mul_le_mul hq hM1
  have htq : q ∣ t := by rw [ht]; exact dvd_mul_right q M
  have htC : C * (κ ^ 2)⁻¹ * (q : ℝ) ≤ (t : ℝ) := by
    have hceil : C * (κ ^ 2)⁻¹ ≤ (M : ℝ) := by
      rw [hM, Nat.cast_max]
      exact le_trans (Nat.le_ceil _) (le_max_right _ _)
    have hcast : (t : ℝ) = (q : ℝ) * (M : ℝ) := by rw [ht]; push_cast; ring
    rw [hcast]
    nlinarith [hceil, hqpos]
  set J : ℕ := Nat.ceil (Real.log (C₀ / (100 * κ)) / Real.log (10 / 9)) + 1 with hJ
  have hJcond : Real.log (C₀ / (100 * κ)) / Real.log (10 / 9) < (J : ℝ) := by
    rw [hJ]; push_cast
    linarith [Nat.le_ceil (Real.log (C₀ / (100 * κ)) / Real.log (10 / 9))]
  have ht1' : 1 ≤ t * 2 ^ J := le_trans ht1 (Nat.le_mul_of_pos_right t (pow_pos (by norm_num) J))
  have htop : 100 * κ < lyapAvg α lam (E : ℂ) (t * 2 ^ J) :=
    lt_of_lt_of_le hL (Work.TMC7Core.Scale.lyap_le_lyapAvg α lam (E : ℂ) ht1')
  obtain ⟨j, hjJ, hp⟩ :=
    Work.TMComp.LocCantor.dyadic_level_pairing (fun n => lyapAvg α lam (E : ℂ) n) t J C₀ κ
      hκ ht1 (fun m _ => Work.TMC7Core.Scale.lyapAvg_two_le α lam (E : ℂ) m)
      (fun m => Work.TMComp.C7Aux.lyapAvg_le_of_hasLEBound hC₀ hE α m) htop hJcond
  have hj1 : 1 ≤ t * 2 ^ j := le_trans ht1 (Nat.le_mul_of_pos_right t (pow_pos (by norm_num) j))
  refine ⟨t * 2 ^ j, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact dvd_trans htq (dvd_mul_right t (2 ^ j))
  · exact hj1
  · calc C * (κ ^ 2)⁻¹ * (q : ℝ) ≤ (t : ℝ) := htC
      _ ≤ ((t * 2 ^ j : ℕ) : ℝ) := by
          have h : t ≤ t * 2 ^ j := Nat.le_mul_of_pos_right t (pow_pos (by norm_num) j)
          exact_mod_cast h
  · have hupper : ((t * 2 ^ j : ℕ) : ℝ) ≤ ((M * 2 ^ J : ℕ) : ℝ) * (q : ℝ) := by
      have hMj : M * 2 ^ j ≤ M * 2 ^ J :=
        Nat.mul_le_mul_left M (Nat.pow_le_pow_right (by norm_num) (le_of_lt hjJ))
      have hnat : t * 2 ^ j ≤ M * 2 ^ J * q := by
        rw [ht]
        calc q * M * 2 ^ j = M * 2 ^ j * q := by ring
          _ ≤ M * 2 ^ J * q := Nat.mul_le_mul_right q hMj
      calc ((t * 2 ^ j : ℕ) : ℝ) ≤ ((M * 2 ^ J * q : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = ((M * 2 ^ J : ℕ) : ℝ) * (q : ℝ) := by push_cast; ring
    exact hupper
  · exact lt_of_lt_of_le hL (Work.TMC7Core.Scale.lyap_le_lyapAvg α lam (E : ℂ) hj1)
  · have h2N : 2 * (t * 2 ^ j) = t * 2 ^ (j + 1) := by rw [pow_succ]; ring
    rw [h2N]; exact hp

end Work.TMC7Core.Scale
