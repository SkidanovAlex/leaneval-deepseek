import Mathlib
import Submission.Work.GM.Energy.EnergyCore.Setup2

namespace Work.GM.Energy.EnergyCore

/-!
# The harmonic-sum bound `Σ_{d ∈ [A, 2N]} ⌈N/d⌉ ≤ 4 N (1 + log 2N)`

We prove the elementary estimate used to control the total mass of the "gcd classes"
with `d ∈ [A, 2N]`.

The route is the standard one:
* `⌈N/d⌉ ≤ N/d + 1` (`Md_le_div_add_one`),
* `Σ_{d} 1/d ≤ 1 + log(2N)` for any initial index `A ≥ 1` (partial harmonic sum bound,
  obtained by telescoping `1/d ≤ log d - log (d-1)`),
* the number of summands is at most `2N`.

The two numerical constants (`4 = 3 + 1`) absorb the extra `log`-free terms.
-/

/-- `1/d ≤ log d - log (d-1)` for `d ≥ 2`, from `log x ≥ 1 - 1/x` at `x = d/(d-1)`. -/
private lemma inv_le_log_sub (d : ℕ) (hd : 2 ≤ d) :
    ((d : ℝ))⁻¹ ≤ Real.log (d : ℝ) - Real.log ((d : ℝ) - 1) := by
  have hd1 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd2 : (0 : ℝ) < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hx : 0 < (d : ℝ) / ((d : ℝ) - 1) := div_pos hd1 hd2
  have h := Real.one_sub_inv_le_log_of_pos hx
  rw [Real.log_div (ne_of_gt hd1) (ne_of_gt hd2), inv_div] at h
  have heq : 1 - ((d : ℝ) - 1) / (d : ℝ) = ((d : ℝ))⁻¹ := by
    field_simp
    ring
  rw [heq] at h
  exact h

/-- Partial harmonic sum bound: `Σ_{d=1}^{B} 1/d ≤ 1 + log B` for `B ≥ 1`. -/
private lemma sum_inv_le_log (B : ℕ) (hB : 1 ≤ B) :
    ∑ d ∈ Finset.Icc 1 B, ((d : ℝ))⁻¹ ≤ 1 + Real.log (B : ℝ) := by
  induction B, hB using Nat.le_induction with
  | base => norm_num
  | succ B hB ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ B + 1)]
    have hd := inv_le_log_sub (B + 1) (by omega)
    have hcast : (((B + 1 : ℕ)) : ℝ) - 1 = (B : ℝ) := by push_cast; ring
    rw [hcast] at hd
    linarith

/-- Partial harmonic sum bound with an arbitrary start `A ≥ 1`. -/
private lemma sum_inv_Icc_le (A B : ℕ) (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∑ d ∈ Finset.Icc A B, ((d : ℝ))⁻¹ ≤ 1 + Real.log (B : ℝ) := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left hA) ?_)
    (sum_inv_le_log B hB)
  intro x hx _
  have hx1 : 1 ≤ x := (Finset.mem_Icc.mp hx).1
  have : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  positivity

/-- `Σ_{d ∈ [A, 2N]} ⌈N/d⌉ ≤ 4 N (1 + log 2N)` (harmonic-sum bound). -/
theorem sum_Md_le (N A : ℕ) (hN : 1 ≤ N) (hA : 1 ≤ A) :
    ∑ d ∈ Finset.Icc A (2 * N), (Work.GM.Energy.EnergyCore.Md N d : ℝ)
      ≤ 4 * (N : ℝ) * (1 + Real.log (2 * N)) := by
  have hB : 1 ≤ 2 * N := by omega
  have h1 : ∑ d ∈ Finset.Icc A (2 * N), (Work.GM.Energy.EnergyCore.Md N d : ℝ)
      ≤ ∑ d ∈ Finset.Icc A (2 * N), ((N : ℝ) / (d : ℝ) + 1) :=
    Finset.sum_le_sum (fun d _ => Md_le_div_add_one N d)
  have h2 : ∑ d ∈ Finset.Icc A (2 * N), ((N : ℝ) / (d : ℝ) + 1)
      = (N : ℝ) * (∑ d ∈ Finset.Icc A (2 * N), ((d : ℝ))⁻¹)
        + ((Finset.Icc A (2 * N)).card : ℝ) := by
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [div_eq_mul_inv]
    · rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have h3 : ∑ d ∈ Finset.Icc A (2 * N), ((d : ℝ))⁻¹ ≤ 1 + Real.log (((2 * N : ℕ)) : ℝ) :=
    sum_inv_Icc_le A (2 * N) hA hB
  have h4 : ((Finset.Icc A (2 * N)).card : ℝ) ≤ (((2 * N : ℕ)) : ℝ) := by
    have hc : (Finset.Icc A (2 * N)).card ≤ (Finset.Icc 1 (2 * N)).card :=
      Finset.card_le_card (Finset.Icc_subset_Icc_left hA)
    have : (Finset.Icc 1 (2 * N)).card = 2 * N := by simp [Nat.card_Icc]
    rw [this] at hc
    exact_mod_cast hc
  have hNR : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hlog : (0 : ℝ) ≤ Real.log (((2 * N : ℕ)) : ℝ) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by exact_mod_cast hB
    linarith
  have hcast2 : (((2 * N : ℕ)) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  have hL : ∑ d ∈ Finset.Icc A (2 * N), (Work.GM.Energy.EnergyCore.Md N d : ℝ)
      ≤ (N : ℝ) * (1 + Real.log (((2 * N : ℕ)) : ℝ)) + (((2 * N : ℕ)) : ℝ) := by
    rw [h2] at h1
    have hm := mul_le_mul_of_nonneg_left h3 hNR
    linarith
  rw [hcast2] at hL hlog
  nlinarith [hL, hlog, hNR]

end Work.GM.Energy.EnergyCore
