import Mathlib
import Submission.Work.Recursion.defs

namespace Work.Recursion

/-- Paper §5.1: `α = ⌈(12d²b)^{1/4}⌉ ≤ ((12d²)^{1/4}+1) b^{1/4}`. -/
theorem aparBound (n : ℕ) (hn : 2 ≤ n) :
    (HvdH.apar n : ℝ) ≤
      ((12 * (HvdH.D : ℝ) ^ 2) ^ ((1 : ℝ) / 4) + 1) * (HvdH.bpar n : ℝ) ^ ((1 : ℝ) / 4) := by
  have hb : 1 ≤ HvdH.bpar n := by
    have : 0 < HvdH.bpar n := Nat.clog_pos (by norm_num) (by omega)
    omega
  have hbR : (1 : ℝ) ≤ (HvdH.bpar n : ℝ) := by exact_mod_cast hb
  set m : ℕ := 12 * HvdH.D ^ 2 * HvdH.bpar n with hm
  have hmR : (m : ℝ) = 12 * (HvdH.D : ℝ) ^ 2 * (HvdH.bpar n : ℝ) := by
    rw [hm]; push_cast; ring
  have hstep : (Nat.sqrt (Nat.sqrt (m - 1)) : ℝ) ≤
      (12 * (HvdH.D : ℝ) ^ 2) ^ ((1 : ℝ) / 4) * (HvdH.bpar n : ℝ) ^ ((1 : ℝ) / 4) := by
    have h1 : (Nat.sqrt (Nat.sqrt (m - 1)) : ℝ) ≤ Real.sqrt ((Nat.sqrt (m - 1) : ℕ) : ℝ) :=
      Real.nat_sqrt_le_real_sqrt
    have h2 : Real.sqrt ((Nat.sqrt (m - 1) : ℕ) : ℝ) ≤ Real.sqrt (Real.sqrt ((m - 1 : ℕ) : ℝ)) := by
      apply Real.sqrt_le_sqrt
      exact Real.nat_sqrt_le_real_sqrt
    have h3 : Real.sqrt (Real.sqrt ((m - 1 : ℕ) : ℝ)) ≤ Real.sqrt (Real.sqrt (m : ℝ)) := by
      apply Real.sqrt_le_sqrt; apply Real.sqrt_le_sqrt
      exact_mod_cast Nat.sub_le m 1
    have h4 : Real.sqrt (Real.sqrt (m : ℝ)) = (m : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (m : ℝ))]
      norm_num
    have h5 : (m : ℝ) ^ ((1 : ℝ) / 4) =
        (12 * (HvdH.D : ℝ) ^ 2) ^ ((1 : ℝ) / 4) * (HvdH.bpar n : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [hmR, Real.mul_rpow (by positivity) (by positivity)]
    calc (Nat.sqrt (Nat.sqrt (m - 1)) : ℝ)
        ≤ Real.sqrt ((Nat.sqrt (m - 1) : ℕ) : ℝ) := h1
      _ ≤ Real.sqrt (Real.sqrt ((m - 1 : ℕ) : ℝ)) := h2
      _ ≤ Real.sqrt (Real.sqrt (m : ℝ)) := h3
      _ = (m : ℝ) ^ ((1 : ℝ) / 4) := h4
      _ = (12 * (HvdH.D : ℝ) ^ 2) ^ ((1 : ℝ) / 4) * (HvdH.bpar n : ℝ) ^ ((1 : ℝ) / 4) := h5
  have hapar : ((HvdH.apar n : ℕ) : ℝ) = (Nat.sqrt (Nat.sqrt (m - 1)) : ℝ) + 1 := by
    unfold HvdH.apar
    rw [← hm]
    push_cast
    ring
  have hA : (0 : ℝ) ≤ (12 * (HvdH.D : ℝ) ^ 2) ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg (by positivity) _
  have hB : (1 : ℝ) ≤ (HvdH.bpar n : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.one_le_rpow hbR (by norm_num)
  rw [hapar]
  nlinarith [hstep, hA, hB]

end Work.Recursion
