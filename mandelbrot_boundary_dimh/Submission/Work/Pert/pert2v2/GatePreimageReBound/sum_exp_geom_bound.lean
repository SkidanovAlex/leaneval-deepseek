import Mathlib

namespace Work.Pert.pert2v2.GatePreimageReBound

theorem sum_exp_geom_bound (M κ C : ℝ) (hM : 0 < M) (hκ : 0 < κ) :
    ∀ t : ℝ, ∀ n : ℕ, (n : ℝ) ≤ (32 / 31) * (t + C) →
      (∑ j ∈ Finset.range n, M * Real.exp (-(κ * (t - (j : ℝ) / 32))))
        ≤ (M * Real.exp (κ * C / 31) / (Real.exp (κ / 32) - 1))
            * Real.exp (-((30 / 31 : ℝ) * κ * t)) := by
  intro t n hn
  have hκ32 : 0 < κ / 32 := by linarith
  have hr1 : (1 : ℝ) < Real.exp (κ / 32) := Real.one_lt_exp_iff.mpr hκ32
  have hden : 0 < Real.exp (κ / 32) - 1 := by linarith
  -- each summand is `exp (-(κ t)) * (exp (κ/32)) ^ j`
  have hterm : ∀ j : ℕ, Real.exp (-(κ * (t - (j : ℝ) / 32)))
      = Real.exp (-(κ * t)) * (Real.exp (κ / 32)) ^ j := by
    intro j
    have harg : -(κ * (t - (j : ℝ) / 32)) = -(κ * t) + (j : ℝ) * (κ / 32) := by ring
    rw [harg, Real.exp_add, Real.exp_nat_mul]
  -- the sum factors as a geometric series
  have hsum : (∑ j ∈ Finset.range n, M * Real.exp (-(κ * (t - (j : ℝ) / 32))))
      = M * Real.exp (-(κ * t)) * (∑ j ∈ Finset.range n, (Real.exp (κ / 32)) ^ j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hterm j]
    ring
  -- geometric bound
  have hgeo : (∑ j ∈ Finset.range n, (Real.exp (κ / 32)) ^ j)
      ≤ (Real.exp (κ / 32)) ^ n / (Real.exp (κ / 32) - 1) := by
    rw [geom_sum_eq (ne_of_gt hr1) n]
    apply div_le_div_of_nonneg_right _ (le_of_lt hden)
    have hnn : 0 ≤ (Real.exp (κ / 32)) ^ n := pow_nonneg (le_of_lt (Real.exp_pos _)) n
    linarith
  -- `exp (-(κ t)) * (exp (κ/32)) ^ n = exp (-(κ t) + κ n / 32)`
  have hpow : M * Real.exp (-(κ * t)) * (Real.exp (κ / 32)) ^ n
      = M * Real.exp (-(κ * t) + κ * (n : ℝ) / 32) := by
    have h1 : Real.exp (-(κ * t)) * (Real.exp (κ / 32)) ^ n
        = Real.exp (-(κ * t) + κ * (n : ℝ) / 32) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add,
        show -(κ * t) + (n : ℝ) * (κ / 32) = -(κ * t) + κ * (n : ℝ) / 32 by ring]
    rw [mul_assoc, h1]
  -- the hypothesis gives `κ n / 32 ≤ κ (t + C) / 31`
  have hn' : κ * (n : ℝ) / 32 ≤ κ * (t + C) / 31 := by
    have h1 : κ / 32 * (n : ℝ) ≤ κ / 32 * ((32 / 31) * (t + C)) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    have e1 : κ / 32 * (n : ℝ) = κ * (n : ℝ) / 32 := by ring
    have e2 : κ / 32 * ((32 / 31) * (t + C)) = κ * (t + C) / 31 := by ring
    rwa [e1, e2] at h1
  have hmono : Real.exp (-(κ * t) + κ * (n : ℝ) / 32)
      ≤ Real.exp (-(κ * t) + κ * (t + C) / 31) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hfinal : M * Real.exp (-(κ * t) + κ * (t + C) / 31) / (Real.exp (κ / 32) - 1)
      = (M * Real.exp (κ * C / 31) / (Real.exp (κ / 32) - 1))
          * Real.exp (-((30 / 31 : ℝ) * κ * t)) := by
    rw [show -(κ * t) + κ * (t + C) / 31 = κ * C / 31 + (-((30 / 31 : ℝ) * κ * t)) by ring,
      Real.exp_add]
    ring
  calc
    (∑ j ∈ Finset.range n, M * Real.exp (-(κ * (t - (j : ℝ) / 32))))
        = M * Real.exp (-(κ * t)) * (∑ j ∈ Finset.range n, (Real.exp (κ / 32)) ^ j) := hsum
    _ ≤ M * Real.exp (-(κ * t)) * ((Real.exp (κ / 32)) ^ n / (Real.exp (κ / 32) - 1)) :=
          mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = M * Real.exp (-(κ * t) + κ * (n : ℝ) / 32) / (Real.exp (κ / 32) - 1) := by
          rw [← mul_div_assoc, hpow]
    _ ≤ M * Real.exp (-(κ * t) + κ * (t + C) / 31) / (Real.exp (κ / 32) - 1) := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hden)
          exact mul_le_mul_of_nonneg_left hmono (le_of_lt hM)
    _ = (M * Real.exp (κ * C / 31) / (Real.exp (κ / 32) - 1))
            * Real.exp (-((30 / 31 : ℝ) * κ * t)) := hfinal

end Work.Pert.pert2v2.GatePreimageReBound
