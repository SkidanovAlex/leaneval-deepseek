import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial

/-- `Δ(z;k) = (z+1)⋯(z+k)/k!` evaluated at a complex point `z`, written as an explicit product.
This is the form `deltaPoly` takes under `Polynomial.aeval`. -/
lemma Delta_eq_prod (z : ℂ) (k : ℕ) :
    Delta z k = ((k.factorial : ℂ))⁻¹ * ∏ i ∈ Finset.range k, (z + ((i : ℂ) + 1)) := by
  rw [Delta, deltaPoly]
  simp only [Polynomial.aeval_def, Polynomial.eval₂_smul]
  rw [show (algebraMap ℚ ℂ) ((k.factorial : ℚ))⁻¹ = ((k.factorial : ℂ))⁻¹ by simp]
  congr 1
  rw [Polynomial.eval₂_finsetProd]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp

/-- `Δ(z;k)` is bounded by `(e (1 + |z|/k))^k`. -/
theorem norm_Delta_le (z : ℂ) (k : ℕ) :
    ‖Delta z k‖ ≤ (Real.exp 1 * (1 + ‖z‖ / (k : ℝ))) ^ k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp [Delta, deltaPoly]
  · have hprod : ∏ i ∈ Finset.range k, ‖z + ((i : ℂ) + 1)‖ ≤ (‖z‖ + (k : ℝ))^k := by
      calc ∏ i ∈ Finset.range k, ‖z + ((i : ℂ) + 1)‖
          ≤ ∏ i ∈ Finset.range k, (‖z‖ + (k : ℝ)) := by
            apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
            intro i hi
            have hik : (i : ℝ) + 1 ≤ (k : ℝ) := by
              have : i + 1 ≤ k := by
                have := Finset.mem_range.mp hi
                omega
              exact_mod_cast this
            calc ‖z + ((i : ℂ) + 1)‖ ≤ ‖z‖ + ‖(i : ℂ) + 1‖ := norm_add_le _ _
              _ ≤ ‖z‖ + (‖(i : ℂ)‖ + ‖(1 : ℂ)‖) := by gcongr; exact norm_add_le _ _
              _ = ‖z‖ + ((i : ℝ) + 1) := by simp
              _ ≤ ‖z‖ + (k : ℝ) := by linarith
        _ = (‖z‖ + (k : ℝ))^k := by rw [Finset.prod_const, Finset.card_range]
    have hstep : ((k.factorial : ℝ))⁻¹ * (‖z‖ + (k : ℝ))^k ≤
        (Real.exp 1 * (1 + ‖z‖ / (k : ℝ)))^k := by
      have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      -- the `k`-th term of the exponential series lower bounds `e^k` by `k^k/k!`
      have key : (k : ℝ)^k / (k.factorial : ℝ) ≤ Real.exp (k : ℝ) := by
        have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) by positivity) (k + 1)
        have hterm : (k : ℝ)^k / (k.factorial : ℝ) ≤
            ∑ i ∈ Finset.range (k + 1), (k : ℝ)^i / ((i.factorial : ℕ) : ℝ) :=
          Finset.single_le_sum (s := Finset.range (k+1))
            (f := fun i : ℕ => (k : ℝ)^i / ((i.factorial : ℕ) : ℝ))
            (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self k))
        linarith
      have hsplit : ‖z‖ + (k : ℝ) = (k : ℝ) * (1 + ‖z‖ / (k : ℝ)) := by
        rw [mul_add, mul_one, mul_div_cancel₀ _ (ne_of_gt hkR)]; ring
      calc ((k.factorial : ℝ))⁻¹ * (‖z‖ + (k : ℝ))^k
          = ((k : ℝ)^k / (k.factorial : ℝ)) * (1 + ‖z‖ / (k : ℝ))^k := by
            rw [hsplit, mul_pow]; ring
        _ ≤ Real.exp (k : ℝ) * (1 + ‖z‖ / (k : ℝ))^k :=
            mul_le_mul_of_nonneg_right key (by positivity)
        _ = (Real.exp 1 * (1 + ‖z‖ / (k : ℝ)))^k := by
            rw [mul_pow, ← Real.exp_nat_mul]
            norm_num
    rw [Delta_eq_prod, norm_mul, norm_inv, norm_natCast, norm_prod]
    calc ((k.factorial : ℝ))⁻¹ * ∏ i ∈ Finset.range k, ‖z + ((i : ℂ) + 1)‖
        ≤ ((k.factorial : ℝ))⁻¹ * (‖z‖ + (k : ℝ))^k :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ ≤ (Real.exp 1 * (1 + ‖z‖ / (k : ℝ)))^k := hstep

end Work.BW
