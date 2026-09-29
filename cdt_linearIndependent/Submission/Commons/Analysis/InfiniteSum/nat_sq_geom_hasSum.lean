import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Cast

noncomputable section

namespace Commons.Analysis.InfiniteSum

/-- `Σₙ n²·Xⁿ = X(1+X)/(1−X)³` for real `‖X‖ < 1` (second moment of the geometric series). -/
lemma nat_sq_geom_hasSum {X : ℝ} (hX : ‖X‖ < 1) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 2 * X ^ n) (X * (1 + X) / (1 - X) ^ 3) := by
  -- n^2 = 2 * (n+2).choose 2 - 3 * (n+1).choose 1 + n.choose 0
  have hid : ∀ n : ℕ,
      (2 : ℝ) * (((n + 2).choose 2 : ℕ) : ℝ) - 3 * (((n + 1).choose 1 : ℕ) : ℝ) +
          (((n).choose 0 : ℕ) : ℝ) = (n : ℝ) ^ 2 := by
    intro n
    rw [Nat.cast_choose_two]
    norm_num
    ring_nf
  have hcoef : ∀ n : ℕ,
      (2 : ℝ) * (((n + 2).choose 2 : ℕ) : ℝ) - 3 * (((n + 1).choose 1 : ℕ) : ℝ) + 1 =
        (n : ℝ) ^ 2 := by
    intro n
    simpa using hid n
  -- Σ X^n = (1-X)⁻¹
  have h0 : HasSum (fun n : ℕ => X ^ n) ((1 - X)⁻¹) := hasSum_geometric_of_norm_lt_one hX
  -- Σ (n+1 choose 1) X^n = 1/(1-X)², Σ (n+2 choose 2) X^n = 1/(1-X)³
  have h1 : HasSum (fun n : ℕ => (((n + 1).choose 1 : ℕ) : ℝ) * X ^ n)
      (1 / (1 - X) ^ (1 + 1)) := hasSum_choose_mul_geometric_of_norm_lt_one 1 hX
  have h2 : HasSum (fun n : ℕ => (((n + 2).choose 2 : ℕ) : ℝ) * X ^ n)
      (1 / (1 - X) ^ (2 + 1)) := hasSum_choose_mul_geometric_of_norm_lt_one 2 hX
  -- linear combination: 2*Σ(n+2 choose 2)X^n - 3*Σ(n+1 choose 1)X^n + ΣX^n
  have hcomb : HasSum
      (fun n : ℕ => (2 : ℝ) * (((n + 2).choose 2 : ℕ) : ℝ) * X ^ n -
          (3 : ℝ) * (((n + 1).choose 1 : ℕ) : ℝ) * X ^ n + X ^ n)
      (2 * (1 / (1 - X) ^ (2 + 1)) - 3 * (1 / (1 - X) ^ (1 + 1)) + (1 - X)⁻¹) := by
    have hA : HasSum (fun n : ℕ => (2 : ℝ) * (((n + 2).choose 2 : ℕ) : ℝ) * X ^ n)
        (2 * (1 / (1 - X) ^ (2 + 1))) := by
      simpa [mul_assoc] using (h2.mul_left (2 : ℝ))
    have hB : HasSum (fun n : ℕ => (3 : ℝ) * (((n + 1).choose 1 : ℕ) : ℝ) * X ^ n)
        (3 * (1 / (1 - X) ^ (1 + 1))) := by
      simpa [mul_assoc] using (h1.mul_left (3 : ℝ))
    exact (hA.sub hB).add h0
  -- the summands are exactly (n:ℝ)^2 * X^n
  have hfun : (fun n : ℕ => (2 : ℝ) * (((n + 2).choose 2 : ℕ) : ℝ) * X ^ n -
          (3 : ℝ) * (((n + 1).choose 1 : ℕ) : ℝ) * X ^ n + X ^ n) =
      (fun n : ℕ => (n : ℝ) ^ 2 * X ^ n) := by
    funext n
    calc
      (2 : ℝ) * (((n + 2).choose 2 : ℕ) : ℝ) * X ^ n -
          (3 : ℝ) * (((n + 1).choose 1 : ℕ) : ℝ) * X ^ n + X ^ n
          = ((2 : ℝ) * (((n + 2).choose 2 : ℕ) : ℝ) -
              3 * (((n + 1).choose 1 : ℕ) : ℝ) + 1) * X ^ n := by ring
      _ = (n : ℝ) ^ 2 * X ^ n := by rw [hcoef n]
  -- closed form of the value
  have hXne : X ≠ 1 := by
    intro hx
    subst X
    norm_num at hX
  have hval : 2 * (1 / (1 - X) ^ (2 + 1)) - 3 * (1 / (1 - X) ^ (1 + 1)) + (1 - X)⁻¹ =
      X * (1 + X) / (1 - X) ^ 3 := by
    have hden : (1 - X : ℝ) ≠ 0 := sub_ne_zero.mpr hXne.symm
    field_simp [hden]
    ring
  convert hcomb using 1
  · exact hfun.symm
  · rw [hval]

end Commons.Analysis.InfiniteSum