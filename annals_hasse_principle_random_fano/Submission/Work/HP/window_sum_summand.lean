import Mathlib

namespace Work.HP

theorem window_sum_summand (n r : ℕ) (hn : 1 ≤ n) (hr : 3 ≤ r) (k : Fin r → ℕ) :
    (2 : ℝ) ^ (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1)))
      / ((2 : ℝ) ^ (r * k ⟨0, by omega⟩) *
          (2 : ℝ) ^ (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩))
    = (2 : ℝ) ^ (∑ j : Fin r, k j * (if (j.1 : ℕ) < 2 then (n + 1) - 2 else (n + 1) + r - 1 - 2 * j.1)) := by
  -- Pointwise: the left exponent summand splits as (right summand) + (correction supported on {0,1}).
  have hpoint : ∀ j : Fin r,
      k j * (n + 1 + r + 1 - 2 * (j.1 + 1))
        = k j * (if (j.1 : ℕ) < 2 then (n + 1) - 2 else (n + 1) + r - 1 - 2 * j.1)
          + k j * (if (j.1 : ℕ) < 2 then r + 1 - 2 * j.1 else 0) := by
    intro j
    rw [← mul_add]
    congr 1
    split <;> omega
  -- The correction sum equals r*k₀ + (k₀ + (r-1)*k₁).
  have hC : (∑ j : Fin r, k j * (if (j.1 : ℕ) < 2 then r + 1 - 2 * j.1 else 0))
      = r * k ⟨0, by omega⟩ + (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩) := by
    have hpoint2 : ∀ j : Fin r,
        k j * (if (j.1 : ℕ) < 2 then r + 1 - 2 * j.1 else 0)
          = (if j = (⟨0, by omega⟩ : Fin r) then k j * (r + 1) else 0)
            + (if j = (⟨1, by omega⟩ : Fin r) then k j * (r - 1) else 0) := by
      intro j
      by_cases h0 : j = (⟨0, by omega⟩ : Fin r)
      · subst h0; simp [Fin.ext_iff]
      by_cases h1 : j = (⟨1, by omega⟩ : Fin r)
      · subst h1; simp [Fin.ext_iff]
      · have hj0 : j.1 ≠ 0 := by intro h; exact h0 (Fin.ext h)
        have hj1 : j.1 ≠ 1 := by intro h; exact h1 (Fin.ext h)
        have hge : 2 ≤ j.1 := by omega
        simp [h0, h1, Nat.not_lt.mpr hge]
    trans ∑ j : Fin r, ((if j = (⟨0, by omega⟩ : Fin r) then k j * (r + 1) else 0)
            + (if j = (⟨1, by omega⟩ : Fin r) then k j * (r - 1) else 0))
    · exact Finset.sum_congr rfl (fun j _ => hpoint2 j)
    · rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ite_true]
      rw [← Nat.add_assoc, mul_comm (k ⟨1, by omega⟩) (r - 1)]
      congr 1
      rw [mul_add, mul_one, mul_comm (k ⟨0, by omega⟩) r]
  -- Combine into the exponent identity A = B + (r*k₀ + (k₀ + (r-1)*k₁)).
  have hA : (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1)))
      = (∑ j : Fin r, k j * (if (j.1 : ℕ) < 2 then (n + 1) - 2 else (n + 1) + r - 1 - 2 * j.1))
        + (r * k ⟨0, by omega⟩ + (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩)) := by
    calc (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1)))
        = ∑ j : Fin r, (k j * (if (j.1 : ℕ) < 2 then (n + 1) - 2 else (n + 1) + r - 1 - 2 * j.1)
              + k j * (if (j.1 : ℕ) < 2 then r + 1 - 2 * j.1 else 0)) :=
            Finset.sum_congr rfl (fun j _ => hpoint j)
      _ = (∑ j : Fin r, k j * (if (j.1 : ℕ) < 2 then (n + 1) - 2 else (n + 1) + r - 1 - 2 * j.1))
            + (∑ j : Fin r, k j * (if (j.1 : ℕ) < 2 then r + 1 - 2 * j.1 else 0)) :=
            Finset.sum_add_distrib
      _ = (∑ j : Fin r, k j * (if (j.1 : ℕ) < 2 then (n + 1) - 2 else (n + 1) + r - 1 - 2 * j.1))
            + (r * k ⟨0, by omega⟩ + (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩)) := by rw [hC]
  calc
    (2 : ℝ) ^ (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1)))
      / ((2 : ℝ) ^ (r * k ⟨0, by omega⟩) *
          (2 : ℝ) ^ (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩))
        = (2 : ℝ) ^ (∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1)))
            / (2 : ℝ) ^ (r * k ⟨0, by omega⟩ + (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩)) := by
          rw [← pow_add]
    _ = (2 : ℝ) ^ ((∑ j : Fin r, k j * (if (j.1 : ℕ) < 2 then (n + 1) - 2 else (n + 1) + r - 1 - 2 * j.1))
            + (r * k ⟨0, by omega⟩ + (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩)))
          / (2 : ℝ) ^ (r * k ⟨0, by omega⟩ + (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩)) := by
          rw [hA]
    _ = (2 : ℝ) ^ (∑ j : Fin r, k j * (if (j.1 : ℕ) < 2 then (n + 1) - 2 else (n + 1) + r - 1 - 2 * j.1)) := by
          rw [show (2 : ℝ) ^ ((∑ j : Fin r, k j * (if (j.1 : ℕ) < 2 then (n + 1) - 2 else (n + 1) + r - 1 - 2 * j.1))
                + (r * k ⟨0, by omega⟩ + (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩)))
              = (2 : ℝ) ^ (∑ j : Fin r, k j * (if (j.1 : ℕ) < 2 then (n + 1) - 2 else (n + 1) + r - 1 - 2 * j.1))
                * (2 : ℝ) ^ (r * k ⟨0, by omega⟩ + (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩)) by rw [pow_add]]
          exact mul_div_cancel_right₀ _ (pow_ne_zero _ (by norm_num))

end Work.HP
