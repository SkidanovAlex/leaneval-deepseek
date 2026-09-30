import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.vkN

set_option linter.unusedVariables false in
/--
Purely arithmetic rearrangement: with `theta = 2 * A * lam * H`, `A ≥ 1`, `H ≥ 0`,
`lam > 0`, `M ≥ 1` and `F = (k-1)!` (hence `F ≥ 1`), one has

`M * 100 * (1 + A * (lam/F) * M) * (1 + theta/(lam/F))
  ≤ 200 * A^2 * F * M * (1 + A * lam * M) * (1 + H)`.

Indeed `theta/(lam/F) = 2 * A * H * F ≤ 2 * A * F * (1 + H)`,
`A * (lam/F) * M ≤ A * lam * M` (as `F ≥ 1`), and `A ≤ A^2`.
-/
lemma final_arith {M k : ℕ} {lam A H theta : ℝ} (hM : 1 ≤ M) (hk : 2 ≤ k) (hlam : 0 < lam)
    (hA : 1 ≤ A) (hH : 0 ≤ H) (hth : theta = 2 * A * lam * H) :
    (M : ℝ) * (100 * (1 + A * (lam / ((Nat.factorial (k - 1) : ℕ) : ℝ)) * (M : ℝ)) *
        (1 + theta / (lam / ((Nat.factorial (k - 1) : ℕ) : ℝ))))
      ≤ 200 * A ^ 2 * ((Nat.factorial (k - 1) : ℕ) : ℝ) * (M : ℝ) * (1 + A * lam * (M : ℝ)) * (1 + H) := by
  set F : ℝ := ((Nat.factorial (k - 1) : ℕ) : ℝ) with hFdef
  have hF1 : (1 : ℝ) ≤ F := by
    rw [hFdef]
    have h := Nat.factorial_pos (k - 1)
    have : (1 : ℕ) ≤ (k - 1).factorial := Nat.succ_le_of_lt h
    exact_mod_cast this
  have hFpos : 0 < F := lt_of_lt_of_le zero_lt_one hF1
  have hF0 : (0 : ℝ) ≤ F := le_of_lt hFpos
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  -- `A * (lam/F) * M ≤ A * lam * M`
  have hXle : A * (lam / F) * (M : ℝ) ≤ A * lam * (M : ℝ) := by
    rw [show A * (lam / F) * (M : ℝ) = A * lam * (M : ℝ) / F by ring]
    exact div_le_self (by positivity) hF1
  -- `theta / (lam/F) = 2 * A * H * F`
  have hYeq : theta / (lam / F) = 2 * A * H * F := by
    rw [hth]; field_simp
  -- `1 + theta / (lam/F) ≤ 2 * A * F * (1 + H)`
  have hYle : 1 + theta / (lam / F) ≤ 2 * A * F * (1 + H) := by
    rw [hYeq]
    nlinarith [hA, hF1, hH]
  have hstep : (1 + A * (lam / F) * (M : ℝ)) * (1 + theta / (lam / F))
      ≤ 2 * A * F * (1 + A * lam * (M : ℝ)) * (1 + H) := by
    have hLR : (1 + A * (lam / F) * (M : ℝ)) * (1 + theta / (lam / F))
        ≤ (1 + A * lam * (M : ℝ)) * (2 * A * F * (1 + H)) := by
      apply mul_le_mul _ hYle _ _
      · linarith [hXle]
      · have : 0 ≤ theta / (lam / F) := by rw [hYeq]; positivity
        linarith
      · have : 0 ≤ A * lam * (M : ℝ) := by positivity
        linarith
    calc (1 + A * (lam / F) * (M : ℝ)) * (1 + theta / (lam / F))
        ≤ (1 + A * lam * (M : ℝ)) * (2 * A * F * (1 + H)) := hLR
      _ = 2 * A * F * (1 + A * lam * (M : ℝ)) * (1 + H) := by ring
  have hA2 : A ≤ A ^ 2 := by nlinarith [hA]
  have hZ0 : (0 : ℝ) ≤ 1 + A * lam * (M : ℝ) := by
    have : 0 ≤ A * lam * (M : ℝ) := by positivity
    linarith
  have hH1 : (0 : ℝ) ≤ 1 + H := by linarith
  calc (M : ℝ) * (100 * (1 + A * (lam / F) * (M : ℝ)) * (1 + theta / (lam / F)))
      = (M : ℝ) * (100 * ((1 + A * (lam / F) * (M : ℝ)) * (1 + theta / (lam / F)))) := by ring
    _ ≤ (M : ℝ) * (100 * (2 * A * F * (1 + A * lam * (M : ℝ)) * (1 + H))) := by
        apply mul_le_mul_of_nonneg_left _ hM0
        apply mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ ≤ 200 * A ^ 2 * F * (M : ℝ) * (1 + A * lam * (M : ℝ)) * (1 + H) := by
        have hC0 : (0 : ℝ) ≤ 200 * F * (M : ℝ) * (1 + A * lam * (M : ℝ)) * (1 + H) := by
          positivity
        have h := mul_le_mul_of_nonneg_right hA2 hC0
        calc (M : ℝ) * (100 * (2 * A * F * (1 + A * lam * (M : ℝ)) * (1 + H)))
            = A * (200 * F * (M : ℝ) * (1 + A * lam * (M : ℝ)) * (1 + H)) := by ring
          _ ≤ A ^ 2 * (200 * F * (M : ℝ) * (1 + A * lam * (M : ℝ)) * (1 + H)) := h
          _ = 200 * A ^ 2 * F * (M : ℝ) * (1 + A * lam * (M : ℝ)) * (1 + H) := by ring

end Work.BMF.vkN
