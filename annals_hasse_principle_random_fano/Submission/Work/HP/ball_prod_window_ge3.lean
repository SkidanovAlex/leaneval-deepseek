import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.lam_basic

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.HP

/-- If `D ≤ c * A'` with `A' ≥ 0` and `D > 0`, then `1 / A' ≤ c / D`. -/
lemma one_div_le_div_of_le_mul {c D A' : ℝ} (hA : 0 ≤ A') (hD : 0 < D)
    (h : D ≤ c * A') : 1 / A' ≤ c / D := by
  have hApos : 0 < A' := by
    by_contra hcon
    have h0 : A' = 0 := le_antisymm (le_of_not_gt hcon) hA
    rw [h0, mul_zero] at h
    linarith
  rw [div_le_div_iff₀ hApos hD]
  simpa using h

/-- The arithmetic core of the window estimate for `r ≥ 1`: multiplying the two ball-count
bounds and dividing by the `2 ^ {k_j}` window quantities. -/
lemma arith_core (r : ℕ) (hr : 1 ≤ r) (K A B X Y : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (k0 k1 : ℕ)
    (h0 : (2 : ℝ) ^ k0 ≤ 2 * A) (h1 : (2 : ℝ) ^ k1 ≤ 2 * B) :
    (K * X ^ r / A ^ r) * (K * Y ^ r / (A * B ^ (r - 1))) ≤
      K ^ 2 * (2 : ℝ) ^ (2 * r) * X ^ r * Y ^ r /
        ((2 : ℝ) ^ (r * k0) * (2 : ℝ) ^ (k0 + (r - 1) * k1)) := by
  have h2A : (0 : ℝ) ≤ (2 * A) ^ (r + 1) := pow_nonneg (by linarith) _
  have h2pow : (2 : ℝ) ^ (r + 1) * (2 : ℝ) ^ (r - 1) = (2 : ℝ) ^ (2 * r) := by
    rw [← pow_add]; congr 1; omega
  have hexp : (r + 1) * k0 + (r - 1) * k1 = k0 * (r + 1) + k1 * (r - 1) := by ring
  have hexp2 : r * k0 + (k0 + (r - 1) * k1) = (r + 1) * k0 + (r - 1) * k1 := by ring
  -- the key power inequality
  have hkey : (2 : ℝ) ^ ((r + 1) * k0 + (r - 1) * k1) ≤
      (2 : ℝ) ^ (2 * r) * (A ^ (r + 1) * B ^ (r - 1)) := by
    have h0' : ((2 : ℝ) ^ k0) ^ (r + 1) ≤ (2 * A) ^ (r + 1) :=
      pow_le_pow_left₀ (by positivity) h0 _
    have h1' : ((2 : ℝ) ^ k1) ^ (r - 1) ≤ (2 * B) ^ (r - 1) :=
      pow_le_pow_left₀ (by positivity) h1 _
    have hmul : ((2 : ℝ) ^ k0) ^ (r + 1) * ((2 : ℝ) ^ k1) ^ (r - 1) ≤
        (2 * A) ^ (r + 1) * (2 * B) ^ (r - 1) :=
      mul_le_mul h0' h1' (by positivity) h2A
    calc (2 : ℝ) ^ ((r + 1) * k0 + (r - 1) * k1)
        = ((2 : ℝ) ^ k0) ^ (r + 1) * ((2 : ℝ) ^ k1) ^ (r - 1) := by
          rw [hexp, pow_add, pow_mul, pow_mul]
      _ ≤ (2 * A) ^ (r + 1) * (2 * B) ^ (r - 1) := hmul
      _ = (2 : ℝ) ^ (2 * r) * (A ^ (r + 1) * B ^ (r - 1)) := by
          rw [mul_pow, mul_pow]
          rw [show (2 : ℝ) ^ (r + 1) * A ^ (r + 1) * ((2 : ℝ) ^ (r - 1) * B ^ (r - 1))
                = ((2 : ℝ) ^ (r + 1) * (2 : ℝ) ^ (r - 1)) * (A ^ (r + 1) * B ^ (r - 1))
              from by ring]
          rw [h2pow]
  have hA' : (0 : ℝ) ≤ A ^ (r + 1) * B ^ (r - 1) :=
    mul_nonneg (pow_nonneg hA _) (pow_nonneg hB _)
  have hDpos : 0 < (2 : ℝ) ^ (r * k0) * (2 : ℝ) ^ (k0 + (r - 1) * k1) := by positivity
  have hDeq : (2 : ℝ) ^ (r * k0) * (2 : ℝ) ^ (k0 + (r - 1) * k1)
      = (2 : ℝ) ^ ((r + 1) * k0 + (r - 1) * k1) := by
    rw [← pow_add, hexp2]
  have hkey' : (2 : ℝ) ^ (r * k0) * (2 : ℝ) ^ (k0 + (r - 1) * k1) ≤
      (2 : ℝ) ^ (2 * r) * (A ^ (r + 1) * B ^ (r - 1)) := by
    rw [hDeq]; exact hkey
  have hdiv : 1 / (A ^ (r + 1) * B ^ (r - 1)) ≤
      (2 : ℝ) ^ (2 * r) /
        ((2 : ℝ) ^ (r * k0) * (2 : ℝ) ^ (k0 + (r - 1) * k1)) :=
    one_div_le_div_of_le_mul hA' hDpos hkey'
  have hP : (0 : ℝ) ≤ K ^ 2 * X ^ r * Y ^ r :=
    mul_nonneg (mul_nonneg (sq_nonneg K) (pow_nonneg hX r)) (pow_nonneg hY r)
  have hLHS : (K * X ^ r / A ^ r) * (K * Y ^ r / (A * B ^ (r - 1)))
      = K ^ 2 * X ^ r * Y ^ r / (A ^ (r + 1) * B ^ (r - 1)) := by
    rw [div_mul_div_comm]
    congr 1
    · ring
    · rw [pow_succ]; ring
  have hRHS : (K ^ 2 * X ^ r * Y ^ r) *
        ((2 : ℝ) ^ (2 * r) /
          ((2 : ℝ) ^ (r * k0) * (2 : ℝ) ^ (k0 + (r - 1) * k1)))
      = K ^ 2 * (2 : ℝ) ^ (2 * r) * X ^ r * Y ^ r /
          ((2 : ℝ) ^ (r * k0) * (2 : ℝ) ^ (k0 + (r - 1) * k1)) := by
    rw [← mul_div_assoc]; ring
  calc (K * X ^ r / A ^ r) * (K * Y ^ r / (A * B ^ (r - 1)))
      = K ^ 2 * X ^ r * Y ^ r / (A ^ (r + 1) * B ^ (r - 1)) := hLHS
    _ = K ^ 2 * X ^ r * Y ^ r * (1 / (A ^ (r + 1) * B ^ (r - 1))) := by
          rw [mul_one_div]
    _ ≤ K ^ 2 * X ^ r * Y ^ r *
          ((2 : ℝ) ^ (2 * r) /
            ((2 : ℝ) ^ (r * k0) * (2 : ℝ) ^ (k0 + (r - 1) * k1))) :=
          mul_le_mul_of_nonneg_left hdiv hP
    _ = K ^ 2 * (2 : ℝ) ^ (2 * r) * X ^ r * Y ^ r /
          ((2 : ℝ) ^ (r * k0) * (2 : ℝ) ^ (k0 + (r - 1) * k1)) := hRHS

theorem ball_prod_window_ge3 (n r : ℕ) (hn : 2 ≤ n) (hr : 3 ≤ r) (hrn : r ≤ n + 1)
    (Ksmall : ℝ) (hKsmall : 0 < Ksmall)
    (hsmallX : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (X : ℝ), 1 ≤ X → lam L 1 ≤ X →
      (ballCount L X : ℝ) ≤ Ksmall * X ^ rk L / lam L 1 ^ rk L)
    (hsmallY : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (Y : ℝ), 1 ≤ Y → 2 ≤ rk L → lam L 2 ≤ Y →
      (ballCount L Y : ℝ) ≤ Ksmall * Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1)))
    (L : Submodule ℤ (Fin (n + 1) → ℤ)) (hrL : rk L = r) (k : Fin r → ℕ)
    (hk2 : ∀ j : Fin r, (2 : ℝ) ^ (k j) ≤ 2 * lam L (j.1 + 1))
    (X Y : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hlX : lam L 1 ≤ X) (hlY : lam L 2 ≤ Y) :
    (ballCount L X : ℝ) * (ballCount L Y : ℝ) ≤
      Ksmall ^ 2 * (2 : ℝ) ^ (2 * r) * X ^ r * Y ^ r /
        ((2 : ℝ) ^ (r * k ⟨0, by omega⟩) *
          (2 : ℝ) ^ (k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩)) := by
  have hrk : 2 ≤ rk L := by rw [hrL]; omega
  have hBCX := hsmallX L X hX hlX
  have hBCY := hsmallY L Y hY hrk hlY
  rw [hrL] at hBCX hBCY
  have hprod : (ballCount L X : ℝ) * (ballCount L Y : ℝ) ≤
      (Ksmall * X ^ r / lam L 1 ^ r) * (Ksmall * Y ^ r / (lam L 1 * lam L 2 ^ (r - 1))) :=
    mul_le_mul hBCX hBCY (Nat.cast_nonneg _)
      (div_nonneg (mul_nonneg (le_of_lt hKsmall) (pow_nonneg (by linarith) r))
        (pow_nonneg (lam_nonneg L 1) r))
  refine le_trans hprod ?_
  have hk0 : (2 : ℝ) ^ (k ⟨0, by omega⟩) ≤ 2 * lam L 1 := by
    have := hk2 ⟨0, by omega⟩
    simpa using this
  have hk1 : (2 : ℝ) ^ (k ⟨1, by omega⟩) ≤ 2 * lam L 2 := by
    have := hk2 ⟨1, by omega⟩
    simpa using this
  exact arith_core r (by omega) Ksmall (lam L 1) (lam L 2) X Y
    (lam_nonneg L 1) (lam_nonneg L 2) (by linarith) (by linarith)
    (k ⟨0, by omega⟩) (k ⟨1, by omega⟩) hk0 hk1

end Work.HP
