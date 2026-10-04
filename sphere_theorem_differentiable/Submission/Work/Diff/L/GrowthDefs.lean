import Mathlib
import Submission.Diff.Alg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The scalar-curvature growth barrier

The ODE barrier used by the scalar-curvature maximum principle: the solution of `φ' = (2/n) φ²`
with `φ(0) = φ₀`, continued by `0` past its pole `n/(2φ₀)`.
-/

namespace Work.Diff.L

/-- The pole `n/(2φ₀)` of the barrier. -/
noncomputable def pole (n : ℕ) (φ₀ : ℝ) : ℝ := (n : ℝ) / (2 * φ₀)

/-- The barrier function: `t ↦ φ₀/(1 - (2/n)φ₀ t)` for `t` below the pole `n/(2φ₀)`, and `0`
past it. -/
noncomputable def φbar (n : ℕ) (φ₀ t : ℝ) : ℝ :=
  if t < pole n φ₀ then φ₀ / (1 - (2 / (n : ℝ)) * φ₀ * t) else 0

lemma φbar_def (n : ℕ) (φ₀ t : ℝ) :
    φbar n φ₀ t
      = if t < (n : ℝ) / (2 * φ₀) then φ₀ / (1 - (2 / (n : ℝ)) * φ₀ * t) else 0 := rfl

lemma φbar_of_lt {n : ℕ} {φ₀ t : ℝ} (h : t < pole n φ₀) :
    φbar n φ₀ t = φ₀ / (1 - (2 / (n : ℝ)) * φ₀ * t) := by
  rw [φbar]
  exact if_pos h

lemma φbar_of_pole_le {n : ℕ} {φ₀ t : ℝ} (h : pole n φ₀ ≤ t) : φbar n φ₀ t = 0 := by
  rw [φbar]
  exact if_neg (not_lt.mpr h)

/-- Below the pole the denominator `1 - (2/n)φ₀ t` is positive. -/
lemma one_sub_mul_pos_of_lt_pole {n : ℕ} {φ₀ t : ℝ} (hφ₀ : 0 < φ₀) (h : t < pole n φ₀) :
    0 < 1 - (2 / (n : ℝ)) * φ₀ * t := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hβ : 0 < (2 / (n : ℝ)) * φ₀ := by positivity
    have hpole : (2 / (n : ℝ)) * φ₀ * pole n φ₀ = 1 := by
      rw [pole]
      field_simp
    have := mul_lt_mul_of_pos_left h hβ
    rw [hpole] at this
    linarith

/-- The barrier is nonnegative. -/
lemma φbar_nonneg {n : ℕ} {φ₀ : ℝ} (hφ₀ : 0 < φ₀) (t : ℝ) : 0 ≤ φbar n φ₀ t := by
  rw [φbar]
  split_ifs with h
  · exact div_nonneg hφ₀.le (one_sub_mul_pos_of_lt_pole hφ₀ h).le
  · exact le_refl 0

/-- Where the denominator is positive, the barrier is at most `φ₀/(1 - (2/n)φ₀ t)`. -/
lemma φbar_le_div {n : ℕ} {φ₀ t : ℝ} (hφ₀ : 0 < φ₀)
    (h : 0 < 1 - (2 / (n : ℝ)) * φ₀ * t) :
    φbar n φ₀ t ≤ φ₀ / (1 - (2 / (n : ℝ)) * φ₀ * t) := by
  rw [φbar]
  split_ifs with _
  · exact le_rfl
  · exact div_nonneg hφ₀.le h.le

end Work.Diff.L
