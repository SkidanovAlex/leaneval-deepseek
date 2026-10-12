import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

/-- The sharp Bogoliubov coefficient inequality: with `A = γ + β`, `β, γ > 0` and `B ^ 2 ≤ β ^ 2`,
the Bogoliubov coefficient `(A - √(A ^ 2 - B ^ 2)) / 2` is at most `B ^ 2 / (4 * γ)`.

Writing `s = √(A ^ 2 - B ^ 2)` one has `(A - s) * (A + s) = B ^ 2`, hence `A - s = B ^ 2 / (A + s)`,
and `A + s ≥ γ + β + γ ≥ 2 * γ` because `s ≥ γ` (as `s ^ 2 = A ^ 2 - B ^ 2 ≥ A ^ 2 - β ^ 2 ≥ γ ^ 2`).
Therefore `(A - s) / 2 = B ^ 2 / (2 * (A + s)) ≤ B ^ 2 / (4 * γ)`. -/
theorem bogCoeffSharpLe {A B γ β : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hA : A = γ + β)
    (hB : B ^ 2 ≤ β ^ 2) :
    (A - Real.sqrt (A ^ 2 - B ^ 2)) / 2 ≤ B ^ 2 / (4 * γ) := by
  have hApos : 0 < A := by rw [hA]; linarith
  have hsqnn : 0 ≤ A ^ 2 - B ^ 2 := by nlinarith [hA, hβ, hγ, hB, sq_nonneg β]
  set s := Real.sqrt (A ^ 2 - B ^ 2) with hsdef
  have hs2 : s ^ 2 = A ^ 2 - B ^ 2 := Real.sq_sqrt hsqnn
  have hsnn : 0 ≤ s := Real.sqrt_nonneg _
  have hB2nn : 0 ≤ B ^ 2 := sq_nonneg B
  have hAs_pos : 0 < A + s := by linarith
  -- `s ≥ γ`, since `s ^ 2 = A ^ 2 - B ^ 2 ≥ A ^ 2 - β ^ 2 = γ ^ 2 + 2 * γ * β ≥ γ ^ 2`.
  have hsge : γ ≤ s := by
    have h : γ ^ 2 ≤ A ^ 2 - B ^ 2 := by nlinarith [hA, hβ, hγ, hB]
    calc γ = Real.sqrt (γ ^ 2) := (Real.sqrt_sq hγ.le).symm
      _ ≤ Real.sqrt (A ^ 2 - B ^ 2) := Real.sqrt_le_sqrt h
  have h2g : 2 * γ ≤ A + s := by linarith
  have hfact : (A - s) * (A + s) = B ^ 2 := by nlinarith [hs2]
  have hAsub : 0 ≤ A - s := by
    have : 0 ≤ (A - s) * (A + s) := by rw [hfact]; exact hB2nn
    nlinarith [hAs_pos, this]
  have hkey : (A - s) * (2 * γ) ≤ B ^ 2 := by
    have := mul_le_mul_of_nonneg_left h2g hAsub
    rw [hfact] at this
    linarith [this]
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * γ)]
  nlinarith [hkey]

end Work.BoseFixB1B
