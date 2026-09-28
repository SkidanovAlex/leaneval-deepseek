import Mathlib
import Submission.Work.HP.F1_arith

namespace Work.HP

theorem F1_arith2 (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α x y D Δ γ C₁ C₂ : ℝ), 1 ≤ α → 1 ≤ x → 1 ≤ y → 1 ≤ D → 0 ≤ Δ →
      0 < γ → 1 ≤ C₁ → 1 ≤ C₂ →
      1 / γ ≤ C₁ / (D * x ^ (d - 1) * y ^ (d - 1)) → Δ * D ≤ C₂ * (x * y) →
      min 1 ((Δ / α) ^ 2) * (1 / γ)
        ≤ C * C₁ * C₂ * α ^ (-(1 / 2) : ℝ)
          / (D ^ ((3:ℝ)/2) * x ^ ((d:ℝ) - 3/2) * y ^ ((d:ℝ) - 3/2)) := by
  refine ⟨1, one_pos, ?_⟩
  intro α x y D Δ γ C₁ C₂ hα hx hy hD hΔ hγ hC₁ hC₂ hγb hDΔ
  simp only [one_mul]
  have hα0 : 0 < α := by linarith
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hD0 : 0 < D := by linarith
  have hC₂0 : 0 < C₂ := by linarith
  -- Step 1: the min is controlled by `sqrt` of the upper bound coming from `Δ*D ≤ C₂*(x*y)`
  have hΔle : Δ ≤ C₂ * (x * y) / D := (le_div_iff₀ hD0).2 (by linarith [hDΔ])
  have hu : Δ / α ≤ C₂ * (x * y) / (D * α) := by
    have h2 : C₂ * (x * y) / (D * α) = (C₂ * (x * y) / D) / α := (div_div _ _ _).symm
    rw [h2]
    exact div_le_div_of_nonneg_right hΔle hα0.le
  have hmin : min 1 ((Δ / α) ^ 2) ≤ Real.sqrt (C₂ * (x * y) / (D * α)) :=
    min_one_sq_le_sqrt_of_le (Δ / α) (C₂ * (x * y) / (D * α)) (div_nonneg hΔ hα0.le) hu
  have hfac : C₂ * (x * y) / (D * α) = C₂ * (x * y / (D * α)) := by ring
  have hsq : Real.sqrt (C₂ * (x * y) / (D * α))
      = Real.sqrt C₂ * Real.sqrt (x * y / (D * α)) := by
    rw [hfac, Real.sqrt_mul hC₂0.le]
  have hleC₂ : Real.sqrt C₂ ≤ C₂ := by
    rw [Real.sqrt_le_iff]
    refine ⟨hC₂0.le, ?_⟩
    have h := le_mul_of_one_le_left hC₂0.le hC₂
    nlinarith [h]
  have hmin2 : min 1 ((Δ / α) ^ 2) ≤ C₂ * Real.sqrt (x * y / (D * α)) := by
    calc min 1 ((Δ / α) ^ 2) ≤ Real.sqrt (C₂ * (x * y) / (D * α)) := hmin
      _ = Real.sqrt C₂ * Real.sqrt (x * y / (D * α)) := hsq
      _ ≤ C₂ * Real.sqrt (x * y / (D * α)) :=
          mul_le_mul_of_nonneg_right hleC₂ (Real.sqrt_nonneg _)
  -- Step 2: the arithmetic identity for the `sqrt`/`(1/γ)` product
  have hsqrt : Real.sqrt (x * y / (D * α))
      = Real.sqrt x * Real.sqrt y / (Real.sqrt D * Real.sqrt α) := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (le_of_lt hx0), Real.sqrt_mul (le_of_lt hD0)]
  have eD : D ^ ((3:ℝ)/2) = D * Real.sqrt D := by
    rw [show (3:ℝ)/2 = 1 + 1/2 by norm_num, Real.rpow_add hD0, Real.rpow_one, Real.sqrt_eq_rpow]
  have ex : x ^ ((d:ℝ) - 3/2) = x ^ (d-1) / Real.sqrt x := by
    have h1 : ((d-1 : ℕ) : ℝ) = (d:ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ d)]; norm_num
    rw [show (d:ℝ) - 3/2 = ((d-1 : ℕ) : ℝ) + (-(1/2)) by rw [h1]; ring]
    rw [Real.rpow_add hx0, Real.rpow_natCast, Real.sqrt_eq_rpow]
    simp only [div_eq_mul_inv, one_mul]
    rw [← Real.rpow_neg (le_of_lt hx0)]
  have ey : y ^ ((d:ℝ) - 3/2) = y ^ (d-1) / Real.sqrt y := by
    have h1 : ((d-1 : ℕ) : ℝ) = (d:ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ d)]; norm_num
    rw [show (d:ℝ) - 3/2 = ((d-1 : ℕ) : ℝ) + (-(1/2)) by rw [h1]; ring]
    rw [Real.rpow_add hy0, Real.rpow_natCast, Real.sqrt_eq_rpow]
    simp only [div_eq_mul_inv, one_mul]
    rw [← Real.rpow_neg (le_of_lt hy0)]
  have key : Real.sqrt (x * y / (D * α)) * (1 / (D * x ^ (d - 1) * y ^ (d - 1)))
      = α ^ (-(1 / 2) : ℝ) / (D ^ ((3:ℝ)/2) * x ^ ((d:ℝ) - 3/2) * y ^ ((d:ℝ) - 3/2)) := by
    rw [hsqrt, eD, ex, ey]
    simp only [Real.sqrt_eq_rpow]
    rw [Real.rpow_neg (le_of_lt hα0)]
    field_simp
  -- Step 3: assemble
  calc min 1 ((Δ / α) ^ 2) * (1 / γ)
      ≤ C₂ * Real.sqrt (x * y / (D * α)) * (C₁ / (D * x ^ (d - 1) * y ^ (d - 1))) :=
        mul_le_mul hmin2 hγb (by positivity) (by positivity)
    _ = C₁ * C₂ * (Real.sqrt (x * y / (D * α)) * (1 / (D * x ^ (d - 1) * y ^ (d - 1)))) := by ring
    _ = C₁ * C₂ * (α ^ (-(1 / 2) : ℝ)
          / (D ^ ((3:ℝ)/2) * x ^ ((d:ℝ) - 3/2) * y ^ ((d:ℝ) - 3/2))) := by rw [key]
    _ = C₁ * C₂ * α ^ (-(1 / 2) : ℝ)
          / (D ^ ((3:ℝ)/2) * x ^ ((d:ℝ) - 3/2) * y ^ ((d:ℝ) - 3/2)) := by ring

end Work.HP
