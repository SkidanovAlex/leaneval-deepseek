import Mathlib

namespace Work.HP

/-- For `0 ≤ V`, the minimum of `1` and `V ^ 2` is at most `√V`. -/
lemma min_one_sq_le_sqrt (V : ℝ) (hV : 0 ≤ V) : min 1 (V^2) ≤ Real.sqrt V := by
  rcases le_total V 1 with h | h
  · rw [min_eq_right (by nlinarith [hV, h, sq_nonneg V])]
    rw [Real.le_sqrt (by positivity) hV]
    have h3 : V^3 ≤ 1 := pow_le_one₀ (n := 3) hV h
    nlinarith [mul_le_mul_of_nonneg_left h3 hV, hV, sq_nonneg V]
  · rw [min_eq_left (by nlinarith [h])]
    rw [Real.le_sqrt zero_le_one hV]
    linarith

/-- Monotone form: if `0 ≤ u ≤ V` then `min 1 (u ^ 2) ≤ √V`. -/
lemma min_one_sq_le_sqrt_of_le (u V : ℝ) (hu : 0 ≤ u) (h : u ≤ V) :
    min 1 (u^2) ≤ Real.sqrt V := by
  have hV : 0 ≤ V := le_trans hu h
  have h2 : u^2 ≤ V^2 := by nlinarith [hu, h]
  calc min 1 (u^2) ≤ min 1 (V^2) := min_le_min le_rfl h2
    _ ≤ Real.sqrt V := min_one_sq_le_sqrt V hV

theorem F1_arith (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α x y D Δ γ : ℝ), 1 ≤ α → 1 ≤ x → 1 ≤ y → 1 ≤ D → 0 ≤ Δ → 0 < γ →
      1 / γ ≤ C / (D * x ^ (d - 1) * y ^ (d - 1)) → Δ * D ≤ C * (x * y) →
      min 1 ((Δ / α) ^ 2) * (1 / γ)
        ≤ C ^ 2 * α ^ (-(1 / 2) : ℝ)
          / (D ^ ((3:ℝ)/2) * x ^ ((d:ℝ) - 3/2) * y ^ ((d:ℝ) - 3/2)) := by
  refine ⟨1, one_pos, ?_⟩
  intro α x y D Δ γ hα hx hy hD hΔ hγ hγb hDΔ
  simp only [one_pow, one_mul] at *
  have hα0 : 0 < α := by linarith
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hD0 : 0 < D := by linarith
  -- Δ ≤ x*y/D, hence Δ/α ≤ x*y/(D*α)
  have hΔle : Δ ≤ x * y / D := (le_div_iff₀ hD0).2 hDΔ
  have hu : Δ / α ≤ x * y / (D * α) := by
    have h2 : x * y / (D * α) = (x * y / D) / α := (div_div (x*y) D α).symm
    rw [h2]
    exact div_le_div_of_nonneg_right hΔle hα0.le
  have hmin : min 1 ((Δ/α)^2) ≤ Real.sqrt (x * y / (D * α)) :=
    min_one_sq_le_sqrt_of_le (Δ/α) (x*y/(D*α)) (div_nonneg hΔ hα0.le) hu
  -- the arithmetic identity converting the two sides
  have hsqrt : Real.sqrt (x*y/(D*α)) = Real.sqrt x * Real.sqrt y / (Real.sqrt D * Real.sqrt α) := by
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
  have key : Real.sqrt (x*y/(D*α)) * (1/(D * x^(d-1) * y^(d-1)))
      = α^(-(1/2) : ℝ) / (D^((3:ℝ)/2) * x^((d:ℝ)-3/2) * y^((d:ℝ)-3/2)) := by
    rw [hsqrt, eD, ex, ey]
    simp only [Real.sqrt_eq_rpow]
    rw [Real.rpow_neg (le_of_lt hα0)]
    field_simp
  calc min 1 ((Δ / α) ^ 2) * (1 / γ)
      ≤ Real.sqrt (x * y / (D * α)) * (1 / (D * x ^ (d - 1) * y ^ (d - 1))) :=
        mul_le_mul hmin hγb (by positivity) (Real.sqrt_nonneg _)
    _ = α ^ (-(1 / 2) : ℝ) / (D ^ ((3:ℝ)/2) * x ^ ((d:ℝ) - 3/2) * y ^ ((d:ℝ) - 3/2)) := key

end Work.HP
