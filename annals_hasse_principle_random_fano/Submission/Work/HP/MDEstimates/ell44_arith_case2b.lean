import Mathlib

namespace Work.HP.MDEstimates

/-- Arithmetic estimate for the "case 2" region of the `ℓ^{(44)}` bound:
if `Z³ ≤ 1000² M¹⁰⁶ Δ` (and `Z, Δ, M ≥ 1`) then
`Z⁶ Δ³ ≤ 1000 Z^{9/2} Δ² (Z^{3/2} + Δ^{3/2}) M⁵³`.

Taking square roots of `Z³ ≤ 1000² M¹⁰⁶ Δ` gives `Z^{3/2} ≤ 1000 M⁵³ Δ^{1/2}`;
multiplying by `Δ` yields `Z^{3/2} Δ ≤ 1000 M⁵³ Δ^{3/2} ≤ 1000 (Z^{3/2}+Δ^{3/2}) M⁵³`,
and multiplying by `Z^{9/2} Δ²` gives the claim. -/
theorem ell44_arith_case2b :
    ∀ Z Δ M : ℝ, 1 ≤ Z → 1 ≤ Δ → 1 ≤ M → Z^3 ≤ 1000^2 * M^106 * Δ →
      Z^6 * Δ^3 ≤ 1000 * Z ^ ((9:ℝ)/2) * Δ^2 * (Z ^ ((3:ℝ)/2) + Δ ^ ((3:ℝ)/2)) * M^53 := by
  intro Z Δ M hZ hΔ hM h
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hΔpos : 0 < Δ := lt_of_lt_of_le zero_lt_one hΔ
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hZnn : 0 ≤ Z := le_of_lt hZpos
  have hΔnn : 0 ≤ Δ := le_of_lt hΔpos
  -- squares of the two sides of the root inequality
  have sqZ : (Z^((3:ℝ)/2))^2 = Z^3 := by
    rw [pow_two, ← Real.rpow_add hZpos]
    rw [show (3:ℝ)/2 + (3:ℝ)/2 = 3 by norm_num]
    exact Real.rpow_natCast Z 3
  have hd : (Δ^((1:ℝ)/2))^2 = Δ := by
    rw [pow_two, ← Real.rpow_add hΔpos]
    rw [show (1:ℝ)/2 + (1:ℝ)/2 = 1 by norm_num]
    exact Real.rpow_one Δ
  have hMsq : (M^53)^2 = M^106 := by ring
  have sqB : (1000 * M^53 * Δ^((1:ℝ)/2))^2 = 1000^2 * M^106 * Δ := by
    rw [mul_pow, mul_pow, hMsq, hd]
  have hsq : (Z^((3:ℝ)/2))^2 ≤ (1000 * M^53 * Δ^((1:ℝ)/2))^2 := by
    rw [sqZ, sqB]; exact h
  -- square root of the hypothesis
  have hsqrt : Z^((3:ℝ)/2) ≤ 1000 * M^53 * Δ^((1:ℝ)/2) :=
    (pow_le_pow_iff_left₀ (Real.rpow_nonneg hZnn _)
      (by positivity : (0:ℝ) ≤ 1000 * M^53 * Δ^((1:ℝ)/2)) (by norm_num : (2:ℕ) ≠ 0)).mp hsq
  have hd32 : Δ^((1:ℝ)/2) * Δ = Δ^((3:ℝ)/2) := by
    have hh := Real.rpow_add hΔpos ((1:ℝ)/2) (1:ℝ)
    rw [Real.rpow_one] at hh
    rw [show (1:ℝ)/2 + 1 = (3:ℝ)/2 by norm_num] at hh
    exact hh.symm
  have hZ6 : Z^6 = Z^((9:ℝ)/2) * Z^((3:ℝ)/2) := by
    rw [← Real.rpow_natCast Z 6, ← Real.rpow_add hZpos]
    norm_num
  -- the reduced inequality
  have hkey : Z^((3:ℝ)/2) * Δ ≤ 1000 * (Z^((3:ℝ)/2) + Δ^((3:ℝ)/2)) * M^53 := by
    have h1 : Z^((3:ℝ)/2) * Δ ≤ 1000 * M^53 * Δ^((3:ℝ)/2) := by
      have h2 := mul_le_mul_of_nonneg_right hsqrt hΔnn
      calc Z^((3:ℝ)/2) * Δ ≤ 1000 * M^53 * Δ^((1:ℝ)/2) * Δ := h2
        _ = 1000 * M^53 * Δ^((3:ℝ)/2) := by rw [mul_assoc (1000*M^53), hd32]
    calc Z^((3:ℝ)/2) * Δ ≤ 1000 * M^53 * Δ^((3:ℝ)/2) := h1
      _ ≤ 1000 * (Z^((3:ℝ)/2) + Δ^((3:ℝ)/2)) * M^53 := by
          have hle : Δ^((3:ℝ)/2) ≤ Z^((3:ℝ)/2) + Δ^((3:ℝ)/2) :=
            le_add_of_nonneg_left (Real.rpow_nonneg hZnn _)
          have hstep := mul_le_mul_of_nonneg_left hle
            (le_of_lt (by positivity : (0:ℝ) < 1000 * M^53))
          calc 1000 * M^53 * Δ^((3:ℝ)/2) = (1000*M^53) * Δ^((3:ℝ)/2) := by ring
            _ ≤ (1000*M^53) * (Z^((3:ℝ)/2) + Δ^((3:ℝ)/2)) := hstep
            _ = 1000 * (Z^((3:ℝ)/2) + Δ^((3:ℝ)/2)) * M^53 := by ring
  -- multiply back by Z^{9/2} Δ²
  have hZ92d2nn : 0 ≤ Z^((9:ℝ)/2) * Δ^2 :=
    mul_nonneg (Real.rpow_nonneg hZnn _) (pow_nonneg hΔnn 2)
  have hmul := mul_le_mul_of_nonneg_left hkey hZ92d2nn
  calc Z^6 * Δ^3 = Z^((9:ℝ)/2) * Δ^2 * (Z^((3:ℝ)/2) * Δ) := by rw [hZ6]; ring
    _ ≤ Z^((9:ℝ)/2) * Δ^2 * (1000 * (Z^((3:ℝ)/2) + Δ^((3:ℝ)/2)) * M^53) := hmul
    _ = 1000 * Z^((9:ℝ)/2) * Δ^2 * (Z^((3:ℝ)/2) + Δ^((3:ℝ)/2)) * M^53 := by ring

end Work.HP.MDEstimates
