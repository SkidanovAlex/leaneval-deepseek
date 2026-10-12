import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

/-- Elementary arithmetic bound: the weighted-energy expression
`E / (π N / (2ℓ)) + G * ((π N / 2)⁻¹ + (R/ℓ)^4 + (π N / 2)⁻²)` is at most `A`,
given the supply bound `N ≥ 4(1+ℓ)(1+E)(1+G)(1+G/A)/A + 4` and the definition
`A = K0 a / (8 μ (ℓ³+1))` together with `32 G μ (ℓ³+1) (R/ℓ)^4 / a ≤ K0`.

Splitting: `E/(πN/(2ℓ)) = 2ℓE/(πN) ≤ A/π`, `G (πN/2)⁻¹ = 2G/(πN) ≤ A/(2π)`,
`G (πN/2)⁻² = 4G/(π²N²) ≤ A/π²` (all from `4ℓE ≤ AN`, `4G ≤ AN`, `4G ≤ AN²`,
which follow from the supply bound), and `G (R/ℓ)^4 ≤ A/4` (from the `K0` bound);
finally `A/π + A/(2π) + A/4 + A/π² ≤ A` since `π ≥ 3`. -/
theorem chBarith {A E G K0 a ℓ μ R : ℝ}
    (hA : A = K0 * a / (8 * μ * (ℓ ^ 3 + 1))) (ha : 0 < a) (hμ : 0 < μ) (hℓ : 0 < ℓ)
    (hA0 : 0 < A) (hE0 : 0 ≤ E) (hG0 : 0 ≤ G) (hR0 : 0 ≤ R) (hRℓ : 2 * R ≤ ℓ)
    (hbig : 32 * G * μ * (ℓ ^ 3 + 1) * (R / ℓ) ^ 4 / a ≤ K0)
    {N : ℝ} (hN : 4 * (1 + ℓ) * (1 + E) * (1 + G) * (1 + G / A) / A + 4 ≤ N) :
    E / (Real.pi * N / (2 * ℓ))
      + G * (((Real.pi * N / (2 * ℓ)) * ℓ)⁻¹ + (R / ℓ) ^ 4
          + (((Real.pi * N / (2 * ℓ)) * ℓ) ^ 2)⁻¹) ≤ A := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hpi3 : (3:ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
  have hpi2 : (9:ℝ) ≤ Real.pi ^ 2 := by nlinarith only [hpi3, sq_nonneg (Real.pi - 3)]
  have h1la : (0:ℝ) ≤ G / A := div_nonneg hG0 (le_of_lt hA0)
  have hlE : (0:ℝ) ≤ ℓ * E := mul_nonneg (le_of_lt hℓ) hE0
  -- the supply bound forces `N ≥ 4`
  have hN4 : (4:ℝ) ≤ N := by
    have hterm : 0 ≤ 4 * (1 + ℓ) * (1 + E) * (1 + G) * (1 + G / A) / A := by positivity
    linarith only [hN, hterm]
  have hNpos : 0 < N := by linarith only [hN4]
  have hN1 : (1:ℝ) ≤ N := by linarith only [hN4]
  -- clearing the denominator of the supply bound
  have h4P : 4 * (1 + ℓ) * (1 + E) * (1 + G) * (1 + G / A) ≤ A * N := by
    have h1 : 4 * (1 + ℓ) * (1 + E) * (1 + G) * (1 + G / A) / A ≤ N := by linarith only [hN]
    have h2 := (div_le_iff₀ hA0).mp h1
    linarith only [h2]
  have hG1 : (1:ℝ) ≤ (1 + G) * (1 + G / A) := by nlinarith only [hG0, h1la]
  have hX1 : (1:ℝ) ≤ (1 + ℓ) * (1 + E) := by nlinarith only [hℓ, hE0]
  have hZ1 : (1:ℝ) ≤ (1 + ℓ) * (1 + E) * (1 + G / A) := by
    have h3 := mul_le_mul hX1 (by linarith only [h1la] : (1:ℝ) ≤ 1 + G / A) (by norm_num) (by positivity)
    simpa using h3
  have h4lE : 4 * ℓ * E ≤ A * N := by
    have hXnn : (0:ℝ) ≤ (1 + ℓ) * (1 + E) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hG1 hXnn
    have h2 : ℓ * E ≤ (1 + ℓ) * (1 + E) := by nlinarith only [hℓ, hE0]
    nlinarith only [h1, h2, h4P]
  have h2lE : 2 * ℓ * E ≤ A * N := by linarith only [h4lE, hlE]
  have h4G : 4 * G ≤ A * N := by
    have hYnn : (0:ℝ) ≤ 1 + G := by linarith only [hG0]
    have h1 := mul_le_mul_of_nonneg_left hZ1 hYnn
    nlinarith only [h1, h4P, hG0]
  have h4GN2 : 4 * G ≤ A * N^2 := by
    have hNN : N ≤ N^2 := by nlinarith only [hN1]
    have h := mul_le_mul_of_nonneg_left hNN (le_of_lt hA0)
    linarith only [h, h4G]
  -- the `K0` bound gives `G (R/ℓ)^4 ≤ A/4`
  have hAeq : A * (8 * μ * (ℓ ^ 3 + 1)) = K0 * a := by rw [hA]; field_simp
  have hbig' : 32 * G * μ * (ℓ ^ 3 + 1) * (R / ℓ) ^ 4 ≤ K0 * a := (div_le_iff₀ ha).mp hbig
  have h4Gu : 4 * (G * (R / ℓ) ^ 4) ≤ A := by
    have hden : (0:ℝ) < 8 * μ * (ℓ ^ 3 + 1) := by positivity
    have h1 : (4 * (G * (R / ℓ) ^ 4)) * (8 * μ * (ℓ ^ 3 + 1)) ≤ A * (8 * μ * (ℓ ^ 3 + 1)) := by
      nlinarith only [hbig', hAeq]
    exact le_of_mul_le_mul_right h1 hden
  have hGu : G * (R / ℓ) ^ 4 ≤ A / 4 := by linarith only [h4Gu]
  have hπN : (0:ℝ) < Real.pi * N := by positivity
  -- the three `π`-terms
  have hT1 : E / (Real.pi * N / (2 * ℓ)) ≤ A / Real.pi := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.pi * N / (2 * ℓ))]
    have heq : (A / Real.pi) * (Real.pi * N / (2 * ℓ)) = A * N / (2 * ℓ) := by
      field_simp
    rw [heq]
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * ℓ)]
    nlinarith only [h2lE]
  have hT2 : G * ((Real.pi * N / (2 * ℓ)) * ℓ)⁻¹ ≤ A / (2 * Real.pi) := by
    rw [show (Real.pi * N / (2 * ℓ)) * ℓ = Real.pi * N / 2 by field_simp]
    rw [inv_div]
    have ht : G * (2 / (Real.pi * N)) = 2 * G / (Real.pi * N) := by ring
    rw [ht]
    rw [div_le_iff₀ hπN]
    have hr : (A / (2 * Real.pi)) * (Real.pi * N) = A * N / 2 := by field_simp
    rw [hr]
    linarith only [h4G]
  have hT4 : G * (((Real.pi * N / (2 * ℓ)) * ℓ) ^ 2)⁻¹ ≤ A / Real.pi ^ 2 := by
    rw [show (Real.pi * N / (2 * ℓ)) * ℓ = Real.pi * N / 2 by field_simp]
    rw [show (Real.pi * N / 2) ^ 2 = Real.pi ^ 2 * N ^ 2 / 4 by ring]
    rw [inv_div]
    have ht : G * (4 / (Real.pi ^ 2 * N ^ 2)) = 4 * G / (Real.pi ^ 2 * N ^ 2) := by ring
    rw [ht]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.pi ^ 2 * N ^ 2)]
    have hr : (A / Real.pi ^ 2) * (Real.pi ^ 2 * N ^ 2) = A * N ^ 2 := by field_simp
    rw [hr]
    exact h4GN2
  -- the numerical comparison `π ≥ 3`
  have hfinal : A / Real.pi + A / (2 * Real.pi) + A / 4 + A / Real.pi ^ 2 ≤ A := by
    have h1 : A / Real.pi ≤ A / 3 := by
      rw [div_le_iff₀ hpi]; nlinarith only [hpi3, hA0.le]
    have h2 : A / (2 * Real.pi) ≤ A / 6 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]; nlinarith only [hpi3, hA0.le]
    have h3 : A / Real.pi ^ 2 ≤ A / 9 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.pi ^ 2)]; nlinarith only [hpi2, hA0.le]
    linarith only [h1, h2, h3, le_of_lt hA0]
  -- assemble
  have hsplit : E / (Real.pi * N / (2 * ℓ))
      + G * (((Real.pi * N / (2 * ℓ)) * ℓ)⁻¹ + (R / ℓ) ^ 4
          + (((Real.pi * N / (2 * ℓ)) * ℓ) ^ 2)⁻¹)
      = E / (Real.pi * N / (2 * ℓ))
        + G * ((Real.pi * N / (2 * ℓ)) * ℓ)⁻¹ + G * (R / ℓ) ^ 4
        + G * (((Real.pi * N / (2 * ℓ)) * ℓ) ^ 2)⁻¹ := by ring
  rw [hsplit]
  linarith only [hT1, hT2, hT4, hGu, hfinal]

end Work.BoseBoxFock.PCFU
