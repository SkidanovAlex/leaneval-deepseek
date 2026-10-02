import Mathlib
import Submission.Commons.Analysis.Real.log_pow_le_mul_rpow

open MeasureTheory
open scoped Real Topology

set_option autoImplicit false

namespace Commons.NumberTheory.Linnik

/-- **Absorption of the far-zero error term (HB (6.14)).**  For every `ε > 0` and constants
`K, C ≥ 0`, `δ > 0`, `x₀ > 0` there is `L₀ ≥ 1` such that for all `L ≥ L₀`

`K / ((δ/2)L) + C e^{x₀ loglog L / 3} / ((δ/2)L)² ≤ ε`.

This is the numerical step that turns the two-sided decay `laplace_far_le` into the `O(L⁻¹)`
slack of Heath-Brown's (6.14). -/
theorem far_absorb {x₀ δ K C ε : ℝ} (hx₀ : 0 < x₀) (hδ : 0 < δ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hε : 0 < ε) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      K / (δ / 2 * L) + C * Real.exp (x₀ * (Real.log (Real.log L) / 3)) / (δ / 2 * L) ^ 2
        ≤ ε := by
  set A : ℕ := ⌈x₀ / 3⌉₊ with hAdef
  have hAle : x₀ / 3 ≤ (A : ℝ) := Nat.le_ceil _
  obtain ⟨C₁, hC₁pos, hC₁⟩ :=
    Commons.Analysis.Real.log_pow_le_mul_rpow (ε := (1:ℝ)/2) (by norm_num) A
  have hC₁nn : 0 ≤ C₁ := hC₁pos.le
  refine ⟨max (Real.exp 1) (max (4 * K / (δ * ε) + 1) ((8 * C * C₁ / (δ^2 * ε))^2 + 1)), ?_, ?_⟩
  · have h1 : (1:ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : (0:ℝ) ≤ 4 * K / (δ * ε) + 1 := by positivity
    have h3 : (0:ℝ) ≤ (8 * C * C₁ / (δ^2 * ε))^2 + 1 := by positivity
    have h4 : (1:ℝ) ≤ (8 * C * C₁ / (δ^2 * ε))^2 + 1 := by
      have := sq_nonneg (8 * C * C₁ / (δ^2 * ε)); linarith only [this]
    linarith only [le_max_left (Real.exp 1) (max (4 * K / (δ * ε) + 1) ((8 * C * C₁ / (δ^2 * ε))^2 + 1)),
      le_max_right (Real.exp 1) (max (4 * K / (δ * ε) + 1) ((8 * C * C₁ / (δ^2 * ε))^2 + 1)),
      le_max_left (4 * K / (δ * ε) + 1) ((8 * C * C₁ / (δ^2 * ε))^2 + 1),
      le_max_right (4 * K / (δ * ε) + 1) ((8 * C * C₁ / (δ^2 * ε))^2 + 1), h1]
  · intro L hL
    have hLexp : Real.exp 1 ≤ L := le_trans (le_max_left _ _) hL
    have hLK : 4 * K / (δ * ε) + 1 ≤ L :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hL)
    have hLC : (8 * C * C₁ / (δ^2 * ε))^2 + 1 ≤ L :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hL)
    have hL1 : 1 ≤ L := by
      have := Real.one_le_exp (show (0:ℝ) ≤ 1 by norm_num)
      linarith only [hLexp, this]
    have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
    have hlogL1 : 1 ≤ Real.log L := by
      calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log L := Real.log_le_log (Real.exp_pos 1) hLexp
    have hlogLpos : 0 < Real.log L := lt_of_lt_of_le one_pos hlogL1
    have hsqrt1 : 1 ≤ Real.sqrt L := Real.one_le_sqrt.mpr hL1
    -- the `exp`/`rpow` bridge and the `(log L)^A` bound
    have hexp_eq : Real.exp (x₀ * (Real.log (Real.log L) / 3)) = (Real.log L) ^ (x₀ / 3) := by
      rw [Real.rpow_def_of_pos hlogLpos]
      congr 1
      ring
    have hpow : Real.exp (x₀ * (Real.log (Real.log L) / 3)) ≤ C₁ * Real.sqrt L := by
      rw [hexp_eq]
      calc (Real.log L) ^ (x₀ / 3) ≤ (Real.log L) ^ (A : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hlogL1 hAle
        _ = (Real.log L) ^ A := Real.rpow_natCast _ _
        _ ≤ C₁ * L ^ ((1:ℝ)/2) := hC₁ L hL1
        _ = C₁ * Real.sqrt L := by rw [Real.sqrt_eq_rpow]
    -- the first term
    have hterm1 : K / (δ / 2 * L) ≤ ε / 2 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < δ / 2 * L)]
      have h4 : 4 * K / (δ * ε) ≤ L := by linarith only [hLK]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < δ * ε)] at h4
      linarith only [h4, hε.le, hδ.le, hLpos.le]
    -- the second term
    have hterm2 : C * Real.exp (x₀ * (Real.log (Real.log L) / 3)) / (δ / 2 * L) ^ 2 ≤ ε / 2 := by
      have hnum : C * Real.exp (x₀ * (Real.log (Real.log L) / 3)) ≤ C * (C₁ * Real.sqrt L) :=
        mul_le_mul_of_nonneg_left hpow hC
      have hden : (0:ℝ) < (δ / 2 * L) ^ 2 := by positivity
      have h1 : C * Real.exp (x₀ * (Real.log (Real.log L) / 3)) / (δ / 2 * L) ^ 2
          ≤ (C * (C₁ * Real.sqrt L)) / (δ / 2 * L) ^ 2 :=
        div_le_div_of_nonneg_right hnum hden.le
      have h2 : (C * (C₁ * Real.sqrt L)) / (δ / 2 * L) ^ 2
          = 4 * C * C₁ / (δ^2 * L * Real.sqrt L) := by
        have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLpos.le
        have h1 : (δ / 2 * L) ^ 2 ≠ 0 := by positivity
        have h2' : δ^2 * L * Real.sqrt L ≠ 0 := by positivity
        rw [div_eq_div_iff h1 h2']
        linear_combination (C * C₁ * δ^2 * L) * hsq
      have h3 : 4 * C * C₁ / (δ^2 * L * Real.sqrt L) ≤ 4 * C * C₁ / (δ^2 * L) := by
        have hpos : 0 < δ^2 * L := by positivity
        have hle : δ^2 * L ≤ δ^2 * L * Real.sqrt L := by nlinarith only [hsqrt1, hpos, hLC]
        exact div_le_div_of_nonneg_left (by positivity) hpos hle
      have h4 : 4 * C * C₁ / (δ^2 * L) ≤ ε / 2 := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < δ^2 * L)]
        have hLC' : 8 * C * C₁ / (δ^2 * ε) ≤ L := by
          have hc := hLC
          have hs := sq_nonneg (8 * C * C₁ / (δ^2 * ε) - 1)
          nlinarith only [hc, hs, hLC]
        rw [div_le_iff₀ (by positivity : (0:ℝ) < δ^2 * ε)] at hLC'
        linarith only [hLC']
      linarith only [h1, h2, h3, h4]
    linarith only [hterm1, hterm2]

end Commons.NumberTheory.Linnik
