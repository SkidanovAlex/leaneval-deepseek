import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Trigonometric

namespace Commons.NumberTheory.Linnik

/-! # Decay of the factor `F₂(x+z) = ((1 − e^{−K(x+z)}) / (x+z))²`

Heath-Brown (1992), §13, p. 81: with `F₂(z) = ((1 − e^{−Kz})/z)²` and `K > 0`,
`x > 0`, the function `z ↦ F₂(x+z)` tends uniformly to zero on the half-plane
`Re z ≥ 0`.  The numerator is bounded by `2` (because
`‖e^{−K(x+z)}‖ = exp(−K(x + Re z)) ≤ exp(−Kx) ≤ 1` on that half-plane), while
`‖x + z‖ ≥ ‖z‖ − x`, so for `‖z‖ ≥ 2x` we get
`‖F₂(x+z)‖ ≤ 16 / ‖z‖²`, which is `< ε` once `‖z‖` is large enough.
-/

/-- `‖(x : ℂ)‖ = x` for `0 ≤ x`. -/
private lemma norm_ofReal_nonneg (x : ℝ) (hx : 0 ≤ x) : ‖(x : ℂ)‖ = x := by
  simp [hx]

/-- `‖1 − e^{w}‖ ≤ 2` whenever `Re w ≤ 0`. -/
private lemma norm_one_sub_exp_le_two (w : ℂ) (hw : w.re ≤ 0) :
    ‖1 - Complex.exp w‖ ≤ 2 := by
  have hE : ‖Complex.exp w‖ ≤ 1 := by
    rw [Complex.norm_exp]
    exact (Real.exp_le_one_iff).2 hw
  calc
    ‖1 - Complex.exp w‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.exp w‖ := norm_sub_le 1 (Complex.exp w)
    _ = 1 + ‖Complex.exp w‖ := by simp
    _ ≤ 2 := by nlinarith

/-- `‖z‖ − x ≤ ‖(x : ℂ) + z‖` for real `x ≥ 0`. -/
private lemma norm_add_ofReal_ge (x : ℝ) (hx : 0 ≤ x) (z : ℂ) :
    ‖z‖ - x ≤ ‖(x : ℂ) + z‖ := by
  have htri : ‖z‖ ≤ ‖(x : ℂ) + z‖ + ‖(x : ℂ)‖ := by
    calc
      ‖z‖ = ‖((x : ℂ) + z) + (-(x : ℂ))‖ := by congr 1; ring
      _ ≤ ‖(x : ℂ) + z‖ + ‖-(x : ℂ)‖ := norm_add_le ((x : ℂ) + z) (-(x : ℂ))
      _ = ‖(x : ℂ) + z‖ + ‖(x : ℂ)‖ := by rw [norm_neg]
  have hxn : ‖(x : ℂ)‖ = x := norm_ofReal_nonneg x hx
  nlinarith

theorem tentF2_decay {K x : ℝ} (hK : 0 < K) (hx : 0 < x) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, 0 ≤ z.re → R ≤ ‖z‖ →
      ‖(((1 - Complex.exp (-((K : ℂ) * ((x : ℂ) + z)))) / ((x : ℂ) + z)) ^ 2)‖ < ε := by
  intro ε hε
  let R : ℝ := max (2 * x) (8 / Real.sqrt ε)
  refine ⟨R, ?_⟩
  intro z hzre hzR
  have hxnorm : ‖(x : ℂ)‖ = x := norm_ofReal_nonneg x (le_of_lt hx)
  -- lower bounds on ‖z‖ coming from `R ≤ ‖z‖`
  have hz2x : 2 * x ≤ ‖z‖ := le_trans (le_max_left (2 * x) (8 / Real.sqrt ε)) hzR
  have hz8 : 8 / Real.sqrt ε ≤ ‖z‖ := le_trans (le_max_right (2 * x) (8 / Real.sqrt ε)) hzR
  have hRpos : 0 < R := by
    dsimp [R]
    positivity
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le hRpos hzR
  -- the exponent `w = −K(x+z)` has non-positive real part
  let w : ℂ := -((K : ℂ) * ((x : ℂ) + z))
  have hwre : w.re ≤ 0 := by
    dsimp [w]
    have hxzre : 0 ≤ x + z.re := by linarith
    have hprod : 0 ≤ K * (x + z.re) := mul_nonneg (le_of_lt hK) hxzre
    simp
    linarith
  have hnum : ‖1 - Complex.exp w‖ ≤ 2 := norm_one_sub_exp_le_two w hwre
  -- denominator estimate: ‖x + z‖ ≥ ‖z‖ − x ≥ x > 0
  have hxz_ge : ‖z‖ - x ≤ ‖(x : ℂ) + z‖ := norm_add_ofReal_ge x (le_of_lt hx) z
  have hzminx_pos : 0 < ‖z‖ - x := by linarith
  have hxz_pos : 0 < ‖(x : ℂ) + z‖ := lt_of_lt_of_le hzminx_pos hxz_ge
  -- ratio bound
  have hratio : ‖(1 - Complex.exp w) / ((x : ℂ) + z)‖ ≤ 4 / ‖z‖ := by
    calc
      ‖(1 - Complex.exp w) / ((x : ℂ) + z)‖
          = ‖1 - Complex.exp w‖ / ‖(x : ℂ) + z‖ := by rw [norm_div]
      _ ≤ 2 / ‖(x : ℂ) + z‖ := by
          exact div_le_div_of_nonneg_right hnum (norm_nonneg _)
      _ ≤ 2 / (‖z‖ - x) := by
          rw [div_le_div_iff₀ hxz_pos hzminx_pos]
          nlinarith
      _ ≤ 4 / ‖z‖ := by
          rw [div_le_div_iff₀ hzminx_pos hzpos]
          nlinarith
  -- square it
  have hsq : ‖((1 - Complex.exp w) / ((x : ℂ) + z)) ^ 2‖ ≤ (4 / ‖z‖) ^ 2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hratio 2
  have hsq16 : ‖((1 - Complex.exp w) / ((x : ℂ) + z)) ^ 2‖ ≤ 16 / ‖z‖ ^ 2 := by
    calc
      ‖((1 - Complex.exp w) / ((x : ℂ) + z)) ^ 2‖ ≤ (4 / ‖z‖) ^ 2 := hsq
      _ = 16 / ‖z‖ ^ 2 := by
        rw [div_pow]
        norm_num
  -- final size: `‖z‖ ≥ 8 / √ε` gives `16 / ‖z‖² ≤ ε/4 < ε`
  have hsqεpos : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have h8 : 8 ≤ ‖z‖ * Real.sqrt ε := by
    have hm := mul_le_mul_of_nonneg_right hz8 (le_of_lt hsqεpos)
    rwa [div_mul_cancel₀ (8 : ℝ) (ne_of_gt hsqεpos)] at hm
  have h64 : 64 ≤ ε * ‖z‖ ^ 2 := by
    have hsq8 : 8 ^ 2 ≤ (‖z‖ * Real.sqrt ε) ^ 2 := by
      exact pow_le_pow_left₀ (by norm_num : 0 ≤ (8 : ℝ)) h8 2
    norm_num at hsq8
    have hsqz : (‖z‖ * Real.sqrt ε) ^ 2 = ‖z‖ ^ 2 * ε := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hε)]
    rwa [hsqz, mul_comm] at hsq8
  have hfin : 16 / ‖z‖ ^ 2 ≤ ε / 4 := by
    rw [div_le_iff₀ (sq_pos_of_pos hzpos)]
    nlinarith
  calc
    ‖(((1 - Complex.exp (-((K : ℂ) * ((x : ℂ) + z)))) / ((x : ℂ) + z)) ^ 2)‖
        ≤ 16 / ‖z‖ ^ 2 := by
          simpa [w] using hsq16
    _ ≤ ε / 4 := hfin
    _ < ε := by nlinarith

end Commons.NumberTheory.Linnik