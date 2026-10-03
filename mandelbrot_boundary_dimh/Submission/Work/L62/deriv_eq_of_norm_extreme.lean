import Mathlib

namespace Work.L62

/-- Auxiliary real-part bound: if `‖z - 1‖ ≤ 1/2` then `Re z` is at least the value that the
boundary tangency point of the disk `D(1, 1/2)` on the circle of radius `‖z‖` would have. -/
private lemma re_ge_of_norm_sub_one_le {z : ℂ} (h2 : ‖z - 1‖ ≤ 1 / 2) :
    z.re ≥ (‖z‖ ^ 2 + 3 / 4) / 2 := by
  have hsq : ‖z - 1‖ ^ 2 = ‖z‖ ^ 2 - 2 * z.re + 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_eq_norm_sq,
      Complex.normSq_one]
    simp only [map_one, mul_one]
    ring
  have h2sq : ‖z - 1‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg (z - 1)) h2 2
    simpa using this
  nlinarith [hsq, h2sq]

/-- The disk `D(1, 1/2)` meets the circle of radius `1/2` only at the point `1/2`. -/
private lemma eq_half_of_norm_eq_half {z : ℂ} (h1 : ‖z‖ = 1 / 2) (h2 : ‖z - 1‖ ≤ 1 / 2) :
    z = 1 / 2 := by
  have hkey : z.re ≥ (‖z‖ ^ 2 + 3 / 4) / 2 := re_ge_of_norm_sub_one_le h2
  have hre : z.re = 1 / 2 := by
    rw [h1] at hkey
    have hle := Complex.re_le_norm z
    rw [h1] at hle
    norm_num at hkey
    linarith
  have him : z.im = 0 := by
    have hns : Complex.normSq z = z.re * z.re + z.im * z.im := Complex.normSq_apply z
    rw [Complex.normSq_eq_norm_sq, h1] at hns
    nlinarith [hns, hre, sq_nonneg z.im]
  refine Complex.ext ?_ ?_
  · simpa using hre
  · simpa using him

/-- The disk `D(1, 1/2)` meets the circle of radius `3/2` only at the point `3/2`. -/
private lemma eq_three_halves_of_norm_eq {z : ℂ} (h1 : ‖z‖ = 3 / 2) (h2 : ‖z - 1‖ ≤ 1 / 2) :
    z = 3 / 2 := by
  have hkey : z.re ≥ (‖z‖ ^ 2 + 3 / 4) / 2 := re_ge_of_norm_sub_one_le h2
  have hre : z.re = 3 / 2 := by
    rw [h1] at hkey
    have hle := Complex.re_le_norm z
    rw [h1] at hle
    norm_num at hkey
    linarith
  have him : z.im = 0 := by
    have hns : Complex.normSq z = z.re * z.re + z.im * z.im := Complex.normSq_apply z
    rw [Complex.normSq_eq_norm_sq, h1] at hns
    nlinarith [hns, hre, sq_nonneg z.im]
  refine Complex.ext ?_ ?_
  · simpa using hre
  · simpa using him

/-- Maximum-modulus rigidity for the derivative of a holomorphic function: if `‖deriv L - 1‖ ≤ 1/2`
on the open preconnected `U`, then `‖deriv L‖` can attain the endpoint values `1/2` and `3/2` only
if `deriv L` is the corresponding constant on all of `U`. -/
theorem deriv_eq_of_norm_extreme {U : Set ℂ} {L : ℂ → ℂ}
    (hUo : IsOpen U) (hUpc : IsPreconnected U) (hLd : DifferentiableOn ℂ L U)
    (hb : ∀ v ∈ U, ‖deriv L v - 1‖ ≤ 1 / 2) :
    (∀ p ∈ U, ‖deriv L p‖ = 1 / 2 → ∀ v ∈ U, deriv L v = 1 / 2) ∧
    (∀ p ∈ U, ‖deriv L p‖ = 3 / 2 → ∀ v ∈ U, deriv L v = 3 / 2) := by
  -- `deriv L` is holomorphic on the open set `U`.
  have hLd' : DifferentiableOn ℂ (deriv L) U := hLd.deriv hUo
  -- The modulus of `deriv L` is bounded below by `1/2` throughout `U`.
  have key : ∀ w ∈ U, 1 / 2 ≤ ‖deriv L w‖ := by
    intro w hw
    have h2 : ‖(1 : ℂ)‖ ≤ ‖deriv L w‖ + ‖deriv L w - 1‖ := by
      calc ‖(1 : ℂ)‖ = ‖deriv L w - (deriv L w - 1)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖deriv L w‖ + ‖deriv L w - 1‖ := norm_sub_le _ _
    rw [norm_one] at h2
    linarith [hb w hw]
  constructor
  · -- Endpoint `1/2`: `‖deriv L‖` attains its minimum, so `1 / deriv L` attains its maximum.
    intro p hp hpn v hv
    have hne : ∀ w ∈ U, deriv L w ≠ 0 := by
      intro w hw hzero
      have := key w hw
      rw [hzero, norm_zero] at this
      norm_num at this
    have hmax : IsMaxOn (norm ∘ (deriv L)⁻¹) U p := by
      intro w hw
      show ‖(deriv L w)⁻¹‖ ≤ ‖(deriv L p)⁻¹‖
      rw [norm_inv, norm_inv, hpn]
      rw [inv_le_inv₀ (by linarith [key w hw]) (by norm_num : (0 : ℝ) < 1 / 2)]
      exact key w hw
    have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hUpc hUo (hLd'.inv hne) hp hmax
    have hv' := heq hv
    have hvv : deriv L v = deriv L p := inv_inj.mp hv'
    rw [hvv]
    exact eq_half_of_norm_eq_half hpn (hb p hp)
  · -- Endpoint `3/2`: `‖deriv L‖` attains its maximum, so `deriv L` is constant.
    intro p hp hpn v hv
    have hmax : IsMaxOn (norm ∘ deriv L) U p := by
      intro w hw
      show ‖deriv L w‖ ≤ ‖deriv L p‖
      rw [hpn]
      have h2 : ‖deriv L w‖ ≤ ‖deriv L w - 1‖ + ‖(1 : ℂ)‖ := by
        calc ‖deriv L w‖ = ‖(deriv L w - 1) + 1‖ := by rw [sub_add_cancel]
          _ ≤ ‖deriv L w - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      rw [norm_one] at h2
      linarith [hb w hw]
    have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hUpc hUo hLd' hp hmax
    rw [heq hv]
    exact eq_three_halves_of_norm_eq hpn (hb p hp)

end Work.L62
