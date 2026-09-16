import Mathlib

namespace Commons.Topology.Algebra.Valued

open Polynomial

/-- Auxiliary arithmetic identity in a commutative group with zero: if `i + j = n` and `r ≠ 0`,
then `(r^j)⁻¹ = r^i * (r^n)⁻¹`. Equivalently `r^i * (r^n)⁻¹ = (r^j)⁻¹`, i.e. the weight `r^i`
"completes" the reciprocal of `r^j` into the reciprocal of `r^n`. -/
lemma inv_pow_eq_mul_inv_pow {Γ₀ : Type*} [CommGroupWithZero Γ₀] {r : Γ₀}
    (hr : r ≠ 0) {i j n : ℕ} (h : i + j = n) :
    (r ^ j)⁻¹ = r ^ i * (r ^ n)⁻¹ := by
  subst h
  rw [pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero i hr), one_mul]

/-- Gauss-type coefficient bound for products of a polynomial with a power series, uniformly in a
finite family. If `1 ≤ r`, each polynomial `p i` has degree at most `d`, the coefficients of the
`p i` are bounded by `C`, and the coefficients of the `g i` satisfy the weighted bound
`v (g i).coeff n * r^n ≤ A`, then the `n`-th coefficient of `∑ i, p i * g i` satisfies
`v (…) * r^n ≤ C * r^d * A`.

The proof uses the ultrametric (non-archimedean) inequality `v (∑ tₓ) ≤ maxₓ v tₓ` in the form
`Valuation.map_sum_le`, together with the expansion of the coefficient of a product as the
antidiagonal sum. Since `r ≥ 1`, the extra weight `r^(x₁)` for a term of bidegree `(x₁, x₂)` with
`x₁ + x₂ = n` is at most `r^d`, and terms with `x₁ > d` simply vanish because of the degree bound. -/
theorem gauss_coeff_sum_mul_polynomial {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] {ι : Type*} [Fintype ι] {r C A : Γ₀}
    (hr : 1 ≤ r) {p : ι → Polynomial K} {g : ι → PowerSeries K} {d : ℕ}
    (hdeg : ∀ i, (p i).natDegree ≤ d) (hp : ∀ i e, Valued.v ((p i).coeff e) ≤ C)
    (hg : ∀ i n, Valued.v (PowerSeries.coeff n (g i)) * r ^ n ≤ A) :
    ∀ n, Valued.v (PowerSeries.coeff n (∑ i, ((p i : Polynomial K) : PowerSeries K) * g i))
      * r ^ n ≤ C * r ^ d * A := by
  intro n
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hr0 : r ≠ 0 := ne_of_gt hrpos
  have hrn : r ^ n ≠ 0 := ne_of_gt (pow_pos hrpos n)
  -- The single bound `B = C * r^d * A * (r^n)⁻¹` which, after multiplication by `r^n`, gives the
  -- desired right-hand side `C * r^d * A`.
  set B : Γ₀ := C * r ^ d * A * (r ^ n)⁻¹ with hB
  -- Bound on the `n`-th coefficient of each individual product `p i * g i`.
  have hinner : ∀ i, Valued.v (PowerSeries.coeff n (((p i : Polynomial K) : PowerSeries K) * g i)) ≤ B := by
    intro i
    rw [PowerSeries.coeff_mul]
    refine Valuation.map_sum_le Valued.v ?_
    intro x hx
    have hx' : x.1 + x.2 = n := by
      simpa using hx
    rw [show (PowerSeries.coeff x.1) ((p i : Polynomial K) : PowerSeries K) = (p i).coeff x.1 from
      Polynomial.coeff_coe (p i) x.1]
    rw [Valuation.map_mul]
    by_cases hxd : x.1 ≤ d
    · -- Non-vanishing degree case: use both coefficient bounds.
      have hgx : Valued.v (PowerSeries.coeff x.2 (g i)) ≤ A * (r ^ x.2)⁻¹ := by
        have h := mul_le_mul_of_nonneg_right (hg i x.2) (zero_le : (0 : Γ₀) ≤ (r ^ x.2)⁻¹)
        rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos hrpos x.2)), mul_one] at h
      have hstep : Valued.v ((p i).coeff x.1) * Valued.v (PowerSeries.coeff x.2 (g i)) ≤
          C * (A * (r ^ x.2)⁻¹) :=
        mul_le_mul (hp i x.1) hgx zero_le zero_le
      have hpow : r ^ x.1 ≤ r ^ d := pow_le_pow_right₀ hr hxd
      calc Valued.v ((p i).coeff x.1) * Valued.v (PowerSeries.coeff x.2 (g i))
          ≤ C * (A * (r ^ x.2)⁻¹) := hstep
        _ = C * A * r ^ x.1 * (r ^ n)⁻¹ := by
              rw [inv_pow_eq_mul_inv_pow hr0 hx']; ac_rfl
        _ ≤ C * A * r ^ d * (r ^ n)⁻¹ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpow (zero_le : (0 : Γ₀) ≤ C * A)) zero_le
        _ = B := by rw [hB]; ac_rfl
    · -- Vanishing case: the polynomial coefficient at `x.1 > d` is zero.
      have hzero : (p i).coeff x.1 = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg i) (not_le.mp hxd))
      rw [hzero, Valuation.map_zero, zero_mul]
      exact zero_le
  -- Bound on the `n`-th coefficient of the whole sum, by the non-archimedean inequality.
  have houter : Valued.v (PowerSeries.coeff n (∑ i, ((p i : Polynomial K) : PowerSeries K) * g i)) ≤ B := by
    rw [map_sum]
    exact Valuation.map_sum_le Valued.v (fun i _ => hinner i)
  -- Multiply through by `r^n` and cancel the reciprocal.
  calc Valued.v (PowerSeries.coeff n (∑ i, ((p i : Polynomial K) : PowerSeries K) * g i)) * r ^ n
      ≤ B * r ^ n := mul_le_mul_left houter (r ^ n)
    _ = C * r ^ d * A := by
        rw [hB]
        calc C * r ^ d * A * (r ^ n)⁻¹ * r ^ n = C * r ^ d * A * ((r ^ n)⁻¹ * r ^ n) := by ac_rfl
          _ = C * r ^ d * A * 1 := by rw [inv_mul_cancel₀ hrn]
          _ = C * r ^ d * A := by rw [mul_one]

end Commons.Topology.Algebra.Valued
