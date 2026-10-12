import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB7AK.K15R

/-- `(2^n)⁻¹ = (1/2)^n` on the reals. -/
private lemma inv_two_pow (n : ℕ) : ((2:ℝ)^n)⁻¹ = (1/2:ℝ)^n := by
  rw [← inv_pow, one_div]

/--
Pointwise bound for a single annulus term: writing `x = 2^k · R ≥ 1`, one has
`2^{k+1} R / π + 1 ≤ 2x + 1 ≤ 3x`, hence the cube is at most `27 x^3`; multiplying by
`x^{-2s}` and using `x^{2s} = x^{2s-3} · x^3` (with `s ≥ 2`) yields the stated bound.
-/
private lemma term_bound (s k : ℕ) (R : ℝ) (hR : 1 ≤ R) (hs : 2 ≤ s) :
    (((2:ℝ)^(k+1) * R / Real.pi + 1) ^ 3) * ((((2:ℝ)^k * R) ^ 2) ^ s)⁻¹
      ≤ 27 * ((1/2:ℝ)^(2*s-3))^k / R^(2*s-3) := by
  set x : ℝ := (2:ℝ)^k * R with hxdef
  have hx1 : 1 ≤ x := by
    rw [hxdef]
    have h1 : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
    nlinarith [h1, hR]
  have hs3 : 3 ≤ 2*s := by omega
  have h2 : (2:ℝ)^(k+1) * R = 2 * x := by rw [hxdef, pow_succ]; ring
  rw [h2]
  have hA : 2 * x / Real.pi + 1 ≤ 3 * x := by
    have hpi : (1:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have h1 : 2 * x / Real.pi ≤ 2 * x := by
      rw [div_le_iff₀ Real.pi_pos]
      nlinarith [hx1, hpi]
    linarith
  have hA0 : 0 ≤ 2 * x / Real.pi + 1 := by positivity
  have hcube : (2 * x / Real.pi + 1)^3 ≤ (3*x)^3 := pow_le_pow_left₀ hA0 hA 3
  have hinv0 : 0 ≤ ((x^2)^s)⁻¹ := by positivity
  have hkey : x^3 * (x^(2*s))⁻¹ = (x^(2*s-3))⁻¹ := by
    have h : x^(2*s) = x^(2*s-3) * x^3 := by rw [← pow_add, Nat.sub_add_cancel hs3]
    rw [h, mul_inv]
    field_simp
  have hR3 : (3*x)^3 * ((x^2)^s)⁻¹ = 27 / x^(2*s-3) := by
    rw [← pow_mul x 2 s, div_eq_mul_inv]
    rw [show (3*x)^3 = 27 * x^3 by ring]
    rw [mul_assoc, hkey]
  have hRx : 27 / x^(2*s-3) = 27 * ((1/2:ℝ)^(2*s-3))^k / R^(2*s-3) := by
    rw [hxdef]
    rw [show ((2:ℝ)^k * R)^(2*s-3) = ((2:ℝ)^(2*s-3))^k * R^(2*s-3) by
      rw [mul_pow, ← pow_mul, mul_comm k (2*s-3), pow_mul]]
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, ← inv_pow, inv_two_pow]
    ring
  calc (2 * x / Real.pi + 1)^3 * ((x^2)^s)⁻¹
      ≤ (3*x)^3 * ((x^2)^s)⁻¹ := mul_le_mul_of_nonneg_right hcube hinv0
    _ = 27 / x^(2*s-3) := hR3
    _ = 27 * ((1/2:ℝ)^(2*s-3))^k / R^(2*s-3) := hRx

/-- The geometric sum `∑_{k<K} q^k ≤ 2` for `0 ≤ q ≤ 1/2`, proved by induction via the
sharper estimate `∑_{k<n} q^k ≤ 2 (1 - q^n)`. -/
private lemma geom_sum_le_two (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1/2) (K : ℕ) :
    ∑ k ∈ Finset.range K, q ^ k ≤ 2 := by
  have h : ∀ n, ∑ k ∈ Finset.range n, q ^ k ≤ 2 * (1 - q ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hqn : 0 ≤ q ^ n := pow_nonneg h0 n
      have h2q : 2 * q ≤ 1 := by linarith
      have hqq : 2 * q * q ^ n ≤ q ^ n := by nlinarith [hqn, h2q]
      linarith
  have hK := h K
  have : 0 ≤ q ^ K := pow_nonneg h0 K
  linarith

theorem annulus_terms_sum_bound (s K : ℕ) (R : ℝ) (hR : 1 ≤ R) (hs : 2 ≤ s) :
    (∑ k ∈ Finset.range K,
        (((2:ℝ)^(k+1) * R / Real.pi + 1) ^ 3) * ((((2:ℝ)^k * R) ^ 2) ^ s)⁻¹)
      ≤ 128 / R ^ (2 * s - 3) := by
  have hq0 : 0 ≤ (1/2:ℝ)^(2*s-3) := by positivity
  have hq1 : (1/2:ℝ)^(2*s-3) ≤ 1/2 := by
    have h1 : (1:ℕ) ≤ 2*s-3 := by omega
    calc (1/2:ℝ)^(2*s-3) ≤ (1/2:ℝ)^1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) h1
      _ = 1/2 := by norm_num
  have hgeo := geom_sum_le_two ((1/2:ℝ)^(2*s-3)) hq0 hq1 K
  have hRp : 0 < R^(2*s-3) := pow_pos (by linarith) _
  calc ∑ k ∈ Finset.range K,
          (((2:ℝ)^(k+1) * R / Real.pi + 1) ^ 3) * ((((2:ℝ)^k * R) ^ 2) ^ s)⁻¹
      ≤ ∑ k ∈ Finset.range K, 27 * ((1/2:ℝ)^(2*s-3))^k / R^(2*s-3) :=
          Finset.sum_le_sum (fun k _ => term_bound s k R hR hs)
    _ = (27 / R^(2*s-3)) * ∑ k ∈ Finset.range K, ((1/2:ℝ)^(2*s-3))^k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ ≤ (27 / R^(2*s-3)) * 2 := by
          apply mul_le_mul_of_nonneg_left hgeo
          positivity
    _ = 54 / R^(2*s-3) := by ring
    _ ≤ 128 / R^(2*s-3) := by
          apply div_le_div_of_nonneg_right (by norm_num : (54:ℝ) ≤ 128) (le_of_lt hRp)

end Work.BoseB7AK.K15R
