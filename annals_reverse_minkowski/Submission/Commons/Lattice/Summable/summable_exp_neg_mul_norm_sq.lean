import Mathlib.Algebra.Module.ZLattice.Summable

namespace Commons.Lattice.Summable

noncomputable section

open Real
open Filter
open scoped BigOperators

/-- For `0 < k` and `0 < t`, the exponential `exp (-t)` is bounded by a
constant (depending only on `k`) times `t⁻¹ ^ k`.  This is the elementary fact
that the exponential decays faster than every power. -/
private lemma exp_neg_mul_inv_pow_le (k : ℕ) (hk : 0 < k) {t : ℝ} (ht : 0 < t) :
    Real.exp (-t) ≤ (k * Real.exp (-1)) ^ k * (t⁻¹) ^ k := by
  let B : ℝ := (k : ℝ) * Real.exp (-1)
  let a : ℝ := t * Real.exp (-(t / (k : ℝ)))
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have ha_nonneg : 0 ≤ a := by
    exact mul_nonneg ht.le (Real.exp_pos _).le
  have ha_le : a ≤ B := by
    have hm := Real.mul_exp_neg_le_exp_neg_one (t / (k : ℝ))
    have hk0 : 0 ≤ (k : ℝ) := by positivity
    calc
      a = (k : ℝ) * ((t / (k : ℝ)) * Real.exp (-(t / (k : ℝ)))) := by
        dsimp [a]
        field_simp [hkR]
      _ ≤ (k : ℝ) * Real.exp (-1) := mul_le_mul_of_nonneg_left hm hk0
  have hpow : a ^ k ≤ B ^ k := pow_le_pow_left₀ ha_nonneg ha_le k
  have hmain : t ^ k * Real.exp (-t) ≤ B ^ k := by
    calc
      t ^ k * Real.exp (-t) = (t * Real.exp (-(t / (k : ℝ)))) ^ k := by
        have h1 : Real.exp (-t) = Real.exp ((k : ℝ) * (-(t / (k : ℝ)))) := by
          congr 1
          field_simp [hkR]
        rw [h1]
        rw [Real.exp_nat_mul]
        rw [← mul_pow]
      _ = a ^ k := by rfl
      _ ≤ B ^ k := hpow
  have htpow : 0 < t ^ k := pow_pos ht k
  calc
    Real.exp (-t) = (t ^ k * Real.exp (-t)) * (t ^ k)⁻¹ := by
      field_simp [pow_pos ht k]
    _ ≤ B ^ k * (t ^ k)⁻¹ := mul_le_mul_of_nonneg_right hmain (inv_nonneg.mpr htpow.le)
    _ = B ^ k * (t⁻¹) ^ k := by rw [← inv_pow]

/-- For `0 < c`, `0 < k`, and `v ≠ 0`:
`exp (-c * ‖v‖²) ≤ ((k * exp(-1))^k * c⁻¹^k) * ‖v‖⁻¹^(2*k)`. -/
private lemma exp_neg_mul_sq_le_pow_inv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : ℝ} (hc : 0 < c) {k : ℕ} (hk : 0 < k) {v : E} (hv0 : v ≠ 0) :
    Real.exp (-c * ‖v‖ ^ 2) ≤
      ((k * Real.exp (-1)) ^ k * (c⁻¹) ^ k) * (‖v‖⁻¹) ^ (2 * k) := by
  have harg : -c * ‖v‖ ^ 2 = -(c * ‖v‖ ^ 2) := by ring
  rw [harg]
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hcsq : 0 < c * ‖v‖ ^ 2 := by positivity
  have hp := exp_neg_mul_inv_pow_le k hk hcsq
  have hprod : ((c * ‖v‖ ^ 2)⁻¹) ^ k = (c⁻¹) ^ k * (‖v‖⁻¹) ^ (2 * k) := by
    have hinv : (c * ‖v‖ ^ 2)⁻¹ = c⁻¹ * (‖v‖⁻¹) ^ 2 := by
      rw [mul_inv]
      congr 1
      rw [sq, mul_inv]
      ring
    rw [hinv, mul_pow]
    congr 1
    rw [← pow_mul]
  calc
    Real.exp (-(c * ‖v‖ ^ 2)) ≤ (k * Real.exp (-1)) ^ k * ((c * ‖v‖ ^ 2)⁻¹) ^ k := hp
    _ = ((k * Real.exp (-1)) ^ k * (c⁻¹) ^ k) * (‖v‖⁻¹) ^ (2 * k) := by
      rw [hprod]
      ring

/-- The Gaussian function `y ↦ exp (-c * ‖y‖²)` is summable over any discrete
`ℤ`-submodule of a finite-dimensional real normed space, for every `c > 0`. -/
lemma summable_exp_neg_mul_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L] {c : ℝ} (hc : 0 < c) :
    Summable fun y : L ↦ Real.exp (-c * ‖(y : E)‖ ^ 2) := by
  classical
  let k : ℕ := Module.finrank ℤ L + 1
  have hk : 0 < k := by omega
  let D : ℝ := (k * Real.exp (-1)) ^ k * (c⁻¹) ^ k
  let g : L → ℝ := fun y => D * (‖(y : E)‖⁻¹) ^ (2 * k)
  have hg_sum : Summable g := by
    dsimp [g]
    have hs : Summable (fun y : L => (‖(y : E)‖⁻¹) ^ (2 * k)) := by
      have hfin : Module.finrank ℤ L < 2 * k := by
        dsimp [k]
        omega
      simpa using (ZLattice.summable_norm_pow_inv L (2 * k) hfin)
    exact hs.mul_left D
  have hbd : ∀ᶠ y : L in Filter.cofinite, ‖Real.exp (-c * ‖(y : E)‖ ^ 2)‖ ≤ g y := by
    rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton (0 : L)).subset ?_
    intro y hy
    by_contra hy0
    have hv0 : (y : E) ≠ 0 := by
      intro hzy
      exact hy0 (Subtype.ext hzy)
    have hb : Real.exp (-c * ‖(y : E)‖ ^ 2) ≤
        ((k * Real.exp (-1)) ^ k * (c⁻¹) ^ k) * (‖(y : E)‖⁻¹) ^ (2 * k) :=
      exp_neg_mul_sq_le_pow_inv (E := E) hc hk hv0
    have hle : ‖Real.exp (-c * ‖(y : E)‖ ^ 2)‖ ≤ g y := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      simpa [g, D] using hb
    exact hy hle
  exact Summable.of_norm_bounded_eventually hg_sum hbd

end

end Commons.Lattice.Summable