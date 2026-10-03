/-
# Hölder's inequality for the normalized residue sum

This module proves `Work.KMTAreas.A7.residueSum_mul_le`, the sub-conjugate Hölder inequality for
the uniform probability measure on `Finset.range q`:

  `(q)⁻¹ ∑_{n<q} u n * v n ≤ ((q)⁻¹ ∑_{n<q} u n ^ p₁) ^ (1/p₁)
                              * ((q)⁻¹ ∑_{n<q} v n ^ p₂) ^ (1/p₂)`

for exponents `p₁, p₂ > 1` with `p₁⁻¹ + p₂⁻¹ ≤ 1` and arbitrary `u v : ℕ → ℝ≥0∞`.

## The mathematics

Write `⟨f⟩ = q⁻¹ ∑_{n<q} f n` for the average over `n < q` (the counting measure on `range q`,
normalized to a probability measure).  The proof is the classical two-step reduction of the
sub-conjugate case to the conjugate one.

* With `r := conjExponent p₁ = p₁/(p₁-1)` the conjugate exponent of `p₁`, the hypothesis
  `p₁⁻¹ + p₂⁻¹ ≤ 1` gives `r ≤ p₂`.
* **Conjugate Hölder** (`ENNReal.inner_le_Lp_mul_Lq`): `S ≤ A^(1/p₁) · C^(1/r)`, where
  `S = ∑ u v`, `A = ∑ u^{p₁}` and `C = ∑ v^r`.
* **Monotonicity of the `ℓ^s` sums** (`ENNReal.rpow_sum_le_const_mul_sum_rpow`, the `s ≥ 1`
  case of `∑ f ≤ q^{1-1/s} (∑ f^s)^{1/s}` applied to `f = v^r` and `s = p₂/r ≥ 1`):
  `C^(1/r) ≤ q^{1/r - 1/p₂} · B^(1/p₂)` with `B = ∑ v^{p₂}`.
* Multiplying by `q⁻¹` and using `1/r = 1 - 1/p₁` gives exactly the claim, because
  `-1 + (1/r - 1/p₂) = -(1/p₁ + 1/p₂)`.

The single boundary case `p₁⁻¹ + p₂⁻¹ = 1` (so `p₂ = r`, `t = 1`) is covered by the same
argument: the monotonicity step is then an equality.
-/
import Mathlib

namespace Work.KMTAreas.A7

open scoped ENNReal BigOperators

theorem residueSum_mul_le (q : ℕ) (p₁ p₂ : ℝ) (hp₁ : 1 < p₁) (hp₂ : 1 < p₂)
    (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) (u v : ℕ → ENNReal) :
    (q : ENNReal)⁻¹ * ∑ n ∈ Finset.range q, u n * v n
      ≤ ((q : ENNReal)⁻¹ * ∑ n ∈ Finset.range q, u n ^ p₁) ^ (1 / p₁)
        * ((q : ENNReal)⁻¹ * ∑ n ∈ Finset.range q, v n ^ p₂) ^ (1 / p₂) := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    simp
  have hq0 : (q : ENNReal) ≠ 0 := by exact_mod_cast hq.ne'
  have hqtop : (q : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hp2pos : 0 < p₂ := by linarith
  -- `r` is the Hölder conjugate exponent of `p₁`, hence `r ≤ p₂`.
  set r : ℝ := p₁.conjExponent with hrdef
  have hconj : p₁.HolderConjugate r := Real.HolderConjugate.conjExponent hp₁
  have hrpos : 0 < r := by
    have := (Real.holderConjugate_iff.mp hconj.symm).1
    linarith
  have hr_inv : r⁻¹ = 1 - p₁⁻¹ := by
    have := (Real.holderConjugate_iff.mp hconj).2
    linarith
  have hp2_le_r : r ≤ p₂ := by
    have hle : p₂⁻¹ ≤ r⁻¹ := by rw [hr_inv]; linarith
    exact (inv_le_inv₀ hp2pos hrpos).mp hle
  -- The three sums and the average.
  set A : ENNReal := ∑ n ∈ Finset.range q, u n ^ p₁ with hA
  set B : ENNReal := ∑ n ∈ Finset.range q, v n ^ p₂ with hB
  set C : ENNReal := ∑ n ∈ Finset.range q, v n ^ r with hC
  set S : ENNReal := ∑ n ∈ Finset.range q, u n * v n with hS
  -- Step 1: conjugate Hölder for the pair `(p₁, r)`.
  have hH : S ≤ A ^ (1/p₁) * C ^ (1/r) := by
    rw [hS, hA, hC]
    exact ENNReal.inner_le_Lp_mul_Lq (Finset.range q) u v hconj
  -- Step 2: monotonicity of the `ℓ^s` sums, with `t = p₂ / r ≥ 1`.
  set t : ℝ := p₂ / r with htdef
  have ht1 : 1 ≤ t := by rw [htdef, one_le_div hrpos]; exact hp2_le_r
  have htr : t * r = p₂ := by rw [htdef]; field_simp
  have htr' : r * t = p₂ := by rw [mul_comm, htr]
  have hJ := ENNReal.rpow_sum_le_const_mul_sum_rpow (Finset.range q) (fun n => v n ^ r) ht1
  rw [Finset.card_range] at hJ
  have hsum_pow : (∑ n ∈ Finset.range q, (v n ^ r) ^ t) = B := by
    rw [hB]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← ENNReal.rpow_mul, htr']
  have hC_le : C ≤ (q : ENNReal) ^ (1 - 1/t) * B ^ (1/t) := by
    have h1 := ENNReal.rpow_le_rpow hJ (by positivity : (0:ℝ) ≤ 1/t)
    have e1 : t * (1/t) = 1 := by field_simp
    have e2 : (t-1) * (1/t) = 1 - 1/t := by field_simp
    rw [hsum_pow, ← ENNReal.rpow_mul, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
        ← ENNReal.rpow_mul, e1, e2, ENNReal.rpow_one] at h1
    exact h1
  have he1 : (1 - 1/t) * (1/r) = 1/r - 1/p₂ := by
    rw [sub_mul, one_mul, one_div_mul_one_div, htr]
  have he2 : (1/t) * (1/r) = 1/p₂ := by
    rw [one_div_mul_one_div, htr]
  have hC_le2 : C ^ (1/r) ≤ (q : ENNReal) ^ (1/r - 1/p₂) * B ^ (1/p₂) := by
    have h1 := ENNReal.rpow_le_rpow hC_le (by positivity : (0:ℝ) ≤ 1/r)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
        ← ENNReal.rpow_mul, he1, he2] at h1
    exact h1
  have hkey : S ≤ (q : ENNReal) ^ (1/r - 1/p₂) * A ^ (1/p₁) * B ^ (1/p₂) := by
    calc S ≤ A ^ (1/p₁) * C ^ (1/r) := hH
      _ ≤ A ^ (1/p₁) * ((q : ENNReal) ^ (1/r - 1/p₂) * B ^ (1/p₂)) :=
            mul_le_mul' le_rfl hC_le2
      _ = (q : ENNReal) ^ (1/r - 1/p₂) * A ^ (1/p₁) * B ^ (1/p₂) := by ring
  have hexp : -1 + (1/r - 1/p₂) = -(1/p₁ + 1/p₂) := by
    rw [one_div, hr_inv]; ring
  -- Multiply by `q⁻¹` and identify the exponents.
  have hfin : (q : ENNReal)⁻¹ * S
      ≤ (q : ENNReal) ^ (-(1/p₁ + 1/p₂)) * A ^ (1/p₁) * B ^ (1/p₂) := by
    calc (q : ENNReal)⁻¹ * S
        ≤ (q : ENNReal)⁻¹ * ((q : ENNReal) ^ (1/r - 1/p₂) * A ^ (1/p₁) * B ^ (1/p₂)) :=
          mul_le_mul' le_rfl hkey
      _ = ((q : ENNReal)⁻¹ * (q : ENNReal) ^ (1/r - 1/p₂)) * A ^ (1/p₁) * B ^ (1/p₂) := by ring
      _ = (q : ENNReal) ^ (-(1/p₁ + 1/p₂)) * A ^ (1/p₁) * B ^ (1/p₂) := by
          rw [← ENNReal.rpow_neg_one, ← ENNReal.rpow_add _ _ hq0 hqtop, hexp]
  have hqa : (q : ENNReal)⁻¹ ^ (1/p₁) = q ^ (-(1/p₁)) := by
    rw [ENNReal.inv_rpow, ENNReal.rpow_neg]
  have hqb : (q : ENNReal)⁻¹ ^ (1/p₂) = q ^ (-(1/p₂)) := by
    rw [ENNReal.inv_rpow, ENNReal.rpow_neg]
  have hprod : (q : ENNReal) ^ (-(1/p₁)) * q ^ (-(1/p₂)) = q ^ (-(1/p₁ + 1/p₂)) := by
    rw [← ENNReal.rpow_add _ _ hq0 hqtop]; ring_nf
  have htarget : ((q : ENNReal)⁻¹ * A) ^ (1/p₁) * ((q : ENNReal)⁻¹ * B) ^ (1/p₂)
      = (q : ENNReal) ^ (-(1/p₁ + 1/p₂)) * A ^ (1/p₁) * B ^ (1/p₂) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1/p₁),
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1/p₂),
        hqa, hqb, ← hprod]
    ring
  rw [htarget]
  exact hfin

end Work.KMTAreas.A7
