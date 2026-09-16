import Submission.ZagierHoffmanProof.GenSuperLSeries

/-!
# The two coefficient estimates for the depth-`r` evaluation of the `L`-series

The evaluation of the depth-`r` `L`-series at a point `θ` interchanges the coefficientwise sum
defining the series with the value sum.  The interchange is justified by the *joint* summability of
`(n,i) ↦ coeff n (A_i·B_i)·θ^n`, where `A_i = (ω^s Q)^{(N+i)}` and `B_i` is the truncated tail
`L`-series `atLrcutGen q ω L (N+i+1)`.  Two estimates are needed:

* (smallness) `v (coeff n (A_i B_i)) ≤ γ^(q^(N+i))·b`, because **all** coefficients of `A_i` are
  bounded by `γ^(q^(N+i))` (`ω^sQ` is small) and the coefficients of the tail `L`-series are
  bounded by `b`;
* (super-entireness) `v (coeff n (A_i B_i)) ≤ b·max a (γ·(γ^(M(J-1)))⁻¹)·(γ^M)^n`: either `j ≥ J`,
  where `j` is the index of the Cauchy sum for which `a γ^(Mj) ≤ γ ≤ 1` so that the `j`-th
  coefficient of `A_i` is bounded by `aγ^(Mj)` — the tail factor then contributes exactly the
  missing `γ^(M(n-j))` — or `j < J`, where the smallness bound `γ^(q^(N+i)) ≤ γ` is used and the
  loss is the constant `γ·(γ^(M(J-1)))⁻¹`.

## Main results

* `v_coeff_mul_le` — the coefficientwise Cauchy bound.
* ★★ `v_coeff_frobTwist_mul_le_small`.
* ★★ `v_coeff_frobTwist_mul_le_super`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Polynomial PowerSeries Finset
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

/-! ## §1. The coefficientwise Cauchy bound -/

/-- If the coefficient valuations of `f` and `g` are bounded by `c` and `d` and
`c p.1 * d p.2 ≤ B` on the antidiagonal of `n`, then `v (coeff n (f*g)) ≤ B`. -/
lemma v_coeff_mul_le (f g : PowerSeries K) {c d : ℕ → Γ₀} {n : ℕ} {B : Γ₀}
    (hf : ∀ j, Valued.v (PowerSeries.coeff j f) ≤ c j)
    (hg : ∀ k, Valued.v (PowerSeries.coeff k g) ≤ d k)
    (hB : ∀ p ∈ Finset.antidiagonal n, c p.1 * d p.2 ≤ B) :
    Valued.v (PowerSeries.coeff n (f * g)) ≤ B := by
  rw [PowerSeries.coeff_mul]
  refine Valuation.map_sum_le (Valued.v) (fun p hp => ?_)
  rw [Valuation.map_mul]
  exact le_trans (mul_le_mul' (hf p.1) (hg p.2)) (hB p hp)

/-! ## §2. The smallness bound -/

/-- **The smallness estimate**: if all coefficients of `F` are `≤ γ` and those of `B` are `≤ b`,
then every coefficient of `frobTwist d F * B` is `≤ γ^(q^d)·b`. -/
lemma v_coeff_frobTwist_mul_le_small {γ : Γ₀} {q : ℕ} [FrobPow K q] {F B : PowerSeries K}
    {b : Γ₀} (hF : ∀ j, Valued.v (PowerSeries.coeff j F) ≤ γ)
    (hB : ∀ k, Valued.v (PowerSeries.coeff k B) ≤ b) (d n : ℕ) :
    Valued.v (PowerSeries.coeff n (frobTwist (R := K) (p := q) d F * B))
      ≤ γ ^ (q ^ d) * b := by
  refine v_coeff_mul_le (c := fun _ => γ ^ (q ^ d)) (d := fun _ => b) _ _
    (fun j => ?_) (fun k => hB k) (fun p _ => le_refl _)
  · rw [frobTwist_coeff, map_pow]
    exact pow_le_pow_left₀ (zero_le) (hF j) _

/-! ## §3. The super-entireness bound -/

/-- The arithmetic core of the super-entireness estimate: for `s_j = min γ (a γ^(Mj))`,
`γ < 1`, `M ≥ 1` and `a γ^(MJ) ≤ γ`, the products `s_j^(q^d)·γ^(M k)` are bounded by
`max a (γ·(γ^(M(J-1)))⁻¹)·γ^(M(j+k))`. -/
lemma min_pow_mul_le {γ a : Γ₀} {M J q d j k : ℕ} (hγ : γ < 1) (hγ0 : γ ≠ 0) (hM1 : 1 ≤ M)
    (hq1 : 1 ≤ q) (hJ : a * γ ^ (M * J) ≤ γ) :
    (min γ (a * γ ^ (M * j))) ^ (q ^ d) * γ ^ (M * k)
      ≤ max a (γ * (γ ^ (M * (J - 1)))⁻¹) * γ ^ (M * (j + k)) := by
  have hγle : γ ≤ 1 := le_of_lt hγ
  have hq1' : 1 ≤ q ^ d := Nat.one_le_pow d q (by omega : 0 < q)
  have hγMJ : a * γ ^ (M * J) ≤ 1 := le_trans hJ hγle
  have hA : γ ^ (M * j) ≠ 0 := pow_ne_zero _ hγ0
  rcases lt_or_ge j J with hj | hj
  · -- `j < J`: use the smallness bound
    have hmin : min γ (a * γ ^ (M * j)) ≤ γ := min_le_left _ _
    have hpow : (min γ (a * γ ^ (M * j))) ^ (q ^ d) ≤ γ :=
      le_trans (pow_le_pow_of_le_one (zero_le) (le_trans hmin hγle) hq1')
        (by rw [pow_one]; exact hmin)
    have hle : γ ^ (M * (J - 1)) ≤ γ ^ (M * j) := by
      refine pow_le_pow_of_le_one (zero_le) hγle ?_
      exact Nat.mul_le_mul_left M (by omega)
    have hpos : 0 < γ ^ (M * (J - 1)) := pow_pos (lt_of_le_of_ne (zero_le) (Ne.symm hγ0)) _
    have hinv : (γ ^ (M * j))⁻¹ ≤ (γ ^ (M * (J - 1)))⁻¹ := inv_anti₀ hpos hle
    calc (min γ (a * γ ^ (M * j))) ^ (q ^ d) * γ ^ (M * k)
        ≤ γ * γ ^ (M * k) := mul_le_mul_of_nonneg_right hpow (zero_le)
      _ = (γ * (γ ^ (M * j))⁻¹) * (γ ^ (M * j) * γ ^ (M * k)) := by
            rw [mul_assoc, ← mul_assoc (γ ^ (M * j))⁻¹ (γ ^ (M * j)) (γ ^ (M * k)),
              inv_mul_cancel₀ hA, one_mul]
      _ = (γ * (γ ^ (M * j))⁻¹) * γ ^ (M * (j + k)) := by
            rw [Nat.mul_add, pow_add]
      _ ≤ (γ * (γ ^ (M * (J - 1)))⁻¹) * γ ^ (M * (j + k)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv (zero_le)) (zero_le)
      _ ≤ max a (γ * (γ ^ (M * (J - 1)))⁻¹) * γ ^ (M * (j + k)) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le)
  · -- `J ≤ j`: use the super-entireness bound
    have hMj : M * J ≤ M * j := Nat.mul_le_mul_left M hj
    have hge : γ ^ (M * j) ≤ γ ^ (M * J) := pow_le_pow_of_le_one (zero_le) hγle hMj
    have haj : a * γ ^ (M * j) ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hge (zero_le)) hγMJ
    have hpow : (min γ (a * γ ^ (M * j))) ^ (q ^ d) ≤ a * γ ^ (M * j) := by
      refine le_trans (pow_le_pow_of_le_one (zero_le) (le_trans (min_le_right _ _) haj) hq1') ?_
      rw [pow_one]
      exact min_le_right _ _
    calc (min γ (a * γ ^ (M * j))) ^ (q ^ d) * γ ^ (M * k)
        ≤ (a * γ ^ (M * j)) * γ ^ (M * k) := mul_le_mul_of_nonneg_right hpow (zero_le)
      _ = a * γ ^ (M * (j + k)) := by rw [mul_assoc, ← pow_add, ← Nat.mul_add]
      _ ≤ max a (γ * (γ ^ (M * (J - 1)))⁻¹) * γ ^ (M * (j + k)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le)

/-- **The super-entireness estimate**: if `v (coeff j F) ≤ min γ (a γ^(Mj))`, `1 ≤ M`, `a γ^(MJ) ≤ γ`
and `v (coeff k B) ≤ b γ^(Mk)`, then every coefficient of `frobTwist d F * B` is bounded by
`b·max a (γ(γ^(M(J-1)))⁻¹)·(γ^M)^n`. -/
lemma v_coeff_frobTwist_mul_le_super {γ a b : Γ₀} {q M J : ℕ} [FrobPow K q] {F B : PowerSeries K}
    (hγ : γ < 1) (hγ0 : γ ≠ 0) (hq1 : 1 ≤ q) (hM1 : 1 ≤ M)
    (hF : ∀ j, Valued.v (PowerSeries.coeff j F) ≤ min γ (a * γ ^ (M * j)))
    (hB : ∀ k, Valued.v (PowerSeries.coeff k B) ≤ b * γ ^ (M * k))
    (hJ : a * γ ^ (M * J) ≤ γ) (d n : ℕ) :
    Valued.v (PowerSeries.coeff n (frobTwist (R := K) (p := q) d F * B))
      ≤ b * max a (γ * (γ ^ (M * (J - 1)))⁻¹) * (γ ^ M) ^ n := by
  have hpow : γ ^ (M * n) = (γ ^ M) ^ n := by rw [← pow_mul]
  refine v_coeff_mul_le
    (c := fun j => min γ (a * γ ^ (M * j)) ^ (q ^ d))
    (d := fun k => b * γ ^ (M * k)) _ _ (fun j => ?_) (fun k => hB k) (fun p hp => ?_)
  · rw [frobTwist_coeff, map_pow]
    exact pow_le_pow_left₀ (zero_le) (hF j) _
  · obtain hsum : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
    subst hsum
    have h1 : γ ^ (M * (p.1 + p.2)) = (γ ^ M) ^ (p.1 + p.2) := by rw [← pow_mul]
    calc min γ (a * γ ^ (M * p.1)) ^ (q ^ d) * (b * γ ^ (M * p.2))
        = b * (min γ (a * γ ^ (M * p.1)) ^ (q ^ d) * γ ^ (M * p.2)) := by
            rw [← mul_assoc, mul_comm (min γ (a * γ ^ (M * p.1)) ^ (q ^ d)) b, mul_assoc]
      _ ≤ b * (max a (γ * (γ ^ (M * (J - 1)))⁻¹) * γ ^ (M * (p.1 + p.2))) :=
            mul_le_mul_of_nonneg_left (min_pow_mul_le hγ hγ0 hM1 hq1 hJ) (zero_le)
      _ = b * max a (γ * (γ ^ (M * (J - 1)))⁻¹) * (γ ^ M) ^ (p.1 + p.2) := by
            rw [h1, mul_assoc]

end ZagierHoffmanPositiveChar
