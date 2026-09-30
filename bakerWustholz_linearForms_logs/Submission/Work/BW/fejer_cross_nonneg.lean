import Mathlib
import Submission.Work.BW.logMomentAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Nonnegativity of the Fejér cross term

For nonnegative summable coefficients `c`, `d` and arbitrary real frequencies `α`, `β`, the
Fejér-weighted cross correlation of the cosine series is bounded below by `-(1/2) (∑ c)(∑ d)`:

`∑_{k=1}^{K} w_k · (∑_m c_m cos(k α_m)) · (∑_m d_m cos(k β_m)) + (1/2) (∑ c)(∑ d) ≥ 0`,

where `w_k = 1 - k/(K+1)` are the Fejér weights (`lmW`).

The proof expands both cosine series into the double sum over `(m,n) : ℕ × ℕ` via
`Summable.tsum_mul_tsum`, brings the (finite) `k`-sum inside with `Summable.tsum_finsetSum`, and
concludes with the pointwise Fejér-positivity bound `∑_k w_k cos(kx) cos(ky) + 1/2 ≥ 0`
(`Work.BW.fejer_pair_nonneg`) against the nonnegative weights `c_m d_n`.
-/

open scoped BigOperators
open Finset

namespace Work.BW

theorem fejer_cross_nonneg (K : ℕ) (c d : ℕ → ℝ) (α β : ℕ → ℝ)
    (hc : ∀ m, 0 ≤ c m) (hd : ∀ m, 0 ≤ d m) (hcs : Summable c) (hds : Summable d) :
    0 ≤ (∑ k ∈ Finset.Icc 1 K, lmW K k *
          ((∑' m, c m * Real.cos ((k : ℝ) * α m)) *
           (∑' m, d m * Real.cos ((k : ℝ) * β m))))
        + (1 / 2) * ((∑' m, c m) * (∑' m, d m)) := by
  -- Summability of the two cosine series.
  have hSc : ∀ k : ℕ, Summable (fun m : ℕ => c m * Real.cos ((k : ℝ) * α m)) := by
    intro k
    refine Summable.of_norm_bounded (g := c) hcs (fun m => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc m)]
    exact mul_le_of_le_one_right (hc m) (Real.abs_cos_le_one _)
  have hSd : ∀ k : ℕ, Summable (fun m : ℕ => d m * Real.cos ((k : ℝ) * β m)) := by
    intro k
    refine Summable.of_norm_bounded (g := d) hds (fun m => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hd m)]
    exact mul_le_of_le_one_right (hd m) (Real.abs_cos_le_one _)
  -- Summability of the coefficient product `(m,n) ↦ c_m d_n`.
  have hP : Summable (fun z : ℕ × ℕ => c z.1 * d z.2) := hcs.mul_of_nonneg hds hc hd
  -- Summability of the product family at fixed `k`.
  have hG : ∀ k : ℕ, Summable (fun z : ℕ × ℕ =>
      (c z.1 * Real.cos ((k : ℝ) * α z.1)) * (d z.2 * Real.cos ((k : ℝ) * β z.2))) := by
    intro k
    refine Summable.of_norm_bounded (g := fun z : ℕ × ℕ => c z.1 * d z.2) hP (fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (hc z.1), abs_of_nonneg (hd z.2)]
    calc c z.1 * |Real.cos ((k : ℝ) * α z.1)| * (d z.2 * |Real.cos ((k : ℝ) * β z.2)|)
        ≤ c z.1 * 1 * (d z.2 * 1) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (hc z.1)
          · exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (hd z.2)
          · exact mul_nonneg (hd z.2) (abs_nonneg _)
          · exact mul_nonneg (hc z.1) zero_le_one
      _ = c z.1 * d z.2 := by ring
  -- The two products of `tsum`s become double sums.
  have hprod : ∀ k : ℕ,
      (∑' m, c m * Real.cos ((k : ℝ) * α m)) * (∑' m, d m * Real.cos ((k : ℝ) * β m))
        = ∑' z : ℕ × ℕ,
            (c z.1 * Real.cos ((k : ℝ) * α z.1)) * (d z.2 * Real.cos ((k : ℝ) * β z.2)) :=
    fun k => Summable.tsum_mul_tsum (hSc k) (hSd k) (hG k)
  have hQ : (∑' m, c m) * (∑' m, d m) = ∑' z : ℕ × ℕ, c z.1 * d z.2 :=
    Summable.tsum_mul_tsum hcs hds hP
  -- Rewrite the `k`-sum into a sum of `tsum`s.
  have hkexp : (∑ k ∈ Finset.Icc 1 K, lmW K k *
        ((∑' m, c m * Real.cos ((k : ℝ) * α m)) *
         (∑' m, d m * Real.cos ((k : ℝ) * β m))))
      = ∑ k ∈ Finset.Icc 1 K, ∑' z : ℕ × ℕ, lmW K k *
          ((c z.1 * Real.cos ((k : ℝ) * α z.1)) * (d z.2 * Real.cos ((k : ℝ) * β z.2))) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hprod k, ← Summable.tsum_mul_left (lmW K k) (hG k)]
  -- Swap the finite `k`-sum with the double sum.
  have hswap : (∑ k ∈ Finset.Icc 1 K, ∑' z : ℕ × ℕ, lmW K k *
          ((c z.1 * Real.cos ((k : ℝ) * α z.1)) * (d z.2 * Real.cos ((k : ℝ) * β z.2))))
      = ∑' z : ℕ × ℕ, ∑ k ∈ Finset.Icc 1 K, lmW K k *
          ((c z.1 * Real.cos ((k : ℝ) * α z.1)) * (d z.2 * Real.cos ((k : ℝ) * β z.2))) := by
    exact (Summable.tsum_finsetSum
        (f := fun (k : ℕ) (z : ℕ × ℕ) => lmW K k *
          ((c z.1 * Real.cos ((k : ℝ) * α z.1)) * (d z.2 * Real.cos ((k : ℝ) * β z.2))))
        (s := Finset.Icc 1 K)
        (fun k _ => (hG k).mul_left (lmW K k))).symm
  have hFsum : Summable (fun z : ℕ × ℕ => ∑ k ∈ Finset.Icc 1 K, lmW K k *
          ((c z.1 * Real.cos ((k : ℝ) * α z.1)) * (d z.2 * Real.cos ((k : ℝ) * β z.2)))) :=
    summable_sum (fun k _ => (hG k).mul_left (lmW K k))
  -- Pointwise: factor `c z.1 * d z.2` out of the `k`-sum.
  have hpt : ∀ z : ℕ × ℕ,
      (∑ k ∈ Finset.Icc 1 K, lmW K k *
          ((c z.1 * Real.cos ((k : ℝ) * α z.1)) * (d z.2 * Real.cos ((k : ℝ) * β z.2))))
        + (1 / 2) * (c z.1 * d z.2)
      = c z.1 * d z.2 * (∑ k ∈ Finset.Icc 1 K, lmW K k *
          (Real.cos ((k : ℝ) * α z.1) * Real.cos ((k : ℝ) * β z.2)) + 1 / 2) := by
    intro z
    have h : ∀ k ∈ Finset.Icc 1 K, lmW K k *
          ((c z.1 * Real.cos ((k : ℝ) * α z.1)) * (d z.2 * Real.cos ((k : ℝ) * β z.2)))
        = c z.1 * d z.2 * (lmW K k *
          (Real.cos ((k : ℝ) * α z.1) * Real.cos ((k : ℝ) * β z.2))) := fun k _ => by ring
    rw [Finset.sum_congr rfl h, ← Finset.mul_sum,
        show (1 / 2 : ℝ) * (c z.1 * d z.2) = c z.1 * d z.2 * (1 / 2) by ring, ← mul_add]
  -- The whole left-hand side is the double sum of a nonnegative family.
  have hmain : (∑ k ∈ Finset.Icc 1 K, lmW K k *
        ((∑' m, c m * Real.cos ((k : ℝ) * α m)) *
         (∑' m, d m * Real.cos ((k : ℝ) * β m))))
      + (1 / 2) * ((∑' m, c m) * (∑' m, d m))
      = ∑' z : ℕ × ℕ, c z.1 * d z.2 * (∑ k ∈ Finset.Icc 1 K, lmW K k *
          (Real.cos ((k : ℝ) * α z.1) * Real.cos ((k : ℝ) * β z.2)) + 1 / 2) := by
    rw [hkexp, hQ, hswap, ← Summable.tsum_mul_left (1/2) hP,
        ← Summable.tsum_add hFsum (hP.mul_left (1 / 2))]
    exact tsum_congr hpt
  rw [hmain]
  exact tsum_nonneg (fun z => mul_nonneg (mul_nonneg (hc z.1) (hd z.2))
    (fejer_pair_nonneg K (α z.1) (β z.2)))

end Work.BW
