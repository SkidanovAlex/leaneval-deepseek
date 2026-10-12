import Mathlib.Analysis.PSeries
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.latticeTailFiberSum`

The **shell-series tail bound** for the three-dimensional lattice.  For `N ≥ 2`, `R ≥ 1` and any
`M`,

    ∑_{j = R+1}^{M} (24 j² + 2) · j^{-2N}  ≤  52 · (R+1)^{3-2N} .

`24 j² + 2` is the cardinality of the `j`-th lattice shell `shell j = box j \ box (j-1)`
(`Work.BoseBoxFock.ShellCard`: exactly `(2j+1)³ - (2j-1)³ = 24 j² + 2` points), and each lattice
vector of the shell has `nSq d ≥ j²`.  So this is the standard sharp three-dimensional tail
estimate `∑_{‖d‖ > ρ} ‖d‖^{-2N} ≲ ρ^{3-2N}` (the exponent `3 - 2N` is the sharp one since
`N > 3/2`), obtained by summing the shell series `∑_j (24 j² + 2) j^{-2N} ≲ ∑_j j^{2-2N}` against
the one-dimensional estimate `∑_{j ≥ K} j^{-q} ≤ 2 K^{1-q}` for `q ≥ 2`.

## Proof

* **Pointwise.**  Writing `(j:ℝ)^{2N} = (j:ℝ)^{2N-2} · (j:ℝ)²` (valid since `N ≥ 1`) and using
  `j ≥ 1`, we get `(24 j² + 2) · (j²)⁻¹ = 24 + 2 j^{-2} ≤ 26`, hence

      (24 j² + 2) · j^{-2N} ≤ 26 · j^{-(2N-2)} .

* **Sum.**  For `j ≥ R+1` and `p = 2N-2 ≥ 2`, the elementary comparison
  `j^{-p} = (j^{p-2})⁻¹ (j²)⁻¹ ≤ ((R+1)^{p-2})⁻¹ (j²)⁻¹` gives

      ∑_{j = R+1}^{M} j^{-p} ≤ ((R+1)^{p-2})⁻¹ · ∑_{j = R+1}^{M} j^{-2}
                             ≤ ((R+1)^{p-2})⁻¹ · 2/(R+1) = 2 (R+1)^{-(p-1)} ,

  where `∑_{j = R+1}^{M} j^{-2} ≤ 2/(R+1)` is Mathlib's `sum_Ioo_inv_sq_le` (applied to
  `Ioo R (M+1) = Ico (R+1) (M+1)`).  With `p - 1 = 2N-3` and the factor `26`, this yields
  `26 · 2 = 52`.
-/

namespace Work.BoseBoxFock.PCFU

open Finset

/-- Elementary algebraic identity: `(n^k)⁻¹ · (2 n⁻¹) = 2 · (n^{k+1})⁻¹`. -/
private lemma arith_inv (n : ℝ) (k : ℕ) : (n ^ k)⁻¹ * (2 * n⁻¹) = 2 * (n ^ (k + 1))⁻¹ := by
  rw [pow_succ, mul_inv]
  ring

/-- **Pointwise step.**  For `j ≥ 1` and `N ≥ 1`,
`(24 j² + 2) · j^{-2N} ≤ 26 · j^{-(2N-2)}`. -/
private lemma term_le_inv_pow (N j : ℕ) (hN : 1 ≤ N) (hj : 1 ≤ j) :
    (24 * (j : ℝ) ^ 2 + 2) * ((j : ℝ) ^ (2 * N))⁻¹ ≤ 26 * ((j : ℝ) ^ (2 * N - 2))⁻¹ := by
  have hx : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hx1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hx2 : (0 : ℝ) < (j : ℝ) ^ 2 := by positivity
  have hkey : (24 * (j : ℝ) ^ 2 + 2) * ((j : ℝ) ^ 2)⁻¹ ≤ 26 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hx2]
    nlinarith [hx1, sq_nonneg ((j : ℝ) - 1)]
  have hpow : (j : ℝ) ^ (2 * N) = (j : ℝ) ^ (2 * N - 2) * (j : ℝ) ^ 2 := by
    rw [← pow_add, show 2 * N - 2 + 2 = 2 * N by omega]
  calc (24 * (j : ℝ) ^ 2 + 2) * ((j : ℝ) ^ (2 * N))⁻¹
      = ((24 * (j : ℝ) ^ 2 + 2) * ((j : ℝ) ^ 2)⁻¹) * ((j : ℝ) ^ (2 * N - 2))⁻¹ := by
        rw [hpow, mul_inv]; ring
    _ ≤ 26 * ((j : ℝ) ^ (2 * N - 2))⁻¹ :=
        mul_le_mul_of_nonneg_right hkey (by positivity)

/-- **Sum step.**  For `N ≥ 2` and any `R`, `M`,
`∑_{j = R+1}^{M} j^{-(2N-2)} ≤ 2 (R+1)^{-(2N-3)}`. -/
private lemma sum_inv_pow_le (N R M : ℕ) (hN : 2 ≤ N) :
    ∑ j ∈ Finset.Ico (R + 1) (M + 1), ((j : ℝ) ^ (2 * N - 2))⁻¹
      ≤ 2 * ((((R : ℝ) + 1) ^ (2 * N - 3))⁻¹) := by
  have hR : (0 : ℝ) < (R : ℝ) + 1 := by positivity
  have hIco : Finset.Ico (R + 1) (M + 1) = Finset.Ioo R (M + 1) := by
    simpa using Finset.Ico_succ_left_eq_Ioo R (M + 1)
  -- pointwise comparison of the `p`-th powers with the square, `p = 2N-2`
  have hA : ∀ j ∈ Finset.Ico (R + 1) (M + 1),
      ((j : ℝ) ^ (2 * N - 2))⁻¹ ≤ (((R : ℝ) + 1) ^ (2 * N - 4))⁻¹ * ((j : ℝ) ^ 2)⁻¹ := by
    intro j hj
    have hjn : R + 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hjn' : ((R : ℝ) + 1) ≤ (j : ℝ) := by
      have : ((R + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjn
      simpa using this
    have hjpos : (0 : ℝ) < (j : ℝ) := by linarith
    have hpow : (j : ℝ) ^ (2 * N - 2) = (j : ℝ) ^ (2 * N - 4) * (j : ℝ) ^ 2 := by
      rw [← pow_add, show 2 * N - 4 + 2 = 2 * N - 2 by omega]
    have hinv : ((j : ℝ) ^ (2 * N - 4))⁻¹ ≤ (((R : ℝ) + 1) ^ (2 * N - 4))⁻¹ := by
      refine (inv_le_inv₀ (pow_pos hjpos _) (pow_pos hR _)).mpr ?_
      exact pow_le_pow_left₀ (le_of_lt hR) hjn' _
    calc ((j : ℝ) ^ (2 * N - 2))⁻¹
        = ((j : ℝ) ^ (2 * N - 4))⁻¹ * ((j : ℝ) ^ 2)⁻¹ := by rw [hpow, mul_inv]
      _ ≤ (((R : ℝ) + 1) ^ (2 * N - 4))⁻¹ * ((j : ℝ) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hinv (by positivity)
  calc ∑ j ∈ Finset.Ico (R + 1) (M + 1), ((j : ℝ) ^ (2 * N - 2))⁻¹
      ≤ ∑ j ∈ Finset.Ico (R + 1) (M + 1),
          (((R : ℝ) + 1) ^ (2 * N - 4))⁻¹ * ((j : ℝ) ^ 2)⁻¹ :=
          Finset.sum_le_sum hA
    _ = (((R : ℝ) + 1) ^ (2 * N - 4))⁻¹ *
          ∑ j ∈ Finset.Ico (R + 1) (M + 1), ((j : ℝ) ^ 2)⁻¹ := by
          rw [Finset.mul_sum]
    _ ≤ (((R : ℝ) + 1) ^ (2 * N - 4))⁻¹ * (2 / ((R : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [hIco]
          have := sum_Ioo_inv_sq_le (α := ℝ) R (M + 1)
          simpa using this
    _ = 2 * ((((R : ℝ) + 1) ^ (2 * N - 3))⁻¹) := by
          rw [div_eq_mul_inv, arith_inv, show 2 * N - 4 + 1 = 2 * N - 3 by omega]

/-- **The shell-series tail bound.**  For `N ≥ 2`, `R ≥ 1` and any `M`,

    ∑_{j = R+1}^{M} (24 j² + 2) · j^{-2N}  ≤  52 · (R+1)^{3-2N} .

(`24 j² + 2` is the cardinality of the `j`-th lattice shell, and `j^{-2N}` is the largest value of
`‖d‖^{-2N}` on that shell.) -/
theorem latticeTailFiberSum (N R M : ℕ) (hN : 2 ≤ N) (hR : 1 ≤ R) :
    ∑ j ∈ Finset.Ico (R + 1) (M + 1), (24 * (j : ℝ) ^ 2 + 2) * ((j : ℝ) ^ (2 * N))⁻¹
      ≤ 52 * ((((R : ℝ) + 1) ^ (2 * N - 3))⁻¹) := by
  have hN1 : 1 ≤ N := by omega
  calc ∑ j ∈ Finset.Ico (R + 1) (M + 1), (24 * (j : ℝ) ^ 2 + 2) * ((j : ℝ) ^ (2 * N))⁻¹
      ≤ ∑ j ∈ Finset.Ico (R + 1) (M + 1), 26 * ((j : ℝ) ^ (2 * N - 2))⁻¹ := by
        apply Finset.sum_le_sum
        intro j hj
        exact term_le_inv_pow N j hN1 (by have := (Finset.mem_Ico.mp hj).1; omega)
    _ = 26 * ∑ j ∈ Finset.Ico (R + 1) (M + 1), ((j : ℝ) ^ (2 * N - 2))⁻¹ :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ 26 * (2 * ((((R : ℝ) + 1) ^ (2 * N - 3))⁻¹)) :=
        mul_le_mul_of_nonneg_left (sum_inv_pow_le N R M hN) (by norm_num)
    _ = 52 * ((((R : ℝ) + 1) ^ (2 * N - 3))⁻¹) := by ring

end Work.BoseBoxFock.PCFU
