import Mathlib
import Submission.Work.A3.Weil.Defs

/-!
# The geometric bound for an affine phase (`Work.A3.Weil.geomBound`)

For a real slope `lam`, an offset `c` and any interval `[a,b] ⊆ [0,N)`, the exponential sum
`Σ_{n ∈ [a,b]} e(lam·n + c)` is bounded by the "first-derivative-test" quantity

`geomBound N lam = 1 / max (intDist lam) (1/N)`,

i.e. by `min (length) (1/intDist lam)`.  This is the closing step of the `k`-fold Weyl
differencing: after differencing a polynomial phase `k+1 = deg Q` times the phase is affine, and
the resulting exponential sum must be bounded by `geomBound`.

The proof reduces the interval to a `range` (via `Int.Icc_eq_finset_map`), pulls out the constant
prefactor `e(lam·a + c)` (which has norm one), and then uses the two available bounds for a
linear-phase sum `Σ_{j<M} e(lam·j)`: the trivial length bound
(`Submission.VanDerCorput.linPhase_trivial`) and, when `intDist lam > 0`, the geometric bound
`(1/2)/intDist lam` (`Submission.UnitCircle.geom_sum_bound_of_intDist_pos`).
-/

namespace Work.A3.Weil

open Finset

/-- The summation range `wRange N = [0,N)` has exactly `N` elements. -/
lemma card_wRange (N : ℕ) : (wRange N).card = N := by
  rw [wRange, Int.card_Icc]
  simp

theorem norm_sum_exp_affine_le_geomBound (lam c : ℝ) (N : ℕ) (a b : ℤ)
    (hsub : Finset.Icc a b ⊆ Work.A3.Weil.wRange N) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp (((2 * Real.pi * (lam * (n : ℝ) + c) : ℝ) : ℂ) * Complex.I)‖
      ≤ Work.A3.Weil.geomBound N lam := by
  classical
  set d : ℝ := Submission.VanDerCorput.intDist lam with hd
  have hd0 : 0 ≤ d := by
    rw [hd]; exact Submission.VanDerCorput.intDist_nonneg lam
  have hGnn : 0 ≤ geomBound N lam := by
    rw [geomBound]
    exact inv_nonneg.mpr (le_trans hd0 (le_max_left _ _))
  by_cases hab : a ≤ b
  · -- nonempty interval: reindex over `range m` and split on the size of `intDist lam`
    set m : ℕ := (b + 1 - a).toNat with hm
    have hm1 : 1 ≤ m := by
      rw [hm]
      exact (Int.le_toNat (by omega : (0 : ℤ) ≤ b + 1 - a)).mpr (by omega)
    have hcard : (Finset.Icc a b).card = m := by rw [hm, Int.card_Icc]
    have hmN : m ≤ N := by
      rw [← hcard]
      have h := Finset.card_le_card hsub
      rwa [card_wRange] at h
    have hreindex :
        ∑ n ∈ Finset.Icc a b,
            Complex.exp (((2 * Real.pi * (lam * (n : ℝ) + c) : ℝ) : ℂ) * Complex.I)
          = Complex.exp (((2 * Real.pi * (lam * (a : ℝ) + c) : ℝ) : ℂ) * Complex.I) *
              ∑ j ∈ Finset.range m, Submission.VanDerCorput.linPhase lam j := by
      rw [hm, Int.Icc_eq_finset_map, Finset.sum_map, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Function.Embedding.trans_apply, addLeftEmbedding_apply,
        Nat.castEmbedding_apply]
      rw [Submission.VanDerCorput.linPhase, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hnorm :
        ‖∑ n ∈ Finset.Icc a b,
            Complex.exp (((2 * Real.pi * (lam * (n : ℝ) + c) : ℝ) : ℂ) * Complex.I)‖
          = ‖∑ j ∈ Finset.range m, Submission.VanDerCorput.linPhase lam j‖ := by
      rw [hreindex, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    rw [hnorm]
    by_cases hcase : d ≤ ((N : ℝ))⁻¹
    · -- `intDist lam` is small: use the length bound, `geomBound N lam = N`
      have hG : geomBound N lam = (N : ℝ) := by
        rw [geomBound, ← hd, max_eq_right hcase, inv_inv]
      rw [hG]
      calc ‖∑ j ∈ Finset.range m, Submission.VanDerCorput.linPhase lam j‖
          ≤ (m : ℝ) := Submission.VanDerCorput.linPhase_trivial lam m
        _ ≤ (N : ℝ) := by exact_mod_cast hmN
    · -- `intDist lam` is large: the geometric bound gives `1/intDist lam`
      have hcase' : ((N : ℝ))⁻¹ < d := not_le.mp hcase
      have hdpos : 0 < d := lt_of_le_of_lt (inv_nonneg.mpr (Nat.cast_nonneg N)) hcase'
      have hG : geomBound N lam = d⁻¹ := by
        rw [geomBound, ← hd, max_eq_left (le_of_lt hcase')]
      rw [hG]
      have hbound := Submission.UnitCircle.geom_sum_bound_of_intDist_pos
        (α := lam) (L := m) (by rwa [← hd])
      calc ‖∑ j ∈ Finset.range m, Submission.VanDerCorput.linPhase lam j‖
          ≤ (1 / 2) / Submission.VanDerCorput.intDist lam := hbound
        _ = (1 / 2) / d := by rw [← hd]
        _ ≤ d⁻¹ := by
            rw [div_le_iff₀ hdpos, inv_mul_cancel₀ (ne_of_gt hdpos)]
            norm_num
  · -- empty interval
    have hempty : Finset.Icc a b = ∅ := Finset.Icc_eq_empty hab
    rw [hempty, Finset.sum_empty, norm_zero]
    exact hGnn

end Work.A3.Weil
