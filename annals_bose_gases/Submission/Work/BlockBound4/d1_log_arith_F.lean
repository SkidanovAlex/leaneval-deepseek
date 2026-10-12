import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BlockBound4

open scoped Real BigOperators Topology

/-- Faithful logarithmic error comparison.  Suggested route: the LHS normalises to
`192 * (M*(M+1)/s^3) * (c0*av^2) * Real.log ((2*c0*av)⁻¹)` (`field_simp; ring`), and
`2*c0*av ≤ 1` gives `Real.log ((2*c0*av)⁻¹) ≤ Real.log ((c0*av)⁻¹)` with both nonnegative;
`1 ≤ M` gives `M+1 ≤ 2*M`.  Then `384 ≤ C`. -/
lemma d1_log_arith_F {M s c0 av C : ℝ} (hs : 0 < s) (hM1 : 1 ≤ M) (hc0 : 0 < c0)
    (hav : 0 < av) (hdil : 2 * c0 * av ≤ 1) (hC : 384 ≤ C) :
    M * ((M + 1) / (4 * s ^ 3))
        * (((2 * Real.pi) ^ 3)⁻¹
            * (6 * c0 * (16 * Real.pi * av) ^ 2 * (4 * Real.pi * Real.log ((2 * c0 * av)⁻¹))))
      ≤ C * (av ^ 2 * c0 * Real.log ((c0 * av)⁻¹) * (M * M / s ^ 3)) := by
  -- Abbreviate the two logarithms.
  set L := Real.log ((2 * c0 * av)⁻¹) with hL
  set K := Real.log ((c0 * av)⁻¹) with hK
  -- Both logarithms are nonnegative, because their arguments are `≥ 1`.
  have hLnn : 0 ≤ L := by
    rw [hL]; apply Real.log_nonneg
    have h2 : (0 : ℝ) < 2 * c0 * av := by positivity
    rw [← inv_one]
    exact (inv_le_inv₀ one_pos h2).mpr hdil
  have hKnn : 0 ≤ K := by
    rw [hK]; apply Real.log_nonneg
    have h1 : (0 : ℝ) < c0 * av := by positivity
    rw [← inv_one]
    exact (inv_le_inv₀ one_pos h1).mpr (by linarith)
  -- `L ≤ K` since `(2*c0*av)⁻¹ ≤ (c0*av)⁻¹`.
  have hLK : L ≤ K := by
    rw [hL, hK]; apply Real.log_le_log
    · positivity
    · have h1 : (0 : ℝ) < c0 * av := by positivity
      have h2 : (0 : ℝ) < 2 * c0 * av := by positivity
      rw [inv_le_inv₀ h2 h1]; linarith
  -- Core scalar inequality: `192 * M * (M+1) * L ≤ C * M^2 * K`.
  have hcore : 192 * (M * (M + 1) * L) ≤ C * M ^ 2 * K := by
    have hMnn : (0 : ℝ) ≤ M := by linarith
    have hMp : M + 1 ≤ 2 * M := by linarith
    have ha : M * (M + 1) * L ≤ M * (2 * M) * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMp hMnn) hLnn
    have hb : 192 * (M * (M + 1) * L) ≤ 192 * (M * (2 * M) * L) :=
      mul_le_mul_of_nonneg_left ha (by norm_num)
    have hstep1 : 192 * (M * (M + 1) * L) ≤ 384 * M ^ 2 * L := by nlinarith [hb]
    have hstep2 : 384 * M ^ 2 * L ≤ 384 * M ^ 2 * K := by nlinarith [hLK, sq_nonneg M]
    have hstep3 : 384 * M ^ 2 * K ≤ C * M ^ 2 * K := by
      nlinarith [hC, mul_nonneg (sq_nonneg M) hKnn]
    linarith
  -- Normalise the two sides, factoring out the positive `c0 * av^2 / s^3`.
  have hnorm1 : M * ((M + 1) / (4 * s ^ 3))
        * (((2 * Real.pi) ^ 3)⁻¹
            * (6 * c0 * (16 * Real.pi * av) ^ 2 * (4 * Real.pi * L)))
      = (c0 * av ^ 2 / s ^ 3) * (192 * (M * (M + 1) * L)) := by
    field_simp
    ring
  have hnorm2 : C * (av ^ 2 * c0 * K * (M * M / s ^ 3))
      = (c0 * av ^ 2 / s ^ 3) * (C * M ^ 2 * K) := by
    field_simp
  rw [hnorm1, hnorm2]
  exact mul_le_mul_of_nonneg_left hcore (by positivity)

end Work.BlockBound4
