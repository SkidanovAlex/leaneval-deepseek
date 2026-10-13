/-
# `Work.FTS.ClassCHon.CmpSupp.coeff_le_decay`

The mode norm of the Dirichlet eigenfunction `eFam m θ = cos θ · gC (2m+1) (sin θ)` in the
weight `cos θ dθ` is

  `eNorm m = ∫_{Iθ} eFam m θ ^ 2 · cos θ = (2m+2)(2m+3)/(4m+5)`     (`eFam_norm_fts`),

so `eNorm m = m + (5m+6)/(4m+5) ≥ m + 1`, hence `√(eNorm m) ≥ √m`.  The present lemma records
the sharper *scale-free* form actually needed downstream: for `m ≥ 1`,

  `m + 1 ≤ 2 √m · √(eNorm m)`,

which is exactly the statement that a coefficient of size `K / √(eNorm m)` on the interval
`[a,b]` decays at the `m^{-3/2}` rate required by the comparison/support argument:

  `(m+1) · (A · (K / √(eNorm m)) / m²) ≤ 2AK · m^{-3/2}`   for `A ≥ 0`, `K > 0`.

Squaring, `m + 1 ≤ 2 √m √(eNorm m)` is `(m+1)² ≤ 4 m · eNorm m`, i.e.

  `(m+1)² (4m+5) ≤ 4 m (2m+2)(2m+3) = 8 m (m+1)(2m+3)`,

which reduces to `4m² + 9m + 5 ≤ 8m² + 12m`, i.e. `0 ≤ 4m² + 3m − 5`, true for `m ≥ 1`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.ModalSolution.cmode_bessel
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.CmpSupp

/-- The closed form of the mode norm `eNorm`: `eNorm m = (2m+2)(2m+3)/(4m+5)`. -/
lemma eNorm_eq (m : ℕ) :
    Work.EllipticEst.ModalSolution.eNorm m
      = ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5) := by
  rw [Work.EllipticEst.ModalSolution.eNorm, Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts]

/-- The scale-free lower bound `m + 1 ≤ 2 √m · √(eNorm m)` for `m ≥ 1`. -/
lemma le_two_sqrt_mul_sqrt_eNorm (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) + 1
      ≤ 2 * (Real.sqrt (m : ℝ) * Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)) := by
  have hn1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hn_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have heNorm_pos : 0 < Work.EllipticEst.ModalSolution.eNorm m :=
    Work.EllipticEst.ModalSolution.eNorm_pos m
  -- the squared form of the bound
  have hbase : (((m : ℝ) + 1) ^ 2)
      ≤ 4 * (m : ℝ) * Work.EllipticEst.ModalSolution.eNorm m := by
    rw [eNorm_eq]
    have h4 : (0 : ℝ) < 4 * (m : ℝ) + 5 := by linarith
    field_simp
    nlinarith [hn1]
  have hsq : (((m : ℝ) + 1) / 2) ^ 2
      ≤ (m : ℝ) * Work.EllipticEst.ModalSolution.eNorm m := by
    rw [show (((m : ℝ) + 1) / 2) ^ 2 = ((m : ℝ) + 1) ^ 2 / 4 by ring]
    linarith
  have hle : ((m : ℝ) + 1) / 2
      ≤ Real.sqrt ((m : ℝ) * Work.EllipticEst.ModalSolution.eNorm m) :=
    Real.le_sqrt_of_sq_le hsq
  rw [Real.sqrt_mul (le_of_lt hn_pos) (Work.EllipticEst.ModalSolution.eNorm m)] at hle
  linarith

theorem coeff_le_decay (A K : ℝ) (hA : 0 ≤ A) (hK : 0 < K) (m : ℕ) (hm : 1 ≤ m) :
    ((m : ℝ) + 1) * (A * (K / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)) / (m : ℝ) ^ 2)
      ≤ (2 * A * K) * (m : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hn_pos : (0 : ℝ) < (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hs_pos : 0 < Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) :=
    Real.sqrt_pos.mpr (Work.EllipticEst.ModalSolution.eNorm_pos m)
  have hkey := le_two_sqrt_mul_sqrt_eNorm m hm
  -- `m^{-3/2} · m² = √m`
  have hpow : (m : ℝ) ^ (-(3 / 2 : ℝ)) * (m : ℝ) ^ 2 = Real.sqrt (m : ℝ) := by
    rw [← Real.rpow_natCast (m : ℝ) 2,
      ← Real.rpow_add hn_pos (-(3 / 2 : ℝ)) ((2 : ℕ) : ℝ),
      show -(3 / 2 : ℝ) + ((2 : ℕ) : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  have hstep : ((m : ℝ) + 1) / (m : ℝ) ^ 2
      ≤ 2 * (m : ℝ) ^ (-(3 / 2 : ℝ))
          * Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) ^ 2)]
    calc (m : ℝ) + 1
        ≤ 2 * (Real.sqrt (m : ℝ)
            * Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)) := hkey
      _ = (2 * (m : ℝ) ^ (-(3 / 2 : ℝ))
              * Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)) * (m : ℝ) ^ 2 := by
          rw [show (2 * (m : ℝ) ^ (-(3 / 2 : ℝ))
                  * Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)) * (m : ℝ) ^ 2
                = 2 * ((m : ℝ) ^ (-(3 / 2 : ℝ)) * (m : ℝ) ^ 2)
                  * Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) by ring, hpow]
          ring
  have hAK : 0 ≤ A * K / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) :=
    div_nonneg (mul_nonneg hA (le_of_lt hK)) (le_of_lt hs_pos)
  calc ((m : ℝ) + 1)
        * (A * (K / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)) / (m : ℝ) ^ 2)
      = (((m : ℝ) + 1) / (m : ℝ) ^ 2)
          * (A * K / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)) := by
        field_simp
        try ring
    _ ≤ (2 * (m : ℝ) ^ (-(3 / 2 : ℝ))
            * Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m))
          * (A * K / Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)) :=
        mul_le_mul_of_nonneg_right hstep hAK
    _ = (2 * A * K) * (m : ℝ) ^ (-(3 / 2 : ℝ)) := by
        field_simp
        try ring

end Work.FTS.ClassCHon.CmpSupp
