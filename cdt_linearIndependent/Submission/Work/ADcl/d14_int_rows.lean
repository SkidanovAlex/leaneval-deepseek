import Mathlib
import Submission.Work.ADcl.yode14_defs

/-!
# `Work.ADcl.d14_int_rows`: the integral rows of the 14-tuple `fourteen a b c`

Rows `11, 12, 13` of the coefficient matrix `Submission.Work.ADcl.A14` cover the `y`-integrals
`∫G`, `∫ (G − jet₁ G)/y`, `∫ (G − jet₂ G)/y²` of the 14-tuple
`Submission.CDTPlan.fourteen a b c` (indices `11, 12, 13`), where
`G = Submission.CDTPlan.GZ a b c`.  For each of them the common denominator is
`QF q0 q = X⁴ · q₀ · q` and the identity is the formal-calculus fact
`(∫ f)' = f`, together with `X^k · tq k f = f − jet_k f` (`Work.CDcl.X_pow_mul_tq`) that absorbs
the powers of `y` into the denominator.
-/

namespace Work.ADcl

open PowerSeries Polynomial

noncomputable section

/-- `X⁴ q₀ q · tq k f = X^{4-k} q₀ q · (f − jet_k f)` for `k ≤ 4`: the power of `y` hidden in
`tq k f` is traded against the common denominator `QF q0 q = X⁴ q₀ q`. -/
lemma QF_mul_tq (q0 q : Polynomial ℚ) (k : ℕ) (hk : k ≤ 4) (f : PowerSeries ℚ) :
    (QF q0 q : PowerSeries ℚ) * Submission.CDTPlan.tq k f
      = (PowerSeries.X : PowerSeries ℚ) ^ (4 - k) * (q0 : PowerSeries ℚ)
        * (q : PowerSeries ℚ) * (f - (Work.CDcl.jet k f : PowerSeries ℚ)) := by
  have hcast : (QF q0 q : PowerSeries ℚ) =
      (PowerSeries.X : PowerSeries ℚ) ^ 4 * (q0 : PowerSeries ℚ) * (q : PowerSeries ℚ) := by
    simp [QF, Polynomial.coe_mul]
  calc (QF q0 q : PowerSeries ℚ) * Submission.CDTPlan.tq k f
      = (PowerSeries.X : PowerSeries ℚ) ^ 4 * (q0 : PowerSeries ℚ) * (q : PowerSeries ℚ)
          * Submission.CDTPlan.tq k f := by rw [hcast]
    _ = (PowerSeries.X : PowerSeries ℚ) ^ (4 - k) * (PowerSeries.X : PowerSeries ℚ) ^ k
          * (q0 : PowerSeries ℚ) * (q : PowerSeries ℚ) * Submission.CDTPlan.tq k f := by
        rw [show (PowerSeries.X : PowerSeries ℚ) ^ 4
              = (PowerSeries.X : PowerSeries ℚ) ^ (4 - k) * (PowerSeries.X : PowerSeries ℚ) ^ k
              from by
                conv_lhs => rw [show (4 : ℕ) = (4 - k) + k from by omega, pow_add]]
    _ = (PowerSeries.X : PowerSeries ℚ) ^ (4 - k) * (q0 : PowerSeries ℚ) * (q : PowerSeries ℚ)
          * ((PowerSeries.X : PowerSeries ℚ) ^ k * Submission.CDTPlan.tq k f) := by ring
    _ = (PowerSeries.X : PowerSeries ℚ) ^ (4 - k) * (q0 : PowerSeries ℚ) * (q : PowerSeries ℚ)
          * (f - (Work.CDcl.jet k f : PowerSeries ℚ)) := by rw [Work.CDcl.X_pow_mul_tq]

theorem d14_int_rows (q0 q : Polynomial ℚ) (A0 : Fin 7 → Fin 7 → Polynomial ℚ)
    (A : Fin 4 → Polynomial ℚ) (cc : Polynomial ℚ) (a b c : ℤ) (k : ℕ)
    (hk : k = 11 ∨ k = 12 ∨ k = 13) :
    (Work.ADcl.QF q0 q : PowerSeries ℚ) *
        PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.fourteen a b c ⟨k, by omega⟩)
      = ∑ j, (Work.ADcl.A14 q0 q A0 A cc (Submission.CDTPlan.GZ a b c) ⟨k, by omega⟩ j :
            PowerSeries ℚ) * Submission.CDTPlan.fourteen a b c j := by
  rcases hk with rfl | rfl | rfl
  · -- row `11`: `(∫G)' = G`, and `A14` row `11` is `QF q0 q` on column `5` (`G`)
    rw [show (⟨11, by omega⟩ : Fin 14) = 11 from rfl,
        show Submission.CDTPlan.fourteen a b c (11 : Fin 14)
          = Submission.CDTPlan.intY (Submission.CDTPlan.GZ a b c) from rfl,
        Work.CDcl.derivative_intY]
    rw [Finset.sum_fin_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp [Work.ADcl.A14, Submission.CDTPlan.fourteen]
  · -- row `12`: `(∫(G − jet₁ G)/y)' = tq 1 G`, absorbed into column `5` and column `0` (`B₁ = 1`)
    rw [show (⟨12, by omega⟩ : Fin 14) = 12 from rfl,
        show Submission.CDTPlan.fourteen a b c (12 : Fin 14)
          = Submission.CDTPlan.intY (Submission.CDTPlan.tq 1 (Submission.CDTPlan.GZ a b c)) from rfl,
        Work.CDcl.derivative_intY,
        QF_mul_tq q0 q 1 (by norm_num) (Submission.CDTPlan.GZ a b c)]
    rw [Finset.sum_fin_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp [Work.ADcl.A14, Work.ADcl.rowT14, Submission.CDTPlan.fourteen, Submission.CDTPlan.B1]
    ring
  · -- row `13`: `(∫(G − jet₂ G)/y²)' = tq 2 G`
    rw [show (⟨13, by omega⟩ : Fin 14) = 13 from rfl,
        show Submission.CDTPlan.fourteen a b c (13 : Fin 14)
          = Submission.CDTPlan.intY (Submission.CDTPlan.tq 2 (Submission.CDTPlan.GZ a b c)) from rfl,
        Work.CDcl.derivative_intY,
        QF_mul_tq q0 q 2 (by norm_num) (Submission.CDTPlan.GZ a b c)]
    rw [Finset.sum_fin_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp [Work.ADcl.A14, Work.ADcl.rowT14, Submission.CDTPlan.fourteen, Submission.CDTPlan.B1]
    ring

end

end Work.ADcl
