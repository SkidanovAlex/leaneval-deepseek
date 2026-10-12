import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.LatGreen.PoissonDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.HeatK1Aux` — auxiliary analytic facts for Poisson/Jacobi summation

Absolute convergence of the one-dimensional periodised heat kernel (`summable_heatK1`,
`summable_thetaTerm1`) and the multiplicativity of the Fourier terms
(`prod_thetaTerm1_eq_thetaTerm`).
-/

noncomputable section

open scoped Real BigOperators
open MeasureTheory Set

namespace Work.BoseFixR.LatGreen

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The one-dimensional periodised heat kernel is absolutely summable: the Gaussian tail beats
the lattice.  Bound: `(x − n)² ≥ n²/2 − x²`. -/
theorem summable_heatK1 {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable fun n : ℤ => heatK1 t (x - n) := by
  have hmain : Summable fun n : ℤ => (4 * Real.pi * t) ^ (-(1 / 2 : ℝ))
      * Real.exp (x ^ 2 / (4 * t)) * Real.exp (-(1 / (8 * t)) * (n : ℝ) ^ 2) :=
    (summable_exp_neg_mul_sq_int (c := 1 / (8 * t)) (by positivity)).mul_left _
  refine Summable.of_nonneg_of_le (fun n => heatK1_nonneg ht _) (fun n => ?_) hmain
  have hb : (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) ≥ 0 := Real.rpow_nonneg (by positivity) _
  have h8t : (0 : ℝ) < 8 * t := by positivity
  have key : -(x - (n : ℝ)) ^ 2 / (4 * t)
      = -(1 / (8 * t)) * (n : ℝ) ^ 2 + x ^ 2 / (4 * t) - (2 * x - (n : ℝ)) ^ 2 / (8 * t) := by
    field_simp
    ring
  unfold heatK1
  calc (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-(x - (n : ℝ)) ^ 2 / (4 * t))
      ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ))
          * (Real.exp (-(1 / (8 * t)) * (n : ℝ) ^ 2) * Real.exp (x ^ 2 / (4 * t))) := by
        refine mul_le_mul_of_nonneg_left ?_ hb
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        rw [key]
        have hdiv : 0 ≤ (2 * x - (n : ℝ)) ^ 2 / (8 * t) := div_nonneg (sq_nonneg _) h8t.le
        linarith
    _ = (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (x ^ 2 / (4 * t))
          * Real.exp (-(1 / (8 * t)) * (n : ℝ) ^ 2) := by ring

/-- The Fourier terms of the torus heat kernel are absolutely summable. -/
theorem summable_thetaTerm1 {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable fun m : ℤ => ‖thetaTerm1 t x m‖ := by
  have h : ∀ m : ℤ, ‖thetaTerm1 t x m‖
      = Real.exp (-(4 * Real.pi ^ 2 * t) * (m : ℝ) ^ 2) := by
    intro m
    unfold thetaTerm1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _), Complex.norm_exp]
    simp
  rw [funext h]
  exact summable_exp_neg_mul_sq_int (by positivity)

/-- The three-dimensional Fourier term is the product of the three one-dimensional ones. -/
theorem prod_thetaTerm1_eq_thetaTerm (t : ℝ) (u : ℝ³) (k : Fin 3 → ℤ) :
    thetaTerm1 t (u 0) (k 0) * (thetaTerm1 t (u 1) (k 1) * thetaTerm1 t (u 2) (k 2))
      = thetaTerm t u k := by
  have h1 : Real.exp (-(4 * Real.pi ^ 2 * t) * (k 0 : ℝ) ^ 2)
        * (Real.exp (-(4 * Real.pi ^ 2 * t) * (k 1 : ℝ) ^ 2)
          * Real.exp (-(4 * Real.pi ^ 2 * t) * (k 2 : ℝ) ^ 2))
      = Real.exp (-(4 * Real.pi ^ 2 * t) * ‖latVec k‖ ^ 2) := by
    rw [latVec_norm_sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h2 : Complex.exp (-(2 * Real.pi * Complex.I * ((k 0 : ℝ) * u 0)))
        * (Complex.exp (-(2 * Real.pi * Complex.I * ((k 1 : ℝ) * u 1)))
          * Complex.exp (-(2 * Real.pi * Complex.I * ((k 2 : ℝ) * u 2))))
      = Complex.exp (-(2 * Real.pi * Complex.I * (((∑ i, (k i : ℝ) * u i) : ℝ) : ℂ))) := by
    rw [← Complex.exp_add, ← Complex.exp_add, Fin.sum_univ_three]
    congr 1
    push_cast
    ring
  have step : thetaTerm1 t (u 0) (k 0) * (thetaTerm1 t (u 1) (k 1) * thetaTerm1 t (u 2) (k 2))
      = (Real.exp (-(4 * Real.pi ^ 2 * t) * (k 0 : ℝ) ^ 2)
            * (Real.exp (-(4 * Real.pi ^ 2 * t) * (k 1 : ℝ) ^ 2)
              * Real.exp (-(4 * Real.pi ^ 2 * t) * (k 2 : ℝ) ^ 2)) : ℂ)
          * (Complex.exp (-(2 * Real.pi * Complex.I * ((k 0 : ℝ) * u 0)))
            * (Complex.exp (-(2 * Real.pi * Complex.I * ((k 1 : ℝ) * u 1)))
              * Complex.exp (-(2 * Real.pi * Complex.I * ((k 2 : ℝ) * u 2))))) := by
    unfold thetaTerm1
    push_cast
    ring
  rw [step, ← Complex.ofReal_mul, ← Complex.ofReal_mul, h1, h2]
  unfold thetaTerm
  rfl

end Work.BoseFixR.LatGreen
