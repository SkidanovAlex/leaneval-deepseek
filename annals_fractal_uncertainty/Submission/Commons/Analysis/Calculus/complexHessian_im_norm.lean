import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Commons.Analysis.Calculus.iteratedFDeriv_two_sqrt_one_add_norm_sq
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_nonneg_of_localMin

namespace Commons.Analysis.Calculus

set_option autoImplicit false

open scoped BigOperators

/-- The `L²` norm of a vector of `ℝᵈ`, viewed as an element of `EuclideanSpace ℝ (Fin d)`,
is the sum of the squares of its coordinates. -/
lemma euclidean_norm_sq_toLp {d : ℕ} (y : Fin d → ℝ) :
    ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d))‖ ^ 2 = ∑ j, y j ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]

/-- The `L²` inner product of two vectors of `ℝᵈ`, viewed as elements of
`EuclideanSpace ℝ (Fin d)`, is the sum of the products of their coordinates. -/
lemma euclidean_inner_toLp {d : ℕ} (y b : Fin d → ℝ) :
    inner ℝ (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 b)
      = ∑ j, y j * b j := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.inner_apply]

/-- Second derivative at `0` of `t ↦ √(1 + ∑ j, (y j + t * b j)²)`.
This is the one-dimensional computation underlying the Hermitian Hessian of
`z ↦ √(1 + ‖Im z‖²)` along the line `t ↦ y + t * b`. -/
lemma deriv_deriv_sqrt_one_add_sum_sq {d : ℕ} (y b : Fin d → ℝ) :
    deriv (deriv (fun t : ℝ => Real.sqrt (1 + ∑ j, (y j + t * b j) ^ 2))) 0
      = (∑ j, b j ^ 2) / Real.sqrt (1 + ∑ j, y j ^ 2)
        - (∑ j, y j * b j) ^ 2 / (Real.sqrt (1 + ∑ j, y j ^ 2)) ^ 3 := by
  have hnorm : ∀ t : ℝ,
      ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) + t • WithLp.toLp 2 b‖ ^ 2
        = ∑ j, (y j + t * b j) ^ 2 := by
    intro t
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro j _
    simp
  have hfun : (fun t : ℝ => Real.sqrt (1 + ∑ j, (y j + t * b j) ^ 2))
      = fun t : ℝ => Real.sqrt
          (1 + ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) + t • WithLp.toLp 2 b‖ ^ 2) := by
    funext t
    rw [hnorm t]
  rw [hfun, deriv_deriv_sqrt_one_add_norm_sq_line, euclidean_norm_sq_toLp y,
    euclidean_norm_sq_toLp b, euclidean_inner_toLp y b]

/-- Elementary algebraic bound: if `r > 0`, `r² = 1 + Y` and `Sᵢ² ≤ Y Tᵢ` for `i = 1, 2`, then
`(T₁ + T₂) / r³ ≤ (T₁ / r - S₁² / r³) + (T₂ / r - S₂² / r³)`.  This is the Cauchy–Schwarz step
in the proof of the Hermitian Hessian inequality. -/
lemma div_add_hessian_bound (r Y T1 T2 S1 S2 : ℝ) (hr : 0 < r) (hr2 : r ^ 2 = 1 + Y)
    (h1 : S1 ^ 2 ≤ Y * T1) (h2 : S2 ^ 2 ≤ Y * T2) :
    (T1 + T2) / r ^ 3 ≤ (T1 / r - S1 ^ 2 / r ^ 3) + (T2 / r - S2 ^ 2 / r ^ 3) := by
  have hr3 : 0 < r ^ 3 := by positivity
  have hmain : (T1 / r - S1 ^ 2 / r ^ 3) + (T2 / r - S2 ^ 2 / r ^ 3)
      = ((T1 + T2) * r ^ 2 - (S1 ^ 2 + S2 ^ 2)) / r ^ 3 := by
    field_simp
    ring
  rw [hmain, div_le_div_iff_of_pos_right hr3, hr2]
  nlinarith [h1, h2]

/-- **The Hermitian Hessian of `z ↦ √(1+‖Im z‖²)`.**  For the plurisubharmonic function
`ψ(z) = √(1 + ∑_j (Im z_j)²)` one has, for all `z, w ∈ ℂᵈ`,
`(‖Re w‖² + ‖Im w‖²) / ⟨Im z⟩³ ≤ (D²ψ z)![w,w] + (D²ψ z)![I • w, I • w]`;  the left-hand side is
`4 ∂∂̄ψ(z)` applied to `w ⊗ w̄`. -/
theorem complexHessian_im_norm {d : ℕ} (z w : Fin d → ℂ) :
    (∑ j, (w j).im ^ 2 + ∑ j, (w j).re ^ 2) / (Real.sqrt (1 + ∑ j, (z j).im ^ 2)) ^ 3 ≤
      (iteratedFDeriv ℝ 2 (fun z : Fin d → ℂ => Real.sqrt (1 + ∑ j, (z j).im ^ 2)) z) ![w, w]
      + (iteratedFDeriv ℝ 2 (fun z : Fin d → ℂ => Real.sqrt (1 + ∑ j, (z j).im ^ 2)) z)
          ![Complex.I • w, Complex.I • w] := by
  set ψ : (Fin d → ℂ) → ℝ := fun z => Real.sqrt (1 + ∑ j, (z j).im ^ 2) with hψ
  have hcont : ContDiff ℝ 2 ψ := by
    rw [hψ]
    apply ContDiff.sqrt
    · apply ContDiff.add contDiff_const
      apply ContDiff.sum
      intro j _
      have hcoord : ContDiff ℝ 2 (fun z : Fin d → ℂ => (z j).im) := by
        have h : ContDiff ℝ 2 (fun z : Fin d → ℂ => (Complex.imCLM : ℂ → ℝ) (z j)) := by
          fun_prop
        simpa using h
      exact hcoord.pow 2
    · intro z; positivity
  -- Reduce the second iterated derivatives to second derivatives along lines.
  have hred1 : (iteratedFDeriv ℝ 2 ψ z) ![w, w]
      = deriv (deriv (fun t : ℝ => ψ (z + t • w))) 0 := by
    rw [iteratedFDeriv_two_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Commons.Analysis.Calculus.FDeriv.deriv_deriv_comp_line (f := ψ) hcont.contDiffAt w]
  have hred2 : (iteratedFDeriv ℝ 2 ψ z) ![Complex.I • w, Complex.I • w]
      = deriv (deriv (fun t : ℝ => ψ (z + t • (Complex.I • w)))) 0 := by
    rw [iteratedFDeriv_two_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Commons.Analysis.Calculus.FDeriv.deriv_deriv_comp_line (f := ψ) hcont.contDiffAt
      (Complex.I • w)]
  -- Identify the restrictions to the two lines.
  have heq1 : (fun t : ℝ => ψ (z + t • w))
      = fun t : ℝ => Real.sqrt (1 + ∑ j, ((z j).im + t * (w j).im) ^ 2) := by
    funext t
    simp only [hψ]
    have hsum : (∑ j, ((z + t • w) j).im ^ 2) = ∑ j, ((z j).im + t * (w j).im) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show ((z + t • w) j).im = (z j).im + t * (w j).im from by
        simp [Complex.add_im, Complex.mul_im]]
    rw [hsum]
  have heq2 : (fun t : ℝ => ψ (z + t • (Complex.I • w)))
      = fun t : ℝ => Real.sqrt (1 + ∑ j, ((z j).im + t * (w j).re) ^ 2) := by
    funext t
    simp only [hψ]
    have hsum : (∑ j, ((z + t • (Complex.I • w)) j).im ^ 2)
        = ∑ j, ((z j).im + t * (w j).re) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show ((z + t • (Complex.I • w)) j).im = (z j).im + t * (w j).re from by
        simp [Complex.add_im, Complex.mul_im]]
    rw [hsum]
  -- Explicit values of the two second derivatives.
  have hD1 : (iteratedFDeriv ℝ 2 ψ z) ![w, w]
      = (∑ j, (w j).im ^ 2) / Real.sqrt (1 + ∑ j, (z j).im ^ 2)
        - (∑ j, (z j).im * (w j).im) ^ 2 / (Real.sqrt (1 + ∑ j, (z j).im ^ 2)) ^ 3 := by
    rw [hred1, heq1]
    exact deriv_deriv_sqrt_one_add_sum_sq (fun j => (z j).im) (fun j => (w j).im)
  have hD2 : (iteratedFDeriv ℝ 2 ψ z) ![Complex.I • w, Complex.I • w]
      = (∑ j, (w j).re ^ 2) / Real.sqrt (1 + ∑ j, (z j).im ^ 2)
        - (∑ j, (z j).im * (w j).re) ^ 2 / (Real.sqrt (1 + ∑ j, (z j).im ^ 2)) ^ 3 := by
    rw [hred2, heq2]
    exact deriv_deriv_sqrt_one_add_sum_sq (fun j => (z j).im) (fun j => (w j).re)
  rw [hD1, hD2]
  -- Cauchy–Schwarz step.
  refine div_add_hessian_bound (Real.sqrt (1 + ∑ j, (z j).im ^ 2)) (∑ j, (z j).im ^ 2)
      (∑ j, (w j).im ^ 2) (∑ j, (w j).re ^ 2)
      (∑ j, (z j).im * (w j).im) (∑ j, (z j).im * (w j).re)
      (Real.sqrt_pos.mpr (by positivity)) (Real.sq_sqrt (by positivity)) ?_ ?_
  · exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  · exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _

end Commons.Analysis.Calculus