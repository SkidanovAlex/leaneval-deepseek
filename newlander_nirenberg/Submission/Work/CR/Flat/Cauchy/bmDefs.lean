/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The Bochner–Martinelli kernel on `ℂⁿ`

This file sets up the kernel of the Bochner–Martinelli potential, the classical solution of the
flat `∂̄`-equation with a gain of one derivative:

  `u(z) = c_n Σ_j (-1)^{j-1} ∫ \overline{ζ_j - z_j} f_j(ζ) / ‖ζ - z‖^{2n} dζ`.

The kernel `bmKernel j x = \overline{x_j} / ‖x‖^{2n}` (with `‖·‖` the *Euclidean* norm on
`ℂⁿ = Fin n → ℂ`) is homogeneous of degree `1 - 2n`, so its first derivatives are homogeneous of
degree `-2n = -dim`; their mean over spheres vanishes, which is what makes the derivative of the
potential a Calderón–Zygmund singular integral controlled by `‖f‖_{C^{0,α}}`.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

/-- The Euclidean norm on `ℂⁿ = Fin n → ℂ`, as a real number. -/
noncomputable def eucNorm {n : ℕ} (x : Fin n → ℂ) : ℝ := Real.sqrt (∑ j, ‖x j‖ ^ 2)

@[simp] lemma eucNorm_zero {n : ℕ} : eucNorm (0 : Fin n → ℂ) = 0 := by
  simp [eucNorm]

lemma eucNorm_nonneg {n : ℕ} (x : Fin n → ℂ) : 0 ≤ eucNorm x := Real.sqrt_nonneg _

lemma eucNorm_pos {n : ℕ} {x : Fin n → ℂ} (hx : x ≠ 0) : 0 < eucNorm x := by
  have hex : ∃ i ∈ (Finset.univ : Finset (Fin n)), 0 < ‖x i‖ ^ 2 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
    exact ⟨j, Finset.mem_univ j, by rw [pow_two]; exact mul_self_pos.mpr (norm_pos_iff.mpr hj).ne'⟩
  rw [eucNorm, Real.sqrt_pos]
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) hex

lemma eucNorm_eq_zero {n : ℕ} {x : Fin n → ℂ} : eucNorm x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  by_contra hx
  exact absurd h (ne_of_gt (eucNorm_pos hx))

lemma eucNorm_sq {n : ℕ} (x : Fin n → ℂ) : eucNorm x ^ 2 = ∑ j, ‖x j‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma continuous_eucNorm {n : ℕ} : Continuous (fun x : Fin n → ℂ => eucNorm x) := by
  have h : Continuous fun x : Fin n → ℂ => Real.sqrt (∑ j, ‖x j‖ ^ 2) :=
    (continuous_finsetSum _ fun j _ => ((continuous_apply j).norm).pow 2).sqrt
  simpa [eucNorm] using h

/-- The Bochner–Martinelli kernel component `j`: `\bar x_j / ‖x‖^{2n}`. -/
noncomputable def bmKernel {n : ℕ} (j : Fin n) (x : Fin n → ℂ) : ℂ :=
  starRingEnd ℂ (x j) / (eucNorm x : ℂ) ^ (2 * n)

/-- The Bochner–Martinelli potential of a family `f` of functions (a `(0,1)`-form
`Σ_j f_j d\bar z_j`). -/
noncomputable def bmPotential {n : ℕ} (f : Fin n → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : ℂ :=
  ∑ j, ∫ ζ, bmKernel j (ζ - z) * f j ζ

end Work.CR.Flat.Cauchy
