/-
Copyright: work module for the Elgindi finite-time singularity project.

# Scalar homogeneity of the weighted `H^k`-norm

The `H^k`-norm of the paper is `sqrt (HkSq α k f)` where `HkSq` is the double integral
(over `[0,∞) × [0,π/2]` with the measure `dz dθ`) of a sum of squares of weighted
derivatives `D_z^j f`, `D_z^j D_θ^i f`.  Every one of the operators involved
(`D_z = z ∂_z`, `D_θ = sin(2θ) ∂_θ`, their iterates and the mixed operators) is
`ℝ`-homogeneous of degree `1`, hence the integrand is homogeneous of degree `2` and
the norm is absolutely homogeneous:

  `HkNorm α k (c · f) = |c| * HkNorm α k f`.

Note that no smoothness of `f` is needed: the one-dimensional constant-multiple rule
for `deriv` is available without a differentiability assumption (`deriv_const_mul_field`),
and the Bochner integral is linear for constants without an integrability assumption
(`MeasureTheory.integral_const_mul`).  The smoothness hypothesis `hf` of the statement
is therefore carried along unused (it is part of the interface the caller relies on).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst

open Work.Spaces

/-! ## Scalar homogeneity of the differential operators -/

private theorem pz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    pz (fun z θ => c * f z θ) = fun z θ => c * pz f z θ := by
  funext z θ
  simp only [pz]
  exact deriv_const_mul_field c

private theorem pth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    pth (fun z θ => c * f z θ) = fun z θ => c * pth f z θ := by
  funext z θ
  simp only [pth]
  exact deriv_const_mul_field c

private theorem Dz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Dz (fun z θ => c * f z θ) = fun z θ => c * Dz f z θ := by
  funext z θ
  simp only [Dz, pz_const_mul]
  ring

private theorem Dth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Dth (fun z θ => c * f z θ) = fun z θ => c * Dth f z θ := by
  funext z θ
  simp only [Dth, pth_const_mul]
  ring

private theorem DzIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (n : ℕ) :
    DzIter n (fun z θ => c * f z θ) = fun z θ => c * DzIter n f z θ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Dz (DzIter n (fun z θ => c * f z θ)) = fun z θ => c * Dz (DzIter n f) z θ
    rw [ih]
    funext z θ
    simp only [Dz, pz_const_mul]
    ring

private theorem DthIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (n : ℕ) :
    DthIter n (fun z θ => c * f z θ) = fun z θ => c * DthIter n f z θ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Dth (DthIter n (fun z θ => c * f z θ)) = fun z θ => c * Dth (DthIter n f) z θ
    rw [ih]
    funext z θ
    simp only [Dth, pth_const_mul]
    ring

private theorem mixed_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) :
    mixed j i (fun z θ => c * f z θ) = fun z θ => c * mixed j i f z θ := by
  show DzIter j (DthIter i (fun z θ => c * f z θ))
    = fun z θ => c * DzIter j (DthIter i f) z θ
  rw [DthIter_const_mul, DzIter_const_mul]

/-! ## Homogeneity of the integrand and of the squared norm -/

/-- The weighted `H^k`-integrand is homogeneous of degree `2` in the amplitude. -/
private theorem HkIntegrand_const_mul (α : ℝ) (k : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    HkIntegrand α k (fun z θ => c * f z θ) z θ = c ^ 2 * HkIntegrand α k f z θ := by
  unfold HkIntegrand
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [DzIter_const_mul]
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [mixed_const_mul]
    split_ifs <;> ring

/-- The squared `H^k`-norm is homogeneous of degree `2` in the amplitude. -/
private theorem HkSq_const_mul (α : ℝ) (k : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    HkSq α k (fun z θ => c * f z θ) = c ^ 2 * HkSq α k f := by
  unfold HkSq
  simp only [HkIntegrand_const_mul]
  have hinner : ∀ z, (∫ θ in Iθ, c ^ 2 * HkIntegrand α k f z θ)
      = c ^ 2 * ∫ θ in Iθ, HkIntegrand α k f z θ :=
    fun z => integral_const_mul _ _
  simp only [hinner]
  rw [integral_const_mul]

/-! ## The `H^k`-norm is absolutely homogeneous -/

set_option linter.unusedVariables false in
theorem HkNorm_const_mul (α : ℝ) (k : ℕ) (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    Work.Spaces.HkNorm α k (fun z θ => c * f z θ) = |c| * Work.Spaces.HkNorm α k f := by
  unfold HkNorm
  rw [HkSq_const_mul]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

end Work.FTS.EllipticEst
