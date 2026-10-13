import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.R1G.GTest

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Homogeneity of `HkNorm` in the amplitude of the visible test perturbation

The visible test perturbation `gTest c = c·z²e^{-z}·sin(2θ)` (`Work.R1G.GTest`) is the scalar
multiple `c • gTest 1` of the normalised one.  Since every operator entering the weighted `H^k`
integrand (`pz`, `pth`, `Dz`, `Dth`, `DzIter`, `DthIter`, `mixed`) is linear, the integrand
`HkIntegrand α k` is homogeneous of degree two in the amplitude, hence so is `HkSq`, and therefore
`HkNorm α 2 (gTest c) = c · HkNorm α 2 (gTest 1)` for `c ≥ 0` (the square root kills the sign, and
`|c| = c`).  This is the estimate requested here.

The proof is purely algebraic: the homogeneity of the integrand is proved for an arbitrary
`f : ℝ → ℝ → ℝ` (so it applies to any scalar multiple), and the two Lebesgue integrals are pulled
apart with `MeasureTheory.integral_const_mul`.
-/

namespace Work.R1G

/-! ## Unconditional `deriv`-linearity

`deriv_const_mul` in Mathlib needs differentiability; the statement below holds *unconditionally*,
because `deriv` is `0` at non-differentiable points (and if `fun y => c * f y` were differentiable
at a point where `f` is not, then `c ≠ 0` would make `f` differentiable there too).  This is what
lets the homogeneity of the integrand be proved without any regularity hypothesis on `f` (in
particular the `z < 0` region, which is irrelevant to the norms but still present in the
definitions, causes no trouble). -/

private theorem deriv_const_mul_uncond (c x : ℝ) (f : ℝ → ℝ) :
    deriv (fun y => c * f y) x = c * deriv f x := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ f x) with hf | hf
    · exact deriv_const_mul c hf
    · have h2 : ¬ DifferentiableAt ℝ (fun y => c * f y) x := by
        intro hh
        apply hf
        have he : f = fun y => c⁻¹ * (c * f y) := by
          funext y; rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
        rw [he]
        exact hh.const_mul c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf,
        deriv_zero_of_not_differentiableAt h2, mul_zero]

/-! ## Pointwise linearity of the differential operators -/

private theorem pz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pz f z θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  rw [deriv_const_mul_uncond]

private theorem Dz_const_mul (c : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => c * g z θ) = fun z θ => c * Work.Spaces.Dz g z θ := by
  funext z θ
  simp only [Work.Spaces.Dz]
  rw [pz_const_mul]
  ring

private theorem pth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  rw [deriv_const_mul_uncond]

private theorem Dth_const_mul (c : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => c * g z θ) = fun z θ => c * Work.Spaces.Dth g z θ := by
  funext z θ
  simp only [Work.Spaces.Dth]
  rw [pth_const_mul]
  ring

private theorem DzIter_const_mul (i : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DzIter i f z θ := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [Work.Spaces.DzIter_succ, ih, Dz_const_mul]

private theorem DthIter_const_mul (i : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [Work.Spaces.DthIter_succ, ih, Dth_const_mul]

private theorem mixed_const_mul (j i : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.mixed j i f z θ := by
  simp only [Work.Spaces.mixed, DthIter_const_mul, DzIter_const_mul]

/-! ## Homogeneity of the weighted integrand and of `HkSq` -/

/-- The weighted `H^k` integrand is homogeneous of degree two in the amplitude. -/
private theorem HkIntegrand_const_mul (α : ℝ) (k : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ)
      = fun z θ => c ^ 2 * Work.Spaces.HkIntegrand α k f z θ := by
  funext z θ
  simp only [Work.Spaces.HkIntegrand, DzIter_const_mul, mixed_const_mul]
  have h1 : (∑ i ∈ Finset.range (k + 1),
        (c * Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = c ^ 2 * ∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (c * Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
      = c ^ 2 * ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by split_ifs with h <;> ring
  rw [h1, h2, mul_add]

/-- `gTest c` is the scalar multiple `c • gTest 1` of the normalised perturbation. -/
private theorem gTest_eq_const_mul (c : ℝ) :
    gTest c = fun z θ => c * gTest 1 z θ := by
  funext z θ
  rw [gTest_apply, gTest_apply]
  ring

/-- `HkSq` of the test perturbation is homogeneous of degree two in the amplitude. -/
private theorem HkSq_gTest_const_mul (α c : ℝ) :
    Work.Spaces.HkSq α 2 (gTest c) = c ^ 2 * Work.Spaces.HkSq α 2 (gTest 1) := by
  simp only [Work.Spaces.HkSq, gTest_eq_const_mul c, HkIntegrand_const_mul]
  simp only [MeasureTheory.integral_const_mul]

/-! ## The requested estimate -/

theorem hkNorm_gTest_le (α : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    Work.Spaces.HkNorm α 2 (gTest c) ≤ c * Work.Spaces.HkNorm α 2 (gTest 1) := by
  have hsq := HkSq_gTest_const_mul α c
  have heq : Work.Spaces.HkNorm α 2 (gTest c) = c * Work.Spaces.HkNorm α 2 (gTest 1) := by
    rw [Work.Spaces.HkNorm, hsq, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc,
      Work.Spaces.HkNorm]
  exact le_of_eq heq

end Work.R1G
