import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Homogeneity of `HkNorm` in a scalar amplitude

For `c ≥ 0` the weighted `H^k` norm `HkNorm A k` is positively homogeneous of degree one:
`HkNorm A k (fun z θ => c * f z θ) = c * HkNorm A k f`.

Every operator entering the weighted `H^k` integrand (`pz`, `pth`, `Dz`, `Dth`, `DzIter`,
`DthIter`, `mixed`) is linear over the reals, so `HkIntegrand A k` is homogeneous of degree
two in the amplitude and hence so is `HkSq A k` (the Bochner integral is scalar homogeneous
*unconditionally*).  The square root then splits the factor `c²` into `|c| = c`.

No regularity hypothesis on `f` is needed: `deriv` is homogeneous for scalar multiplication
unconditionally (if `f` is not differentiable at a point and `c ≠ 0`, neither is `c * f`), and
the total Bochner integral is homogeneous without any integrability assumption.  In particular
the irrelevant region `z < 0` causes no trouble.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory

namespace Work.R1G

set_option autoImplicit false

/-! ## Unconditional `deriv`-linearity -/

/-- `deriv` is scalar homogeneous **unconditionally**, unlike Mathlib's `deriv_const_mul`,
which needs differentiability: if `f` is not differentiable at `x` then neither is `c * f`
for `c ≠ 0`, so both sides are `0`. -/
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
private theorem HkIntegrand_const_mul (A : ℝ) (k : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkIntegrand A k (fun z θ => c * f z θ)
      = fun z θ => c ^ 2 * Work.Spaces.HkIntegrand A k f z θ := by
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
          then (c * Work.Spaces.mixed j i f z θ * Work.Spaces.Wt A z θ) ^ 2 else 0)
      = c ^ 2 * ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt A z θ) ^ 2 else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by split_ifs with h <;> ring
  rw [h1, h2, mul_add]

/-- `HkSq` is homogeneous of degree two in the amplitude.  Neither integral needs an
integrability hypothesis: `MeasureTheory.integral_const_mul` is unconditional. -/
private theorem HkSq_const_mul (A c : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq A k (fun z θ => c * f z θ) = c ^ 2 * Work.Spaces.HkSq A k f := by
  simp only [Work.Spaces.HkSq, HkIntegrand_const_mul]
  simp only [MeasureTheory.integral_const_mul]

/-! ## The requested homogeneity of `HkNorm` -/

theorem HkNorm_const_mul (A c : ℝ) (hc : 0 ≤ c) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkNorm A k (fun z θ => c * f z θ) = c * Work.Spaces.HkNorm A k f := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, HkSq_const_mul A c k f,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

end Work.R1G
