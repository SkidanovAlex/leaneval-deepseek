import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Galerkin.Hilbert

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Scalar homogeneity of the weighted `ℋ^k`-integrand

The whole content is that `HkIntegrand` is a sum of squares of expressions that are *linear* in
`f`, so it is homogeneous of degree two: `HkIntegrand α k (c·f) = c² · HkIntegrand α k f`.
The operators appearing in `HkIntegrand` (`pz`, `pth`, `Dz`, `Dth`, their iterates, and
`mixed = D_z^j ∘ D_θ^i`) all commute with multiplication by a constant, and this commutation is
**unconditional**: `deriv` is scalar homogeneous with no differentiability hypothesis (if `f` is
not differentiable at `x` then neither is `c * f` for `c ≠ 0`, and both sides are `0`).  In
particular the smoothness hypothesis `SmoothNbhd f` of the main theorem is not needed here.
-/

/-- `deriv` is scalar homogeneous **unconditionally**, unlike Mathlib's `deriv_const_mul`
(which assumes `DifferentiableAt`). -/
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

private theorem pz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pz f z θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  rw [deriv_const_mul_uncond]

private theorem pth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  rw [deriv_const_mul_uncond]

private theorem Dz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dz f z θ := by
  funext z θ
  simp only [Work.Spaces.Dz, pz_const_mul]
  ring

private theorem Dth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dth f z θ := by
  funext z θ
  simp only [Work.Spaces.Dth, pth_const_mul]
  ring

private theorem DzIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DzIter i (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.DzIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_succ, ih, Dz_const_mul]

private theorem DthIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DthIter_succ, Work.Spaces.DthIter_succ, ih, Dth_const_mul]

private theorem mixed_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.mixed j i f z θ := by
  simp only [Work.Spaces.mixed, DthIter_const_mul, DzIter_const_mul]

/-- **The weighted `ℋ^k`-integrand is homogeneous of degree two in the amplitude:**
`HkIntegrand α k (c·f) z θ = c² · HkIntegrand α k f z θ`, for every `c : ℝ` and every `f`
(no regularity on `f` is needed). -/
theorem HkIntegrand_const_mul (α : ℝ) (k : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ
      = c ^ 2 * Work.Spaces.HkIntegrand α k f z θ := by
  rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [DzIter_const_mul]
    ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mixed_const_mul]
    split_ifs with h <;> ring

/-- **`ℋ^k` is closed under scalar multiplication.** If `f` is smooth on a neighbourhood of the
closed quadrant and in `ℋ^k`, then so is `c * f` for every `c : ℝ`.

Intended proof: for smooth `f` one has `DzIter i (c*f) = c * DzIter i f` and
`mixed j i (c*f) = c * mixed j i f`, whence `HkIntegrand α k (c*f) z θ = c^2 * HkIntegrand α k f z θ`
pointwise; the integral of `c^2 * ·` is `c^2 * ∫ ·`, giving the two membership clauses of `HkMem`. -/
theorem HkMem_const_mul {α : ℝ} {k : ℕ} (c : ℝ) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.Spaces.SmoothNbhd f) (hmf : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (fun z θ => c * f z θ) := by
  obtain ⟨h1, h2⟩ := hmf
  constructor
  · -- the `θ`-slices of the integrand are integrable, being `c²` times the slices of `f`
    intro z hz
    have hfun : (fun θ => Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
        = fun θ => c ^ 2 * Work.Spaces.HkIntegrand α k f z θ :=
      funext fun θ => HkIntegrand_const_mul α k c f z θ
    rw [hfun]
    exact (h1 z hz).const_mul _
  · -- the `z`-slices of the iterated integral are integrable, being `c²` times those of `f`
    have hfun : (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
        = fun z => c ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
      funext z
      rw [show (fun θ => Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
            = fun θ => c ^ 2 * Work.Spaces.HkIntegrand α k f z θ from
          funext fun θ => HkIntegrand_const_mul α k c f z θ]
      rw [MeasureTheory.integral_const_mul]
    rw [hfun]
    exact h2.const_mul _

end

end Work.FTS.Galerkin.Hilbert
