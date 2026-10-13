/-
# `Work.FTS.LocData.HkMem_const_mul`

**Scalar multiplication preserves `ℋ^k`**: if `f ∈ ℋ^k` (`Work.Spaces.HkMem α k f`) then so is
`fun z θ => β * f z θ`, for every real `β`.

This is the scalar-linearity of the space `ℋ^k` of the paper, in the *unconditional* form:
no smoothness of `f` is required.  The reason is that `deriv` is linear over constants
without any differentiability hypothesis (`deriv_const_mul_field`, valid because the junk
value of `deriv` at a non-differentiable point is `0`), so each `D_z`/`D_θ`-derivative of the
scalar multiple is the scalar multiple of the derivative, and hence the whole
`ℋ^k`-integrand is simply multiplied by `β²`:

`HkIntegrand α k (β·f) z θ = β² · HkIntegrand α k f z θ`   (`hkIntegrand_const_mul`).

Both halves of the `HkMem` certificate then transfer by `Integrable.const_mul` and
`integral_const_mul`.

(The sibling modules of this chapter phrase the same fact for a *smooth* `f` with an extra
`SmoothNbhd` hypothesis; as shown here that hypothesis is unnecessary.)
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

set_option autoImplicit false

/-! ## The pointwise calculus: `D_z`, `D_θ` and their iterates commute with a scalar -/

/-- `D_z (β·g) = β·(D_z g)`: multiplication by a constant commutes with `D_z = z ∂_z`.
No differentiability of `g` is needed, `deriv` being linear over constants. -/
theorem Dz_const_mul (β : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => β * g z θ) = fun z θ => β * Work.Spaces.Dz g z θ := by
  funext z θ
  simp only [Work.Spaces.Dz, Work.Spaces.pz, deriv_const_mul_field]
  ring

/-- `D_θ (β·g) = β·(D_θ g)`: multiplication by a constant commutes with
`D_θ = sin(2θ) ∂_θ`.  No differentiability of `g` is needed. -/
theorem Dth_const_mul (β : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => β * g z θ) = fun z θ => β * Work.Spaces.Dth g z θ := by
  funext z θ
  simp only [Work.Spaces.Dth, Work.Spaces.pth, deriv_const_mul_field]
  ring

/-- `D_z^i (β·g) = β·(D_z^i g)`. -/
theorem DzIter_const_mul (β : ℝ) (i : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (fun z θ => β * g z θ)
      = fun z θ => β * Work.Spaces.DzIter i g z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      exact Dz_const_mul β _

/-- `D_θ^i (β·g) = β·(D_θ^i g)`. -/
theorem DthIter_const_mul (β : ℝ) (i : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => β * g z θ)
      = fun z θ => β * Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      exact Dth_const_mul β _

/-- `D_z^j D_θ^i (β·g) = β·(D_z^j D_θ^i g)`, i.e. the mixed operators of `HkIntegrand`
commute with a scalar. -/
theorem mixed_const_mul (β : ℝ) (j i : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => β * g z θ)
      = fun z θ => β * Work.Spaces.mixed j i g z θ := by
  rw [Work.Spaces.mixed, Work.Spaces.mixed, DthIter_const_mul, DzIter_const_mul]

/-! ## The `ℋ^k`-integrand of a scalar multiple -/

/-- The `ℋ^k`-integrand scales by `β²`:
`HkIntegrand α k (β·f) z θ = β² · HkIntegrand α k f z θ`.

Every summand of `HkIntegrand` is the square of a weighted derivative, and each weighted
derivative of `β·f` is `β` times the corresponding derivative of `f`
(`DzIter_const_mul`, `mixed_const_mul`); the weights `w z / sin(2θ)^{η/2}`, `Wt α z θ` do not
depend on `f`. -/
theorem hkIntegrand_const_mul (α : ℝ) (k : ℕ) (β : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (fun z θ => β * f z θ) z θ
      = β ^ 2 * Work.Spaces.HkIntegrand α k f z θ := by
  rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand]
  simp only [DzIter_const_mul, mixed_const_mul]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hp : (1 ≤ i ∧ i + j ≤ k)
    · simp [hp]; ring
    · simp [hp]

/-! ## The main result -/

/-- **`ℋ^k` is closed under scalar multiplication.**  If `f ∈ ℋ^k` then `β·f ∈ ℋ^k` for every
`β : ℝ`.

Both integrability requirements transfer from `f` to `β·f` because the corresponding
`ℋ^k`-integrands differ by the constant factor `β²` (`hkIntegrand_const_mul`):
the angular slices by `Integrable.const_mul`, and the outer `z`-integral by
`integral_const_mul` followed by `Integrable.const_mul`. -/
theorem HkMem_const_mul (α : ℝ) (k : ℕ) (β : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (fun z θ => β * f z θ) := by
  constructor
  · intro z hz
    have h := hf.1 z hz
    rw [funext (fun θ => hkIntegrand_const_mul α k β f z θ)]
    exact h.const_mul _
  · have h := hf.2
    have key : (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => β * f z θ) z θ)
        = fun z => β ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
      funext z
      simp only [hkIntegrand_const_mul]
      rw [integral_const_mul]
    rw [key]
    exact h.const_mul _

end Work.FTS.LocData
