/-
# Homogeneity of the weighted `H^k` integrand in the amplitude

`HkIntegrand α k (fun z θ => β * f z θ) z θ = β^2 * HkIntegrand α k f z θ`: the integrand is a
sum of squares of expressions that are *linear* in `f`, so it is homogeneous of degree two.

The only ingredient is that every operator occurring in `HkIntegrand` (`pz`, `pth`, `Dz`, `Dth`,
their iterates, and `mixed = D_z^j ∘ D_θ^i`) commutes with multiplication by a constant.
This holds **unconditionally** — no regularity hypothesis on `f` is needed — because `deriv`
commutes with scalar multiplication without differentiability assumptions (if `f` is not
differentiable at `x`, then neither is `β * f` for `β ≠ 0`, and both sides are `0`).  Compare
`Work.R1G.HkNorm_const_mul`, where the same computation is carried out to the level of
`HkNorm`.

Remark: at `k = 0` the second sum of `HkIntegrand` is empty (`1 ≤ i` fails), so the second
block vanishes; the case analysis below handles it uniformly.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.LocData.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.LocData

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

/-! ## The requested pointwise homogeneity -/

theorem HkIntegrand_const_mul (α : ℝ) (k : ℕ) (β : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (fun z θ => β * f z θ) z θ
      = β ^ 2 * Work.Spaces.HkIntegrand α k f z θ := by
  simp only [Work.Spaces.HkIntegrand, DzIter_const_mul, mixed_const_mul]
  have h1 : (∑ i ∈ Finset.range (k + 1),
        (β * Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = β ^ 2 * ∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (β * Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
      = β ^ 2 * ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by split_ifs with h <;> ring
  rw [h1, h2, mul_add]

end Work.FTS.LocData
