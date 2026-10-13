import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.HkMem_mono

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ℋ^k` is closed under scalar multiplication

`Work.Spaces.HkMem α k f` says that the weighted `H^k`-integrand of `f` has honest
iterated integrals over `[0,∞) × [0,π/2]`.  Here we prove that the class is closed under
`f ↦ c · f` for every `c : ℝ`.

The point is that every weighted derivative appearing in `Work.Spaces.HkIntegrand` is
`ℝ`-linear in `f` (`D_z^i` and `D_z^j D_θ^i` are built from `deriv`, which is scalar
homogeneous *unconditionally*, see `deriv_const_mul_field`), so that

  `HkIntegrand α k (c·f) z θ = c^2 * HkIntegrand α k f z θ`.

Both membership clauses are then immediate from the corresponding clauses for `f`
(pulling `c^2` out of the angular integral with `MeasureTheory.integral_const_mul`).

In particular no smoothness hypothesis is needed for this statement; the `SmoothNbhd`
hypothesis of the requested signature is simply not used.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep.Norm

set_option autoImplicit false

/-! ## Scalar homogeneity of the weighted derivatives -/

/-- `∂_z` is scalar homogeneous: unconditional, since `deriv` is. -/
private theorem pz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pz f z θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  exact deriv_const_mul_field c

/-- `∂_θ` is scalar homogeneous. -/
private theorem pth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  exact deriv_const_mul_field c

/-- `D_z = z ∂_z` is scalar homogeneous. -/
private theorem Dz_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dz f z θ := by
  funext z θ
  simp only [Work.Spaces.Dz, pz_const_mul]
  ring

/-- `D_θ = sin(2θ) ∂_θ` is scalar homogeneous. -/
private theorem Dth_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.Dth f z θ := by
  funext z θ
  simp only [Work.Spaces.Dth, pth_const_mul]
  ring

/-- Iterated `D_z` is scalar homogeneous. -/
private theorem DzIter_const_mul (c : ℝ) (j : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DzIter j f z θ := by
  induction j with
  | zero => rfl
  | succ n ih => simp only [Work.Spaces.DzIter_succ, ih, Dz_const_mul]

/-- Iterated `D_θ` is scalar homogeneous. -/
private theorem DthIter_const_mul (c : ℝ) (i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ n ih => simp only [Work.Spaces.DthIter_succ, ih, Dth_const_mul]

/-- The mixed derivative `D_z^j D_θ^i` is scalar homogeneous. -/
private theorem mixed_const_mul (c : ℝ) (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.mixed j i f z θ := by
  simp only [Work.Spaces.mixed, DthIter_const_mul, DzIter_const_mul]

/-! ## Homogeneity of the weighted `H^k`-integrand -/

/-- The weighted `H^k`-integrand is homogeneous of degree `2` in the amplitude. -/
private theorem HkIntegrand_const_mul (A : ℝ) (c : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand A k (fun z θ => c * f z θ) z θ
      = c ^ 2 * Work.Spaces.HkIntegrand A k f z θ := by
  rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand]
  have h1 : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => c * f z θ) z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      = c ^ 2 * ∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [DzIter_const_mul]
    ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (fun z θ => c * f z θ) z θ * Work.Spaces.Wt A z θ) ^ 2
          else 0)
      = c ^ 2 * ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt A z θ) ^ 2 else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : 1 ≤ i ∧ i + j ≤ k
    · rw [ite_eq_left h, ite_eq_left h, mixed_const_mul]
      ring
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  rw [h1, h2]
  ring

/-! ## Closure of `ℋ^k` under scalar multiplication -/

theorem HkMem_const_mul (α : ℝ) (k : ℕ) (c : ℝ) {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (hmf : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (fun z θ => c * f z θ) := by
  -- the smoothness of `f` is not needed: `deriv` is scalar homogeneous unconditionally
  have _hf : Work.Spaces.SmoothNbhd f := hf
  refine ⟨fun z hz => ?_, ?_⟩
  · -- angular slice: pull the constant `c^2` out of the integrand
    have h := (hmf.1 z hz).const_mul (c ^ 2)
    simpa only [HkIntegrand_const_mul, IntegrableOn] using h
  · -- radial integral: the inner integral is `c^2` times the inner integral for `f`
    have h := (hmf.2).const_mul (c ^ 2)
    simpa only [HkIntegrand_const_mul, integral_const_mul, IntegrableOn] using h

end Work.FTS.CoercivityStep.Norm
