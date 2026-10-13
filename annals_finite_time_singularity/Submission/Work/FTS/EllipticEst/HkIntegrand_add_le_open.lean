/-
Copyright: work module for the Elgindi finite-time singularity project.

# Subadditivity of the `ℋ^k`-integrand on the open quadrant

`Work.Spaces.HkIntegrand α k f z θ` is the sum of the squares of the weighted derivatives of `f`
(two blocks: the `D_z`-block and the `D_z^j D_θ^i`-block, with `i ≥ 1`).  The `D`-operators are
linear on the open quadrant `Q0 = (0,∞) × (0,π/2)` where the data are differentiable
(`Work.FTS.EllipticEst.SmoothOpen.DzIter_add`, `SmoothOpen.mixed_add`), so at an interior point
of the domain termwise `(a + b)² ≤ 2a² + 2b²` gives

`HkIntegrand α k (f+g) z θ ≤ 2 · HkIntegrand α k f z θ + 2 · HkIntegrand α k g z θ`.

The boundary lines `z = 0` and `sin(2θ) = 0` of the domain `Iz ×ˢ Iθ = [0,∞) × [0,π/2]` need
separate treatment and are trivial there:

* at `z = 0` the weight `w 0 = (1+0)²/0² = 0` (Lean's totalised division) kills the integrand
  (`Work.FTS.LocData.HkIntegrand_zero_fst`);
* at `sin(2θ) = 0` the first block is killed by `1/0 = 0` and, in the second block, the surviving
  indices all have `i ≥ 1`, so each summand carries at least one factor `D_θ`, hence `sin(2θ) = 0`
  (`Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero`).

Together with the nonnegativity of the integrand (`Work.Spaces.HkIntegrand_nonneg`), this gives
the bound at every point of `Iz ×ˢ Iθ`.

This is the open-quadrant analogue of `Work.FTS.LocData.HkIntegrand_add_le` (which is stated for
data smooth on the *bigger* strip `z > -1`) and is the input of the closure of `ℋ^k` under
addition for `SmoothOpen` data (`Work.FTS.EllipticEst.HkMem_add_smoothOpen`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.Coercivity.HkIntegrand_endpoint_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## The algebraic core: sums of squares of sums -/

private lemma sum_sq_add_le {ι : Type*} (s : Finset ι) (x y : ι → ℝ) :
    (∑ i ∈ s, (x i + y i) ^ 2) ≤ 2 * (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, y i ^ 2) := by
  calc (∑ i ∈ s, (x i + y i) ^ 2)
      ≤ ∑ i ∈ s, (2 * x i ^ 2 + 2 * y i ^ 2) :=
        Finset.sum_le_sum fun i _ => by
          have h := add_sq_le (a := x i) (b := y i); linarith
    _ = 2 * (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, y i ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The pointwise inequality for the integrand, given the additivity of the iterated operators
at `(z, θ)`. -/
private lemma HkIntegrand_add_le_pt (α : ℝ) (k : ℕ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hz : ∀ i, Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.DzIter i f z θ + Work.Spaces.DzIter i g z θ)
    (hm : ∀ i j, Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ) :
    Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α k f z θ
        + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  have hZ : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    have h1 : (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = ∑ i ∈ Finset.range (k + 1),
          ((Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
            + (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hz i]; ring
    rw [h1]
    exact sum_sq_add_le _ _ _
  have hM : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
    set S : Finset (ℕ × ℕ) := ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
      (fun p => 1 ≤ p.1 ∧ p.1 + p.2 ≤ k) with hS
    have e : ∀ u : ℝ → ℝ → ℝ,
        (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i u z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          = ∑ p ∈ S, (Work.Spaces.mixed p.2 p.1 u z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      intro u
      rw [hS, Finset.sum_filter, Finset.sum_product]
    rw [e f, e g, e (fun z θ => f z θ + g z θ)]
    have hconv : (∑ p ∈ S,
          (Work.Spaces.mixed p.2 p.1 (fun z θ => f z θ + g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2)
        = ∑ p ∈ S, ((Work.Spaces.mixed p.2 p.1 f z θ * Work.Spaces.Wt α z θ)
            + (Work.Spaces.mixed p.2 p.1 g z θ * Work.Spaces.Wt α z θ)) ^ 2 := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hm p.1 p.2]; ring
    rw [hconv]
    exact sum_sq_add_le _ _ _
  simp only [Work.Spaces.HkIntegrand]
  linarith [hZ, hM]

/-! ## The theorem -/

/-- **Subadditivity of the `ℋ^k`-integrand for `SmoothOpen` data.**  For `f`, `g` of class
`C^∞` on the open quadrant `(0,∞) × (0,π/2)` and every `(z,θ) ∈ Iz ×ˢ Iθ`,

`HkIntegrand α k (f+g) z θ ≤ 2 · HkIntegrand α k f z θ + 2 · HkIntegrand α k g z θ`. -/
theorem HkIntegrand_add_le_open (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : SmoothOpen f) (hg : SmoothOpen g) {z : ℝ} (hz : z ∈ Work.Spaces.Iz)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α k f z θ
        + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  by_cases hz0 : z = 0
  · -- `z = 0`: the integrand vanishes identically
    rw [hz0, Work.FTS.LocData.HkIntegrand_zero_fst]
    have h1 := Work.Spaces.HkIntegrand_nonneg α k f 0 θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α k g 0 θ
    linarith
  by_cases hs : Real.sin (2 * θ) = 0
  · -- `sin (2θ) = 0`: the integrand vanishes identically
    rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k
      (fun z θ => f z θ + g z θ) z θ hs]
    have h1 := Work.Spaces.HkIntegrand_nonneg α k f z θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α k g z θ
    linarith
  · -- interior point of the quadrant: additivity of the `D`-operators plus the algebra
    have hzge : 0 ≤ z := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hz
    have hzpos : 0 < z := lt_of_le_of_ne hzge (Ne.symm hz0)
    have hbnd : 0 ≤ θ ∧ θ ≤ π / 2 := by
      simpa only [Work.Spaces.Iθ, Set.mem_Icc] using hθ
    have hθ1 : 0 < θ := by
      rcases eq_or_lt_of_le hbnd.1 with h | h
      · exact absurd (by rw [← h]; simp) hs
      · exact h
    have hθ2 : θ < π / 2 := by
      rcases lt_or_eq_of_le hbnd.2 with h | h
      · exact h
      · exact absurd (by rw [h, show (2 : ℝ) * (π / 2) = π from by ring, Real.sin_pi]) hs
    exact HkIntegrand_add_le_pt α k f g z θ
      (fun i => SmoothOpen.DzIter_add hf hg i z θ hzpos hθ1 hθ2)
      (fun i j => SmoothOpen.mixed_add hf hg j i z θ hzpos hθ1 hθ2)

end Work.FTS.EllipticEst
