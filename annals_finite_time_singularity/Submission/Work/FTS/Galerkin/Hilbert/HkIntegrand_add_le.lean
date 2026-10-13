import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Coercivity.E2Mixed.E2model_mixed_split
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.Galerkin.Hilbert

/-- **Pointwise subadditivity of the `ℋ^k` integrand.**  For `f`, `g` smooth on an open
neighbourhood of the closed quadrant `[0,∞) × [0,π/2]`, the weighted `ℋ^k` integrand of
`f + g` is pointwise bounded by twice the sum of the integrands of `f` and `g` at every point
of the closed quadrant.

Intended proof: on `nbhU = (-1,∞) × (-1,π/2+1)` the iterated operators are additive,
`DzIter i (f+g) = DzIter i f + DzIter i g` and `mixed j i (f+g) = mixed j i f + mixed j i g`
(`Work.Coercivity.E2Mixed.DzIter_add_of_isOpen`, `...DthIter_add_of_isOpen`,
`...mixed_add_of_isOpen`, with `V = nbhU`); then each summand of the integrand satisfies
`(a + b)^2 ≤ 2 a^2 + 2 b^2`, and summing (including the `if`-filtered double sum, rewritten as
a sum over `((range (k+1)) ×ˢ (range (k+1))).filter (fun p => 1 ≤ p.1 ∧ p.1 + p.2 ≤ k)`)
gives the claim.  Every point of `Iz × Iθ` lies in `nbhU` (`Work.Spaces.mem_nbhU`). -/
theorem HkIntegrand_add_le {α : ℝ} {k : ℕ} {f g : Work.FTS.Galerkin.Fn}
    (hf : Work.Spaces.SmoothNbhd f) (hg : Work.Spaces.SmoothNbhd g) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
        ≤ 2 * (Work.Spaces.HkIntegrand α k f z θ + Work.Spaces.HkIntegrand α k g z θ) := by
  intro z hz θ hθ
  -- every point of the closed quadrant lies in the open neighbourhood on which `SmoothNbhd` lives
  have hy : (z, θ) ∈ Work.Spaces.nbhU := Work.Spaces.mem_nbhU hz hθ
  -- the iterated operators are additive at `(z,θ)`
  have hDz : ∀ i : ℕ, Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.DzIter i f z θ + Work.Spaces.DzIter i g z θ := fun i =>
    Work.Coercivity.E2Mixed.DzIter_add_of_isOpen Work.Spaces.isOpen_nbhU hf hg i hy
  have hMixed : ∀ j i : ℕ, Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ := fun j i =>
    Work.Coercivity.E2Mixed.mixed_add_of_isOpen Work.Spaces.isOpen_nbhU hf hg j i hy
  simp only [Work.Spaces.HkIntegrand]
  -- the pure `D_z` sum
  have hZ : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + 2 * (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    calc (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ i ∈ Finset.range (k + 1),
            (2 * (Work.Spaces.DzIter i f z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
              + 2 * (Work.Spaces.DzIter i g z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [hDz i]
          nlinarith [sq_nonneg (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
            - Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))]
      _ = 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  -- the `if`-filtered mixed double sum, bounded summand by summand
  have hM : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then
          (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
        + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (2 * (if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
              + 2 * (if 1 ≤ i ∧ i + j ≤ k then
                (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
          apply Finset.sum_le_sum; intro i hi
          apply Finset.sum_le_sum; intro j hj
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · rw [ite_eq_left hc, ite_eq_left hc, ite_eq_left hc, hMixed j i]
            nlinarith [sq_nonneg (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ
              - Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ)]
          · rw [ite_eq_right hc, ite_eq_right hc, ite_eq_right hc]
            norm_num
      _ = 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
          + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
  linarith [hZ, hM]

end Work.FTS.Galerkin.Hilbert
