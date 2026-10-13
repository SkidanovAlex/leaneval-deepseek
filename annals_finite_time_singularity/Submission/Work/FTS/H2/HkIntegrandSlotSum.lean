import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

/-- The five top-order summands of the `ℋ⁴`-integrand of `g` (the pure `D_z^4` summand and the
four mixed summands `D_z^jD_θ^i g·W` with `(j,i) = (3,1),(2,2),(1,3),(0,4)`) add up to at most
`HkIntegrand α 4 g`:
`(D_z^4g·w/sin(2θ)^{η/2})² + Σ_{(j,i)} (mixed j i g·Wt α)² ≤ HkIntegrand α 4 g`.
Route: `HkIntegrand` is the sum of its two finite sums; the five LHS terms are distinct
summands of those sums, all other summands being squares or literal `0`, hence nonnegative.
Use `Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ 4 le_rfl` and
`Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i j hi hij` for the five individual summands
together with `Finset.single_le_sum`/`Finset.sum_le_sum` bookkeeping (or `nlinarith` after
rewriting `HkIntegrand` and showing each LHS term is one of its summands). -/
theorem HkIntegrandSlotSum (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (Work.Spaces.DzIter 4 g z θ * (Work.Spaces.w z
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      + (Work.Spaces.mixed 3 1 g z θ * Work.Spaces.Wt α z θ) ^ 2
      + (Work.Spaces.mixed 2 2 g z θ * Work.Spaces.Wt α z θ) ^ 2
      + (Work.Spaces.mixed 1 3 g z θ * Work.Spaces.Wt α z θ) ^ 2
      + (Work.Spaces.mixed 0 4 g z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  -- The pure `D_z^4` summand is one of the summands of the first (pure `D_z`) sum of
  -- `HkIntegrand α 4 g`, all the other summands of that sum being squares, hence `≥ 0`.
  have hZ : (Work.Spaces.DzIter 4 g z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ ∑ i ∈ Finset.range (4 + 1),
          (Work.Spaces.DzIter i g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
    Finset.single_le_sum
      (f := fun i => (Work.Spaces.DzIter i g z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (fun i _ => sq_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_self 4))
  -- The four mixed summands are the summands `(i,j) = (1,3),(2,2),(3,1),(4,0)` of the second
  -- (double) sum of `HkIntegrand α 4 g`; pair each of them with the index `i` of its outer
  -- summand, so that the four terms are dominated by the partial sums `∑_j` of the double sum,
  -- all the remaining summands of which are `0` or squares, hence `≥ 0`.
  have hmix : (Work.Spaces.mixed 3 1 g z θ * Work.Spaces.Wt α z θ) ^ 2
        + (Work.Spaces.mixed 2 2 g z θ * Work.Spaces.Wt α z θ) ^ 2
        + (Work.Spaces.mixed 1 3 g z θ * Work.Spaces.Wt α z θ) ^ 2
        + (Work.Spaces.mixed 0 4 g z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    -- The four mixed terms are `T 1 3, T 2 2, T 3 1, T 4 0` for the summand
    -- `T i j = if 1 ≤ i ∧ i + j ≤ 4 then (mixed j i g z θ * Wt α z θ)^2 else 0`.
    have hstep : (Work.Spaces.mixed 3 1 g z θ * Work.Spaces.Wt α z θ) ^ 2
          + (Work.Spaces.mixed 2 2 g z θ * Work.Spaces.Wt α z θ) ^ 2
          + (Work.Spaces.mixed 1 3 g z θ * Work.Spaces.Wt α z θ) ^ 2
          + (Work.Spaces.mixed 0 4 g z θ * Work.Spaces.Wt α z θ) ^ 2
        = ∑ i ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + (4 - i) ≤ 4 then
              (Work.Spaces.mixed (4 - i) i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
      simp [Finset.sum_range_succ]
    rw [hstep]
    -- Each of the four terms is a summand of the corresponding partial sum `∑_j`.
    apply Finset.sum_le_sum
    intro i hi
    refine Finset.single_le_sum
      (f := fun j => if 1 ≤ i ∧ i + j ≤ 4 then
        (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
      (fun j _ => ?_) (Finset.mem_range.mpr ?_)
    · split_ifs with h
      · exact sq_nonneg _
      · exact le_refl 0
    · have := Finset.mem_range.mp hi
      omega
  rw [Work.Spaces.HkIntegrand]
  linarith

end Work.FTS.H2
