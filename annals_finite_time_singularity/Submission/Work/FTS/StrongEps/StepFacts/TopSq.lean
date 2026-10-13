/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/StepFacts/TopSq.lean`

The *top-order part* of the weighted `H^k`-integrand of `Work.Spaces`:

`TopSq α m f z θ = (D_z^m f · w z / sin(2θ)^{η/2})²
  + ∑_{i,j ≤ m} [1 ≤ i, i + j = m] · (D_z^j D_θ^i f · Wt α z θ)²`,

i.e. the `D_z^m`-slot together with the mixed slots of order exactly `m`.  The point of the
definition is the splitting

`HkIntegrand α m f ≤ HkIntegrand α (m-1) f + TopSq α m f`,

which lets one estimate the *already present* lower-order slots by the level-`m-1` norm (they are
literally its slots) and treat only the finitely many top slots separately.  This is the
bookkeeping behind the one-order smoothing estimate for the log-coordinate mollifier `J_ε`.

The main lemma is `HkIntegrand_le_prev_add_TopSq`, together with the auxiliary
`mixed_sum_step` (the purely combinatorial splitting of the mixed double sum at level `m`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StepFacts

set_option autoImplicit false

/-- The top-order slots of `HkIntegrand α m f`: the pure `D_z^m`-slot and the mixed slots whose
order `i + j` is exactly `m` (with `i ≥ 1`, as in `HkIntegrand`). -/
def TopSq (α : ℝ) (m : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.DzIter m f z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
    + ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        if 1 ≤ i ∧ i + j = m then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0

/-- `TopSq` is a sum of squares, hence nonnegative. -/
theorem TopSq_nonneg (α : ℝ) (m : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ TopSq α m f z θ := by
  refine add_nonneg (sq_nonneg _) ?_
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
    split_ifs with h
    · exact sq_nonneg _
    · exact le_refl 0

/-- **The combinatorial splitting of the mixed double sum.**  The mixed part of `HkIntegrand` at
level `m` is the mixed part at level `m - 1` plus the terms of exact order `m`.

The proof compares the two sides pointwise: for natural `i j`,
`[1 ≤ i ∧ i + j ≤ m] = [1 ≤ i ∧ i + j ≤ m - 1] + [1 ≤ i ∧ i + j = m]` as indicator functions,
and the terms with `i = m` or `j = m` in the level-`m-1` indicator already vanish (there
`i + j ≥ m > m - 1`), so the sum over `range (m+1)²` of the level-`m-1` indicator equals the sum
over `range m × range m`. -/
theorem mixed_sum_step (X : ℕ → ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        (if 1 ≤ i ∧ i + j ≤ m then X i j else 0))
      = (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
          (if 1 ≤ i ∧ i + j ≤ m - 1 then X i j else 0))
        + (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
            (if 1 ≤ i ∧ i + j = m then X i j else 0)) := by
  -- the pointwise indicator identity
  have hpt : ∀ i j : ℕ,
      (if 1 ≤ i ∧ i + j ≤ m then X i j else 0)
        = (if 1 ≤ i ∧ i + j ≤ m - 1 then X i j else 0)
          + (if 1 ≤ i ∧ i + j = m then X i j else 0) := by
    intro i j
    by_cases h1 : 1 ≤ i
    · by_cases h2 : i + j ≤ m - 1
      · rw [if_pos ⟨h1, by omega⟩, if_pos ⟨h1, h2⟩, if_neg (by omega), add_zero]
      · by_cases h3 : i + j = m
        · rw [if_pos ⟨h1, by omega⟩, if_neg (by omega), if_pos ⟨h1, h3⟩, zero_add]
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), add_zero]
    · rw [if_neg (by tauto), if_neg (by tauto), if_neg (by tauto), add_zero]
  -- the level-`m-1` sum over `range (m+1)²` equals the one over `range m × range m`
  have hshift : (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        (if 1 ≤ i ∧ i + j ≤ m - 1 then X i j else 0))
      = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
          (if 1 ≤ i ∧ i + j ≤ m - 1 then X i j else 0) := by
    have hinner : ∀ i : ℕ, (∑ j ∈ Finset.range (m + 1),
          (if 1 ≤ i ∧ i + j ≤ m - 1 then X i j else 0))
        = ∑ j ∈ Finset.range m, (if 1 ≤ i ∧ i + j ≤ m - 1 then X i j else 0) := by
      intro i
      refine (Finset.sum_subset (Finset.range_subset_range.mpr (Nat.le_succ m)) ?_).symm
      intro j hj hnj
      rw [Finset.mem_range] at hj hnj
      have : j = m := by omega
      subst this
      exact if_neg (by rintro ⟨h1, h2⟩; omega)
    rw [Finset.sum_congr rfl (fun i _ => hinner i)]
    refine (Finset.sum_subset (Finset.range_subset_range.mpr (Nat.le_succ m)) ?_).symm
    intro i hi hni
    rw [Finset.mem_range] at hi hni
    have : i = m := by omega
    subst this
    refine Finset.sum_eq_zero fun j hj => if_neg ?_
    rintro ⟨h1, h2⟩
    omega
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))]
  simp only [Finset.sum_add_distrib]
  rw [hshift]

/-- **The level-`m` integrand splits into the level-`(m-1)` integrand and the top slots.** -/
theorem HkIntegrand_le_prev_add_TopSq (α : ℝ) (m : ℕ) (hm : 1 ≤ m) (f : ℝ → ℝ → ℝ)
    (z θ : ℝ) :
    Work.Spaces.HkIntegrand α m f z θ
      ≤ Work.Spaces.HkIntegrand α (m - 1) f z θ + TopSq α m f z θ := by
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  -- the pure `D_z` sums
  have hZ : (∑ i ∈ Finset.range (m + 1),
        (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = (∑ i ∈ Finset.range (m - 1 + 1),
          (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + (Work.Spaces.DzIter m f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [hm']
    exact Finset.sum_range_succ _ _
  -- the mixed sums
  have hM := mixed_sum_step (fun i j => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
    m
  have hM' : (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
        (if 1 ≤ i ∧ i + j ≤ m - 1 then
          (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      = (∑ i ∈ Finset.range (m - 1 + 1), ∑ j ∈ Finset.range (m - 1 + 1),
        (if 1 ≤ i ∧ i + j ≤ m - 1 then
          (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
    rw [hm']
  rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand, TopSq]
  rw [hZ, hM, hM']
  linarith

end Work.FTS.StrongEps.StepFacts
