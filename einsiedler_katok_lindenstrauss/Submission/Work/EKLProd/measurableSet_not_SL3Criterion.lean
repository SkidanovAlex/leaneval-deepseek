import Mathlib
import Submission.Work.EKLRelCross.SL3famDefs

/-!
# `Work.EKLProd.measurableSet_not_SL3Criterion`

Measurability of the set of parameters at which the countable proportionality criterion
`Work.EKLRelCross.SL3Criterion` **fails**, for a pair of families of measures on `SL₃(ℝ)`
parametrised by `X₃`.

The criterion
```
SL3Criterion m1 m2  ↔  ∃ p₀, 0 < m1 (SL3fam p₀) ∧ 0 < m2 (SL3fam p₀) ∧
                                 ∀ p, m2 (SL3fam p) * m1 (SL3fam p₀) = m1 (SL3fam p) * m2 (SL3fam p)
```
is a countable Boolean combination of the elementary (pointwise) conditions `0 < m (SL3fam p)` and
`m₂ (SL3fam p) * m₁ (SL3fam p₀) = m₁ (SL3fam p) * m₂ (SL3fam p)`.  Hence, if the parametrised
evaluations `y ↦ mᵢ y (SL3fam p)` are measurable for every `p`, so is the criterion, and so is its
negation.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Work.EKLProd

open Work.EKLRelCross

/-- The set of parameters satisfying the countable proportionality criterion is the countable union
over the reference set `p₀` of the (pointwise) positivity and proportionality conditions. -/
lemma setOf_SL3Criterion_eq {α : Type*} (m1 m2 : α → Measure Work.EKLContract.SL3) :
    {y | SL3Criterion (m1 y) (m2 y)} =
      ⋃ p₀ : ℕ × Finset ℕ,
        ({y | 0 < m1 y (SL3fam p₀)} ∩ {y | 0 < m2 y (SL3fam p₀)}) ∩
        ⋂ p : ℕ × Finset ℕ,
          {y | m2 y (SL3fam p) * m1 y (SL3fam p₀) =
               m1 y (SL3fam p) * m2 y (SL3fam p₀)} := by
  ext y
  simp only [SL3Criterion, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter]
  tauto

/-- Measurability of the countable proportionality criterion, assuming measurability of the
evaluations on the countable π-system `SL3fam`. -/
lemma measurableSet_SL3Criterion {α : Type*} [MeasurableSpace α]
    {m1 m2 : α → Measure Work.EKLContract.SL3}
    (h1 : ∀ p : ℕ × Finset ℕ, Measurable fun y => m1 y (SL3fam p))
    (h2 : ∀ p : ℕ × Finset ℕ, Measurable fun y => m2 y (SL3fam p)) :
    MeasurableSet {y | SL3Criterion (m1 y) (m2 y)} := by
  rw [setOf_SL3Criterion_eq m1 m2]
  refine MeasurableSet.iUnion fun p₀ => ?_
  refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_
  · exact measurableSet_lt measurable_const (h1 p₀)
  · exact measurableSet_lt measurable_const (h2 p₀)
  · refine MeasurableSet.iInter fun p => ?_
    exact measurableSet_eq_fun ((h2 p).mul (h1 p₀)) ((h1 p).mul (h2 p₀))

theorem measurableSet_not_SL3Criterion
    {m1 m2 : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    (h1 : ∀ p : ℕ × Finset ℕ, Measurable fun y => m1 y (Work.EKLRelCross.SL3fam p))
    (h2 : ∀ p : ℕ × Finset ℕ, Measurable fun y => m2 y (Work.EKLRelCross.SL3fam p)) :
    MeasurableSet {y : Work.EKLContract.X3 |
      ¬ Work.EKLRelCross.SL3Criterion (m1 y) (m2 y)} := by
  have h : {y : Work.EKLContract.X3 | ¬ SL3Criterion (m1 y) (m2 y)} =
      {y | SL3Criterion (m1 y) (m2 y)}ᶜ := rfl
  rw [h]
  exact (measurableSet_SL3Criterion h1 h2).compl

end Work.EKLProd
