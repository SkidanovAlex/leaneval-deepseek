import Mathlib
import Submission.Work.EKLC7.borel_eq_generateFrom_Ioc_rat
import Submission.Work.EKLC7.isPiSystem_Ioc_rat
import Submission.Work.EKLC7.sUnion_range_Ioc_rat_eq_univ

/-!
# Two measures on `ℝ` finite on compacts, agreeing on rational half-open intervals

If `μ` and `ν` are measures on `ℝ` which are finite on compact sets and agree on every
half-open interval `(a, b]` with **rational** endpoints, then `μ = ν`.

The proof is the standard π-system / uniqueness argument.  Let

* `S = {Ioc (a : ℝ) (b : ℝ) | a b : ℚ}` be the family of half-open intervals with rational
  endpoints, and
* `T = {Ioc (-n, n] | n : ℕ}` be the covering family.

Then:

* `S` is a π-system (`isPiSystem_Ioc_rat`);
* `S` generates the Borel σ-algebra on `ℝ` (`borel_eq_generateFrom_Ioc_rat`), since the
  rationals are dense;
* `T ⊆ S`, `T` is countable, and `⋃₀ T = univ` (`sUnion_range_Ioc_rat_eq_univ`);
* every member of `T` has finite `μ`-measure (it is contained in a compact interval and `μ`
  is finite on compacts).

Hence `Measure.ext_of_generateFrom_of_cover_subset` applies.
-/

open MeasureTheory Set

namespace Work.EKLC7

/-- Two measures on `ℝ` that are finite on compacts and agree on all half-open intervals with
rational endpoints are equal. -/
theorem ext_of_Ioc_rat {μ ν : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsFiniteMeasureOnCompacts μ] [MeasureTheory.IsFiniteMeasureOnCompacts ν]
    (h : ∀ a b : ℚ, μ (Set.Ioc (a : ℝ) (b : ℝ)) = ν (Set.Ioc (a : ℝ) (b : ℝ))) : μ = ν := by
  refine Measure.ext_of_generateFrom_of_cover_subset (m0 := inferInstance)
    (S := {s : Set ℝ | ∃ a b : ℚ, s = Ioc (a : ℝ) (b : ℝ)})
    (T := Set.range (fun n : ℕ => Ioc (-(((n : ℚ)) : ℝ)) (((n : ℚ)) : ℝ))) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact BorelSpace.measurable_eq.trans borel_eq_generateFrom_Ioc_rat
  · exact isPiSystem_Ioc_rat
  · rintro _ ⟨n, rfl⟩
    exact ⟨-(n : ℚ), (n : ℚ), by simp⟩
  · exact Set.countable_range _
  · exact sUnion_range_Ioc_rat_eq_univ
  · rintro _ ⟨n, rfl⟩
    exact (measure_Ioc_lt_top (μ := μ)).ne
  · rintro _ ⟨a, b, rfl⟩
    exact h a b

end Work.EKLC7
