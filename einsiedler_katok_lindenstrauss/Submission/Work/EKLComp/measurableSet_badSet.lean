import Mathlib
import Submission.Work.EKLComp.BirkhoffDefs

open MeasureTheory Filter

namespace Work.EKLComp

/-- `birkA T f n` is measurable when `T` and `f` are: it is a finite sum of the
measurable functions `f ∘ T^[k]` multiplied by a constant. -/
theorem measurable_birkA {X : Type*} [MeasurableSpace X] (T : X → X) (hT : Measurable T)
    (f : X → ℝ) (hf : Measurable f) (n : ℕ) :
    Measurable (fun x => Work.EKLComp.Birkhoff.birkA T f n x) := by
  change Measurable (fun x => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f (T^[k] x))
  fun_prop

/-- The set of points where the Birkhoff averages of `f` frequently exceed the rational
level `q` is the `limsup` of the measurable sets `{x | q < birkA T f n x}`. -/
theorem measurableSet_frequently_lt_birkA {X : Type*} [MeasurableSpace X] (T : X → X)
    (hT : Measurable T) (f : X → ℝ) (hf : Measurable f) (q : ℚ) :
    MeasurableSet {x | ∃ᶠ n in atTop, (q : ℝ) < Work.EKLComp.Birkhoff.birkA T f n x} := by
  have hlim := MeasurableSet.measurableSet_limsup
    (s := fun n => {x | (q : ℝ) < Work.EKLComp.Birkhoff.birkA T f n x})
    (fun n => measurableSet_lt measurable_const (measurable_birkA T hT f hf n))
  rwa [show {x : X | ∃ᶠ n in atTop, (q : ℝ) < Work.EKLComp.Birkhoff.birkA T f n x}
      = Filter.limsup (fun n => {x | (q : ℝ) < Work.EKLComp.Birkhoff.birkA T f n x}) atTop
      from by ext x; simp [Filter.mem_limsup_iff_frequently_mem]]

/-- `badSet T f ε` is Borel measurable when `T` and `f` are measurable: it is the countable
union over `q ∈ ℚ` with `ε < q` of the `limsup` of the measurable sets `{x | q < birkA T f n x}`,
where `birkA T f n x = n⁻¹ ∑_{k<n} f (T^[k] x)` is a finite sum of measurable functions. -/
theorem measurableSet_badSet {X : Type*} [MeasurableSpace X] (T : X → X) (hT : Measurable T)
    (f : X → ℝ) (hf : Measurable f) (ε : ℝ) :
    MeasurableSet (Work.EKLComp.Birkhoff.badSet T f ε) := by
  have heq : Work.EKLComp.Birkhoff.badSet T f ε
      = ⋃ q : ℚ,
          {x | ε < (q : ℝ) ∧ ∃ᶠ n in atTop, (q : ℝ) < Work.EKLComp.Birkhoff.birkA T f n x} := by
    ext x; simp [Work.EKLComp.Birkhoff.badSet]
  rw [heq]
  apply MeasurableSet.iUnion
  intro q
  by_cases h : ε < (q : ℝ)
  · simpa [h] using measurableSet_frequently_lt_birkA T hT f hf q
  · simp [h]

end Work.EKLComp
