import Mathlib
import Submission.Work.EKLProd.AtomProductDefs
import Submission.Work.EKLRelCross.SL3criterion
import Submission.Work.EKLRelCross.SL3famDefs

set_option linter.unusedVariables false

namespace Work.EKLProd

open MeasureTheory

/-- `SL3Criterion` is symmetric in its two arguments: the defining relation
`m2 a * m1 a₀ = m1 a * m2 a₀` is unchanged (up to commutativity of multiplication)
when the two measures are swapped, and the positivity requirements are symmetric. -/
lemma SL3Criterion_comm {m1 m2 : MeasureTheory.Measure Work.EKLContract.SL3} :
    Work.EKLRelCross.SL3Criterion m1 m2 ↔ Work.EKLRelCross.SL3Criterion m2 m1 := by
  constructor
  · rintro ⟨p₀, h1, h2, h⟩
    exact ⟨p₀, h2, h1, fun p => (h p).symm⟩
  · rintro ⟨p₀, h2, h1, h⟩
    exact ⟨p₀, h1, h2, fun p => (h p).symm⟩

/-- On the locus where `y` lies in the `n`-th flower and in both `XH`, `XU`, and where both
`atomShU` and `atomMargU` are nonzero, `atomId` (the (8.12c) identification) is equivalent to the
negation of `atomBad` (failure of the countable proportionality criterion `SL3Criterion`).

Indeed, on that locus `atomBad y` is exactly `¬ SL3Criterion (atomShU … y) (atomMargU … y)`,
while `SL3criterion` identifies `atomId y` with `SL3Criterion (atomMargU … y) (atomShU … y)`, and
`SL3Criterion` is symmetric. -/
theorem atomId_iff_not_atomBad {H T U : Subgroup Work.EKLContract.SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (hf : Work.EKLProd.ProdFlowerFam H T U μ) (n : ℕ)
    {νH νU : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {XH XU : Set Work.EKLContract.X3} {y : Work.EKLContract.X3}
    (hyZ : y ∈ hf.Z n) (hyH : y ∈ XH) (hyU : y ∈ XU)
    (h1 : Work.EKLProd.atomShU hf n νU y ≠ 0)
    (h2 : Work.EKLProd.atomMargU hf n νH y ≠ 0)
    (h1t : MeasureTheory.IsFiniteMeasureOnCompacts (Work.EKLProd.atomShU hf n νU y))
    (h2t : MeasureTheory.IsFiniteMeasureOnCompacts (Work.EKLProd.atomMargU hf n νH y)) :
    (Work.EKLProd.atomId hf n νH νU y ↔
      ¬ Work.EKLProd.atomBad hf n XH XU νH νU y) := by
  have hcrit := Work.EKLRelCross.SL3criterion (m1 := atomMargU hf n νH y)
      (m2 := atomShU hf n νU y) h2t h1t h2 h1
  have hsymm := SL3Criterion_comm (m1 := atomMargU hf n νH y) (m2 := atomShU hf n νU y)
  have hbad : ¬ atomBad hf n XH XU νH νU y ↔
      Work.EKLRelCross.SL3Criterion (atomShU hf n νU y) (atomMargU hf n νH y) := by
    show ¬ (y ∈ hf.Z n ∧ y ∈ XH ∧ y ∈ XU ∧ atomShU hf n νU y ≠ 0 ∧
        atomMargU hf n νH y ≠ 0 ∧
        ¬ Work.EKLRelCross.SL3Criterion (atomShU hf n νU y) (atomMargU hf n νH y)) ↔ _
    constructor
    · intro h
      by_contra hS
      exact h ⟨hyZ, hyH, hyU, h1, h2, hS⟩
    · rintro hS ⟨-, -, -, -, -, hS'⟩
      exact hS' hS
  rw [hbad]
  exact hcrit.trans hsymm

end Work.EKLProd
