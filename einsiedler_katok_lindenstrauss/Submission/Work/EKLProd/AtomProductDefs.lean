import Mathlib
import Submission.Work.EKLProd.ProdFlowerAssemblyDefs
import Submission.Work.EKLRelProduct.Defs
import Submission.Work.EKLRelProduct.LocStructDefs
import Submission.Work.EKLRelCross.SL3criterion

/-!
# Vocabulary for `Work.EKLProd.prodFlower_atom_product`

This module fixes the objects of the atom-level product structure at a base point of a
product-box flower (plan §12.3, `(AL_z)`).

For `y : X₃` and a flower family `hf : ProdFlowerFam H T U μ`:

* `atomShU hf n νU y` — the (Pisa 8.12c) translate of the `U`-leafwise measure at `y`,
  restricted to the `U`-ball `V hf.R ∩ U`:
  `(uShift hf νU n y) ↾ (V hf.R ∩ U)`.

* `atomMargU hf n νH y` — the `U`-marginal of the joint `(T,U)`-law of the plaque measure at
  `y`, restricted to the same ball: `((prodFlowerΛTP hf n νH y).map Prod.snd) ↾ (V hf.R ∩ U)`.

* `atomId hf n νH νU y` — **the identification `(8.12c)` at the point `y`**: the two measures
  above are proportional with a constant `c ≠ 0, ⊤`.  This is *exactly* the conclusion of
  `Work.EKLRelProduct.psiEqNuU` at the point `y` (the statement stays at the same point `y`; it
  is the fibre statements `Work.EKLProd.prodFlower_nuU_fibre`/`uSide` that carry a second base
  point).

* `atomBad hf n νH νU` — a **sound Borel** description of the set of points where `atomId`
  fails: on the conull set where `y ∈ Z n`, `y ∈ XH`, `y ∈ XU` and both measures are nonzero,
  the failure of `atomId` is equivalent to the failure of the countable proportionality
  criterion `Work.EKLRelCross.SL3Criterion` (this is the content of
  `Work.EKLRelCross.SL3criterion`), and the latter is a countable Boolean combination of
  evaluations `y ↦ (atomShU … y) (SL3fam p)`, `y ↦ (atomMargU … y) (SL3fam p)`, which are
  measurable by the section-measurability of weakly measurable locally finite families
  (`Work.EKLC6Core.measurable_apply_section`).

`atomBad` is designed so that *both* implications hold on the conull locus:
`atomBad y → ¬ atomId y` (soundness: the criterion is required for proportionality) and
`¬ atomBad y → atomId y` (completeness there).
-/

open MeasureTheory Topology Filter
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLProd

open Work.EKLContract

variable {H T U : Subgroup SL3} {μ : MeasureTheory.Measure X3}

/-- The (Pisa 8.12c) translate of the `U`-leafwise measure at `y`, restricted to the `U`-ball. -/
def atomShU (hf : ProdFlowerFam H T U μ) (n : ℕ) (νU : X3 → Measure SL3) (y : X3) :
    Measure SL3 :=
  (Work.EKLRelProduct.uShift hf νU n y).restrict (V hf.R ∩ (U : Set SL3))

/-- The `U`-marginal of the joint `(T,U)`-law of the plaque measure at `y`, restricted to the
`U`-ball. -/
def atomMargU (hf : ProdFlowerFam H T U μ) (n : ℕ) (νH : X3 → Measure SL3) (y : X3) :
    Measure SL3 :=
  ((prodFlowerΛTP hf n νH y).map Prod.snd).restrict (V hf.R ∩ (U : Set SL3))

/-- **The identification (8.12c) at the point `y`**: the translated `U`-leafwise measure and the
`U`-marginal of the plaque measure are proportional (with a finite nonzero constant). -/
def atomId (hf : ProdFlowerFam H T U μ) (n : ℕ) (νH : X3 → Measure SL3)
    (νU : X3 → Measure SL3) (y : X3) : Prop :=
  ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ atomShU hf n νU y = c • atomMargU hf n νH y

/-- The sound Borel bad set for the identification at the points of the `n`-th flower: the
countable criterion `SL3Criterion` is violated (and both measures are nonzero, so that the
criterion is equivalent to proportionality). -/
def atomBad (hf : ProdFlowerFam H T U μ) (n : ℕ) (XH XU : Set X3)
    (νH : X3 → Measure SL3) (νU : X3 → Measure SL3) : Set X3 :=
  {y : X3 | y ∈ hf.Z n ∧ y ∈ XH ∧ y ∈ XU ∧ atomShU hf n νU y ≠ 0 ∧
    atomMargU hf n νH y ≠ 0 ∧
    ¬ Work.EKLRelCross.SL3Criterion (atomShU hf n νU y) (atomMargU hf n νH y)}

end Work.EKLProd

end
