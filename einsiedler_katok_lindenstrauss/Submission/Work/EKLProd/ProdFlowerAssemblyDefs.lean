import Mathlib
import Submission.Work.EKLProd.ProdFlowerDefs
import Submission.Work.EKLProd.ProdFlowerLemmas

/-!
# C5b: the objects of the local product-structure derivation

This module fixes the vocabulary of the `π`-`λ` step of C5b (`EKLComp/ProductPlan.md` §10.3):
the *atom pushforward* `prodFlowerΛ` of the `H`-leafwise measure at a base point of a
product-box flower, its joint law `prodFlowerΛTP` under the `(T,U)`-coordinate map
`g ↦ (hT T U g, hU T U g)`, and the normalised `T`-marginal `prodFlowerκ` predicted by the
`T`-side tower identity `Work.EKLProd.prodFlower_T_slice`.

The product structure of the `T`-side is `prodFlowerΛTP x = (prodFlowerκ x).prod (… .map Prod.snd)`,
see `Work.EKLProd.prodFlower_Lambda_prod`.
-/

open MeasureTheory Topology Filter
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLProd

open Work.EKLContract

variable {H T U : Subgroup SL3} {μ : MeasureTheory.Measure X3}

/-- The pushforward of the `H`-leafwise measure at `x`, cut down to the `H`-shape of the `n`-th
flower, under the plaque coordinate `h ↦ h * co n x` (the coordinates of the atom's base point).
A measure on `SL₃` carried by the product box `prodBox T U hf.R`. -/
def prodFlowerΛ (hf : ProdFlowerFam H T U μ) (n : ℕ)
    (νH : X3 → MeasureTheory.Measure SL3) (x : X3) : MeasureTheory.Measure SL3 :=
  ((νH x).restrict (shape (hf.mH n) H x)).map (fun h : SL3 => h * hf.co n x)

/-- The joint law of the `T`-part and the `U`-part of the plaque coordinate of the points of the
`H`-shape (`EKLComp/ProductPlan.md` §10.3, the measure called `Λ''` there). -/
def prodFlowerΛTP (hf : ProdFlowerFam H T U μ) (n : ℕ)
    (νH : X3 → MeasureTheory.Measure SL3) (x : X3) : MeasureTheory.Measure (SL3 × SL3) :=
  (prodFlowerΛ hf n νH x).map (fun g : SL3 => (hT T U g, hU T U g))

/-- The normalised `T`-marginal of the atom: the translate `(νT x) · (hT T U (co n x))` of the
`T`-leafwise measure at `x`, restricted to the `T`-ball `V hf.R ∩ T` and normalised.  This is the
first factor of the product structure predicted by the `T`-side tower identity. -/
def prodFlowerκ (hf : ProdFlowerFam H T U μ) (n : ℕ)
    (νT : X3 → MeasureTheory.Measure SL3) (x : X3) : MeasureTheory.Measure SL3 :=
  (((νT x).map (fun g : SL3 => g * hT T U (hf.co n x)))
      (V hf.R ∩ (T : Set SL3)))⁻¹ •
    (((νT x).map (fun g : SL3 => g * hT T U (hf.co n x))).restrict (V hf.R ∩ (T : Set SL3)))

end Work.EKLProd
