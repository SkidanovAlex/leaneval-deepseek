import Mathlib
import Submission.Work.EKLRelProduct.Defs
import Submission.Work.EKLRelProduct.uAvg_eq
import Submission.Work.EKLProd.prodFlower_T_slice
import Submission.Work.EKLProd.ProdFlowerDefs

/-!
# `Work.EKLRelProduct.LocStructDefs`

Vocabulary for the local product structure `Work.EKLRelProduct.locStruct`.

For a product-box flower `hf : ProdFlowerFam H T U μ` with plaque coordinate `co n z = t_z * u_z`
(`t_z = hT T U (co n z) ∈ T`, `u_z = hU T U (co n z) ∈ U`), the pointwise product structure of the
`H`-plaquette measure asserts that the joint law of the `T`-part and the `U`-part of the plaque
coordinate `w ↦ (hT T U w, hU T U w)` under `(νH z) ↾ shape (mH n) H z` is a product of two
measures on `SL₃`:

* `etaT hf νT n z` — the **`T`-factor**: the translate `(νT z).map (· * t_z)` of the `T`-leafwise
  measure, restricted to the `T`-ball `V R ∩ T` and normalised.  Equivalently (see `S_T`), the
  normalised restriction of `νT z` to the source set `S_T hf n z`.
* `psi hf νH n z` — the **`U`-factor**: the pushforward of `(νH z) ↾ shape (mH n) H z` under
  `hU T U` (the `U`-marginal `ν_r'` of the plaquette measure).

`S_T`, `S_U` are the source sets of the two factors: the directions of `T`/`U` along which a point
of `shape` still lands in the product box.
-/

open MeasureTheory
open Work.EKLContract Work.EKLProd

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelProduct

variable {H T U : Subgroup SL3} {μ : MeasureTheory.Measure X3}

/-- The set of `T`-directions `g` out of the base point whose plaque coordinate `g * t_z` still
lies in the `T`-ball `V R ∩ T`: the source set of the `T`-factor `etaT`. -/
def S_T (hf : ProdFlowerFam H T U μ) (n : ℕ) (z : X3) : Set SL3 :=
  {g : SL3 | g * hT T U (hf.co n z) ∈ V hf.R ∩ (T : Set SL3)}

/-- The set of `U`-directions `g` out of the base point whose plaque coordinate
`shiftMap t_z u_z g = t_z⁻¹ * g * t_z * u_z` still lies in the `U`-ball `V R ∩ U`: the source set
of the `U`-factor `psi`. -/
def S_U (hf : ProdFlowerFam H T U μ) (n : ℕ) (z : X3) : Set SL3 :=
  {g : SL3 | shiftMap (hT T U (hf.co n z)) (hU T U (hf.co n z)) g
      ∈ V hf.R ∩ (U : Set SL3)}

/-- The `T`-factor of the product structure at `z`: the normalised restriction of the `T`-leafwise
measure `νT z` to the source set `S_T hf n z`. -/
def etaT (hf : ProdFlowerFam H T U μ) (νT : X3 → MeasureTheory.Measure SL3) (n : ℕ) (z : X3) :
    MeasureTheory.Measure SL3 :=
  ((νT z) (S_T hf n z))⁻¹ • ((νT z).restrict (S_T hf n z))

/-- The `U`-factor of the product structure at `z`: the pushforward of the `H`-plaquette measure
`(νH z) ↾ shape (mH n) H z` under the `U`-part map `hU T U`. -/
def psi (hf : ProdFlowerFam H T U μ) (νH : X3 → MeasureTheory.Measure SL3) (n : ℕ) (z : X3) :
    MeasureTheory.Measure SL3 :=
  ((νH z).restrict (shape (hf.mH n) H z)).map (fun w : SL3 => hU T U w)

end Work.EKLRelProduct

end
