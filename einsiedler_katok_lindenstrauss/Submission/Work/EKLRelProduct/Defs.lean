import Mathlib
import Submission.Work.EKLProd.ProdFlowerDefs

/-!
# `Work.EKLRelProduct.Defs`

Definitions used by the C5b (`P_Product`) assembly in this directory.

* `gconj g x = g * x * g⁻¹` — conjugation, written out (Mathlib's `conj` is the star).
* `uShift` — the (Pisa 8.12c) translate of the `U`-leafwise measure:
  with `co n y = t_y * u_y` the decomposition of the plaque coordinate,
  `uShift y := (νU y).map (u ↦ t_y * u * t_y⁻¹ * u_y⁻¹)`.
-/

open MeasureTheory
open Work.EKLContract Work.EKLProd

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelProduct

/-- Conjugation in `SL₃(ℝ)`, written out (Mathlib's `conj` is the star operation). -/
def gconj (g x : SL3) : SL3 := g * x * g⁻¹

/-- The (8.12c) reparametrisation of the `U`-leafwise measure at the point `y` of the `n`-th flower
(the map `u ↦ t_y⁻¹ * u * t_y * u_y` is the inverse of the `U`-leaf coordinate of the
`H`-plaquette, cf. `Work.EKLRelProduct.uAvg_eq`):
`(νU y).map (u ↦ t_y⁻¹ * u * t_y * u_y)` where `co n y = t_y * u_y`. -/
def uShift {H T U : Subgroup SL3} {μ : Measure X3} (hf : ProdFlowerFam H T U μ)
    (νU : X3 → Measure SL3) (n : ℕ) (y : X3) : Measure SL3 :=
  (νU y).map (fun u => gconj (hT T U (hf.co n y))⁻¹ u * (hU T U (hf.co n y)))

/-- The `U`-marginal `ν_r'` of the `H`-plaquette measure `Λ''` of the `n`-th flower: the
pushforward of `(νH x)|_{shape}` under `h ↦ hU (co (h • x))` (the `U`-part of the coordinate of
the translate).  This is the `ν_r` of Pisa 8.12. -/
def uMarg {H T U : Subgroup SL3} {μ : Measure X3} (hf : ProdFlowerFam H T U μ)
    (νH : X3 → Measure SL3) (n : ℕ) (x : X3) : Measure SL3 :=
  ((νH x).restrict (shape (hf.mH n) H x)).map (fun h => hU T U (hf.co n (h • x)))

/-- The normalised `U`-shape average of `1_B ∘ (hU ∘ co)`, the object identified with
`ν_r'` by the (8.12c) computation. -/
def uAvg {H T U : Subgroup SL3} {μ : Measure X3} (hf : ProdFlowerFam H T U μ)
    (νU : X3 → Measure SL3) (n : ℕ) (y : X3) (B : Set SL3) : ℝ :=
  (∫ u in shape (hf.mU n) U y, B.indicator (fun _ => (1 : ℝ)) (hU T U (hf.co n (u • y)))
      ∂(νU y))
    / ((νU y) (shape (hf.mU n) U y)).toReal

end Work.EKLRelProduct
