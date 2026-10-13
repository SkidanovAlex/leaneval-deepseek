import Mathlib
import Submission.Work.WilG4a.CD.PosHalf
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG1.Calc.pos_mem

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilG4a.CD

open WilkiesDesign

/-! ## 1. The coordinates of `ℝ^{p+3} = (z, δ, y)`

`z` occupies the coordinates `0,…,p`, `δ` the coordinate `p+1` and `y` the coordinate `p+2`. -/

/-- The coordinate of `z (Fin.last p)` in `ℝ^{p+3}`. -/
def czt (p : ℕ) : Fin (p + 3) := Fin.castSucc (Fin.castSucc (Fin.last p))

/-- The coordinate of `δ` in `ℝ^{p+3}`. -/
def cdl (p : ℕ) : Fin (p + 3) := Fin.castSucc (Fin.last (p + 1))

/-- The coordinate of `y` in `ℝ^{p+3}`. -/
def cyl (p : ℕ) : Fin (p + 3) := Fin.last (p + 2)

/-- The pullback index `Fin (p+1) → Fin (p+3)`: `z`'s first `p` coordinates are kept and the
last one is replaced by the coordinate of `y`. -/
def iotaInfl (p : ℕ) : Fin (p + 1) → Fin (p + 3) :=
  Fin.snoc (fun i : Fin p => Fin.castSucc (Fin.castSucc (Fin.castSucc i))) (Fin.last (p + 2))

/-- The condition `(y - z(last))² < δ²` on `ℝ^{p+3}`. -/
def inflCell (p : ℕ) : Set (Fin (p + 3) → ℝ) :=
  {w | (w (cyl p) - w (czt p)) ^ 2 < (w (cdl p)) ^ 2}

/-- The pointwise localisation: `z` admits a `δ > 0` such that the vertical interval
`(z(last) - δ, z(last) + δ)` through `z` lies in `X`. -/
def inflated (p : ℕ) (X : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  {z | ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |y - z (Fin.last p)| < δ → Fin.snoc (Fin.init z) y ∈ X}

/-- The explicit `Ω`-description of `inflated`: project `δ` off
`{δ > 0} ∩ (proj (inflCell ∩ pullback X))ᶜ`. -/
def inflatedAux (p : ℕ) (X : Set (Fin (p + 1) → ℝ)) : Set (Fin (p + 1) → ℝ) :=
  projLast (posHalf_y (p + 2) (Fin.last (p + 1)) ∩
    (projLast (inflCell p ∩ (Work.WilG5.coordPre (iotaInfl p) X)ᶜ))ᶜ)

end Work.WilG4a.CD
