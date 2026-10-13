/-
  WilVP FINAL WIRE: `Work.WilVP.ValProp_TR`.

  The valuation property for `TR` (vdDMM (3.7), containment half; frozen statement
  `Work.WilC5.ValProp`), assembled from

  * `Work.WilVP.isoBallProp_real`  : `IsoBallProp ℝ`     (N1 = `isoBall_real` + C4's `realULPM`),
  * `Work.WilVP.transferOfIsoBall` : `IsoBallProp ℝ → ∀ M ⊨ TR, IsoBallProp M`   (N2),
  * `Work.WilVP.valProp_of_isoBall`: `(∀ M ⊨ TR, IsoBallProp M) → ValProp`        (N3),
  * `Work.WilVP.exists_closer_translate` : the standard-part step of N3 (kept in its own module,
    because it is the only module of this subproject that imports `Work.WilC5.stdPart`).

  This file is deliberately a *term-mode* composition (review fix F1): the `ℝ`-instance arguments
  of `isoBallProp_real` and `transferOfIsoBall` are fixed in the modules that state them, so no
  fresh `ℝ`-instance synthesis happens here.
-/
import Mathlib
import Submission.Work.WilVP.Defs
import Submission.Work.WilVP.RealH1
import Submission.Work.WilVP.transferOfIsoBall
import Submission.Work.WilVP.valProp_of_isoBall
import Submission.Work.WilVP.exists_closer_translate
import Submission.Work.WilC5.ValProp

set_option autoImplicit false

noncomputable section
open Classical
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilVP

/-- **ValProp_TR.**  The valuation property for `TR`: if some element definable from `S ∪ {z}` has
a value outside `v(S^×)`, then so does some translate `z − a`, `a ∈ S`. -/
theorem ValProp_TR (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (hOM : OMinModels) (hPB : PolyBoundedRExp) : Work.WilC5.ValProp :=
  valProp_of_isoBall
    (fun M _ _ _ _ _ _ _ S => exists_closer_translate (M := M) S)
    (transferOfIsoBall (isoBallProp_real hR hOM hPB))

end Work.WilVP
