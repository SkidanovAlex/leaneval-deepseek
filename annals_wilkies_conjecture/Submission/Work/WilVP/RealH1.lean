/-
  WilVP: the `ℝ`-side input `H1` for the final wire.

  `Work.WilVP.isoBallProp_real` packages `Work.WilVP.isoBall_real` (N1) with C4's `realULPM`
  (H1) into the single statement `IsoBallProp ℝ`.  Keeping this in its own module (a) makes the
  final file a two-line term and (b) keeps every `ℝ`-instance-level elaboration away from
  `Submission.Work.WilC5.stdPart` (review fix F1).
-/
import Mathlib
import Submission.Work.WilVP.N1_iso
import Submission.Work.WilC4.realULPM

set_option autoImplicit false

noncomputable section
open Classical
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilVP

/-- `H1` at `ℝ`: `Work.WilVP.isoBall_real` fed with C4's `realULPM`. -/
theorem isoBallProp_real
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (hOM : OMinModels) (hPB : PolyBoundedRExp) : IsoBallProp ℝ :=
  isoBall_real (Work.WilC4.realULPM hR hOM hPB) hOM

end Work.WilVP
