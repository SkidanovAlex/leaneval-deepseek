import Mathlib
import Submission.Work.Mostow.geodSetup
import Submission.Work.Mostow.nearId_blk
import Submission.Work.Mostow.resStd_hom_discrete

/-!
# `Work.Mostow.ellipsoidMargRegion`

The ellipsoid of normal vectors `W` moved by `≤ η₁/40` under the normal part of a
small-rotation element `p` of the pointwise stabiliser of the standard geodesic is contained
in the image under `nrmC 1 m` of the Margulis region.

Route: `p` is the block element `blk 1 m 1 (nrmStd 1 m p)` (from `rhd_stab_form` plus
`resStd 1 m p = 1`), and the near-identity criterion `nearId_blk` at the base point
`fermiW 1 m 0 W` converts the displacement bound `‖nrmStd 1 m p W - W‖ ≤ η₁/40` into
`NearIdAt p (fermiW 1 m 0 W) η₁` (because `10 · (η₁/40) < η₁`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

theorem ellipsoidMargRegion (m : ℕ)
    (hA1 : Submission.Mostow.POActionProp 1) (hI1 : Submission.Mostow.HypIsometryProp 1)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1))
    (p : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1) (hpΛ : p ∈ Λ)
    (hpstab : p ∈ Submission.Mostow.SetStabStd 1 m)
    (hptriv : Submission.Mostow.resStd 1 m p = 1) (hpne : p ≠ 1)
    (η₁ : ℝ) (hη₁ : 0 < η₁)
    (hrot : Submission.Mostow.rotN (Submission.Mostow.nrmStd 1 m p) ≤ η₁ / 40) :
    {W : Submission.Mostow.E m |
        ‖Submission.Mostow.nrmStd 1 m p W - W‖ ≤ η₁ / 40}
      ⊆ Submission.Mostow.nrmC 1 m '' (Work.Mostow.margRegion m Λ η₁) := by
  intro W hW
  -- `p` is the block element determined by its normal part.
  have hp_eq : p = blk 1 m (1 : PO 1 1) (nrmStd 1 m p) := by
    conv_lhs => rw [rhd_stab_form 1 m hA1 hI1 hA hI hpstab]
    rw [hptriv]
  -- hence the displacement bound makes `p` near the identity at the base point.
  have hnear : NearIdAt p (fermiW 1 m (0 : E 1) W) η₁ := by
    intro u hu
    have hb := (nearId_blk m hA1 hI1 hA hI (nrmStd 1 m p) (0 : E 1) W).1
      (η₁ / 40) η₁ hrot hW (by linarith)
    rw [hp_eq]
    exact hb u hu
  exact ⟨fermiW 1 m (0 : E 1) W, ⟨p, hpΛ, hpstab, hptriv, hpne, hnear⟩,
    nib_nrmC_fermiW m (0 : E 1) W⟩

end Work.Mostow
