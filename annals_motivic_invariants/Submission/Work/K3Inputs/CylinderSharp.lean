import Submission.Work.K3Inputs.Cylinder
import Submission.Work.K3Inputs.sameCylinderField_of_cyl_birational

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3Inputs.CylinderSharp` — the sharp form of the clause (F2)

`SameCylinderField 𝕜 X Y` (an isomorphism `κ(X)(t) ≅ κ(Y)(t)` of cylinder fields, `𝕜`-linear in
the sense of commuting with `cylResMap`) and the (over-the-base) birationality of the cylinders
`X × 𝔸¹ ∼ Y × 𝔸¹` are related by two implications:

* `←` is proved without any geometric input: an over-the-base partial isomorphism of the cylinders
  gives the cylinder-field isomorphism (`Work.K3Inputs.sameCylinderField_of_cyl_birational`);
* `→` is the clause (F2), the paper's Lemma `lem-stbirCY` at `W = ℙ¹` (uniqueness of the fibration
  of `Z × ℙ¹` for `Z` not separably uniruled), in its sharp form `CylinderRigidOver`
  (`Work.K3Inputs.Cylinder.lean`).

So the only non-formal content of (F2) is the descent direction.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.K3Inputs

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

variable {𝕜 : Type} [Field 𝕜]
/-- **The sharp form of (F2) makes `SameCylinderField` equivalent to (over-the-base) birationality
of the cylinders.**

The direction `←` is the proved converse (`Work.K3Inputs.sameCylinderField_of_cyl_birational`),
which needs no separably-uniruled input; the direction `→` is the sharp form of the cylinder
rigidity.  Hence the *only* non-formal content of (F2) is the descent
`κ(X)(t) ≅ κ(Y)(t) ⟹ X × ℙ¹ ∼ Y × ℙ¹` of `lem-stbirCY`. -/
theorem sameCylinderField_iff_cyl_birational {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))] [IsIntegral (Cyl 𝕜 X)]
    [IsIntegral (Cyl 𝕜 Y)] (hrigid : CylinderRigidOver 𝕜 X Y) :
    SameCylinderField 𝕜 X Y ↔
      ∃ i : (Cyl 𝕜 X).PartialIso (Cyl 𝕜 Y),
        i.IsOver (Cyl 𝕜 X ↘ Spec (.of 𝕜)) (Cyl 𝕜 Y ↘ Spec (.of 𝕜)) :=
  ⟨hrigid, sameCylinderField_of_cyl_birational 𝕜⟩


end

end Work.K3Inputs
