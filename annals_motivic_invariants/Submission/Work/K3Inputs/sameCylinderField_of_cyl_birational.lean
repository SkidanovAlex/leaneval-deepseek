import Mathlib
import Submission.Work.K3Inputs.Defs
import Submission.Work.K3Inputs.Cylinder
import Submission.Work.K3Inputs.cylFieldAlgEquiv
import Submission.Work.K3Inputs.cylIsoPullbackAffineLine
import Submission.Work.K3Inputs.funFieldAlgEquiv_of_partialIsoOver

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.K3Inputs

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open MotivicInvariants
open Work.K3Inputs

/-- **The converse of the cylinder rigidity is automatic** (for a partial isomorphism *over*
`Spec 𝕜`).

`Work.K3Inputs.CylinderRigid 𝕜 X Y` is the clause (F2) of the ℙ¹-bundle bridge: an isomorphism
`κ(X)(t) ≅ κ(Y)(t)` of cylinder fields descends to a birational map `X × ℙ¹ ⤏ Y × ℙ¹` (the paper's
`lem-stbirCY` at `W = ℙ¹`).  The converse direction needs no separably-uniruled input: a partial
isomorphism between the cylinders *over the base* induces a `𝕜`-algebra isomorphism of their
function fields, and the function field of the cylinder is `RatFunc κ(X)`
(`Work.CrauderKatz.functionField_prod_affineLine`).  So the content of (F2) is exactly the descent
direction, i.e. the uniqueness of the fibration of `Z × ℙ¹` for `Z` not separably uniruled.

(Over-ness is necessary: `Scheme.Birational`/`PartialIso` carry no compatibility with the structure
maps, and `SameCylinderField` is `𝕜`-linear, in the sense that the isomorphism commutes with
`cylResMap`; without `IsOver` the statement is false, e.g. for `𝕜 = ℚ(t)`, `Y = Spec 𝕜` with the
structure map `t ↦ t²`.  The two `IsIntegral`-hypotheses on the cylinders are needed for the
function-field bookkeeping; they hold, for instance, when `X`, `Y` are `Variety`-arguments together
with geometric integrality over `Spec 𝕜`.) -/
theorem sameCylinderField_of_cyl_birational (𝕜 : Type) [Field 𝕜] {X Y : Scheme.{0}}
    [IsIntegral X] [IsIntegral Y] [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))]
    [IsIntegral (Cyl 𝕜 X)] [IsIntegral (Cyl 𝕜 Y)]
    (h : ∃ i : (Cyl 𝕜 X).PartialIso (Cyl 𝕜 Y),
      i.IsOver (Cyl 𝕜 X ↘ Spec (.of 𝕜)) (Cyl 𝕜 Y ↘ Spec (.of 𝕜))) :
    SameCylinderField 𝕜 X Y := by
  -- The partial isomorphism of the cylinders over `Spec 𝕜` gives a `𝕜`-linear isomorphism of
  -- their function fields.
  obtain ⟨Φ, hΦ⟩ := funFieldAlgEquiv_of_partialIsoOver 𝕜 (X := Cyl 𝕜 X) (Y := Cyl 𝕜 Y) h
  -- Each cylinder agrees with the fibre product of `X` with `Spec 𝕜[t]`, over `Spec 𝕜`.
  obtain ⟨ιX, hιX⟩ := cylIsoPullbackAffineLine 𝕜 X
  obtain ⟨ιY, hιY⟩ := cylIsoPullbackAffineLine 𝕜 Y
  -- The function field of a cylinder is `RatFunc` of the function field of its base, over `𝕜`.
  obtain ⟨eX, heX⟩ := cylFieldAlgEquiv 𝕜 X (Cyl 𝕜 X) ιX hιX
  obtain ⟨eY, heY⟩ := cylFieldAlgEquiv 𝕜 Y (Cyl 𝕜 Y) ιY hιY
  refine ⟨eX.symm.trans (Φ.trans eY), ?_⟩
  rw [RingEquiv.toRingHom_trans', RingEquiv.toRingHom_trans', RingHom.comp_assoc,
    RingHom.comp_assoc]
  have heX' : ∀ a, eX.symm (cylResMap 𝕜 X a)
      = Work.CrauderKatz.functionFieldResMap 𝕜 (Cyl 𝕜 X) a := by
    intro a
    rw [← RingHom.congr_fun heX a]
    exact RingEquiv.symm_apply_apply eX _
  have hΦ' : ∀ a, Φ (Work.CrauderKatz.functionFieldResMap 𝕜 (Cyl 𝕜 X) a)
      = Work.CrauderKatz.functionFieldResMap 𝕜 (Cyl 𝕜 Y) a := fun a => RingHom.congr_fun hΦ a
  have heY' : ∀ a, eY (Work.CrauderKatz.functionFieldResMap 𝕜 (Cyl 𝕜 Y) a)
      = cylResMap 𝕜 Y a := fun a => RingHom.congr_fun heY a
  ext a
  change eY (Φ (eX.symm (cylResMap 𝕜 X a))) = cylResMap 𝕜 Y a
  rw [heX' a, hΦ' a, heY' a]

end Work.K3Inputs
