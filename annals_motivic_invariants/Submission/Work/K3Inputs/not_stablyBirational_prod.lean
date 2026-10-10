import Submission.Work.K3Inputs.StablyBiratK3
import Submission.Work.K3Inputs.not_stablyBirat_prod

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3Inputs.not_stablyBirational_prod` — the product form of the distinguishing

`Work.K3.StablyBirational 𝕜 X Y` (the K3 chapter's relation, used by `Work.K3.TotaroInput`) is
`∃ n m, X × 𝔸ⁿ ∼ Y × 𝔸ᵐ` with the challenge's `BirationalMap` and with the `Variety` instances of
the products bound inside the existential.  This file provides the two conversions between it and
the instance-free `Work.K3Inputs.StablyBirat` which the cylinder calculus uses, and combines them
with the exponent shift `Work.K3Inputs.not_stablyBirat_prod`:

* `Work.K3Inputs.StablyBirat_of_stablyBirational` — from the K3 chapter's relation to
  `StablyBirat`, via partial-isomorphism representatives of the `BirationalMap`
  (`Work.Motivic.exists_partialIso_toBirationalMap`);
* `Work.K3Inputs.not_stablyBirational_prod` — if `X` and `Y` are not stably birational over `𝕜`,
  then `X × 𝔸ⁿ` and `Y × 𝔸ᵐ` are not: the form used to justify that the `[κ(S)(t)]`-coefficient of
  `c(ψ_𝕜)` is computed at the class `[S × ℙ¹]` (with
  `Work.K3Inputs.not_sameCylinderField_of_totaro` for the resulting statement
  `κ(S)(t) ≄ κ(S')(t)`).

(The conclusion is stated with `StablyBirat`, without the `Variety`-instance arguments of
`Work.K3.StablyBirational`: the two relations are related by
`Work.K3Inputs.StablyBirat_to_stablyBirational` and
`Work.K3Inputs.StablyBirat_of_stablyBirational`, and — since the `Over`-structure of a fibre
product is entered as *data* into the types `StablyBirational 𝕜 _ _` — stating the conclusion in
the instance-free form avoids having to reconcile `Work.K3.prodOverOver` with
`MotivicInvariants.Variety.over` at the call site.  See `NOTES.md` §5 for the details.)
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

/-- The instance-free stable birationality is implied by the K3 chapter's relation: a
`BirationalMap` between the products is represented by a partial isomorphism
(`Work.Motivic.exists_partialIso_toBirationalMap`), and the `Variety` instances bound in the
existential supply the integrality needed for `Scheme.Birational`. -/
theorem StablyBirat_of_stablyBirational {X Y : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y]
    (h : Work.K3.StablyBirational 𝕜 X Y) : StablyBirat 𝕜 X Y := by
  obtain ⟨n, m, hX, hY, φ⟩ := h
  obtain ⟨φ⟩ := φ
  haveI := hX.isIntegral
  haveI := hY.isIntegral
  obtain ⟨i, -⟩ := Work.Motivic.exists_partialIso_toBirationalMap φ
  exact ⟨n, m, ⟨i⟩⟩

/-- **`X × 𝔸ⁿ` and `Y × 𝔸ᵐ` are not stably birational when `X` and `Y` are not** (K3 chapter's
relation), i.e. the `[κ(X)(t)]`-coefficient of an invariant is computed at the `ℙ¹`-bundle of
`X` rather than at a class depending on the model. -/
theorem not_stablyBirational_prod {X Y : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y]
    (h : ¬ Work.K3.StablyBirational 𝕜 X Y) (n m : ℕ) :
    ¬ StablyBirat 𝕜 (Work.K3.prodOver 𝕜 X (AffineN 𝕜 n))
      (Work.K3.prodOver 𝕜 Y (AffineN 𝕜 m)) :=
  not_stablyBirat_prod 𝕜 (not_stablyBirat_of_not_stablyBirational X Y h) n m

end

end Work.K3Inputs
