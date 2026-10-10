import Submission.Work.K3Inputs.Defs
import Submission.Work.K3Inputs.Cylinder
import Submission.Work.K3Inputs.exists_variety_prodOver_affineSpace

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.K3Inputs.StablyBiratK3` — the two models of stable birationality, and the Totaro chain

`Work.K3.StablyBirational` (the K3 chapter's relation, used by `Work.K3.TotaroInput`) is
`∃ n m, X × 𝔸ⁿ ∼ Y × 𝔸ᵐ` with the challenge's `BirationalMap` and with a `Variety` instance bound
inside the existential; `Work.K3Inputs.StablyBirat` is the same relation with Mathlib's
`Scheme.Birational` and no instance arguments, which is the form in which the ℙ¹-bundle bridge and
the cylinder calculus are carried out (`Work.K3Inputs.bridge_of_clauses`,
`Work.K3Inputs.not_sameCylinderField_of_cylinderRigid`).

This file connects the two:

* `StablyBirat_to_stablyBirational` — the instance-free relation implies the K3 chapter's
  (unpack the exponents, install the `Variety` instances of the products via
  `Work.K3Inputs.exists_variety_prodOver_affineSpace`, and use `PartialIso.toBirationalMap`);
* `not_stablyBirat_of_not_stablyBirational` — its contrapositive, the form in which Totaro's input
  is consumed;
* **`not_sameCylinderField_of_totaro`** — the *distinguishing* the `cInv` count needs, at the level
  of function fields: for the two centres `S`, `S'` of the K3 link, non-isomorphic `K`-trivial
  varieties of Picard number one, the cylinder fields `κ(S)(t)` and `κ(S')(t)` are *not*
  isomorphic, i.e. `S × ℙ¹` and `S' × ℙ¹` are not stably birational.  (This is precisely the input
  `¬ ResEquiv 𝕜 y x` of `Work.K3.K3Data`, since the two exceptional divisors of the link are
  `ℙ¹`-bundles over `S` and `S'`.)
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

/-- **The instance-free stable birationality implies the K3 chapter's relation.** -/
theorem StablyBirat_to_stablyBirational (X Y : Scheme.{0}) [Variety 𝕜 X] [Variety 𝕜 Y]
    (h : StablyBirat 𝕜 X Y) : Work.K3.StablyBirational 𝕜 X Y := by
  obtain ⟨n, m, hb⟩ := h
  obtain ⟨i⟩ := hb
  have hX : Variety 𝕜 (Work.K3.prodOver 𝕜 X (AffineN 𝕜 n)) :=
    Classical.choice (exists_variety_prodOver_affineSpace 𝕜 X n)
  have hY : Variety 𝕜 (Work.K3.prodOver 𝕜 Y (AffineN 𝕜 m)) :=
    Classical.choice (exists_variety_prodOver_affineSpace 𝕜 Y m)
  exact ⟨n, m, hX, hY, ⟨i.toBirationalMap⟩⟩

/-- The contrapositive: `¬ Work.K3.StablyBirational` gives `¬ StablyBirat`. -/
theorem not_stablyBirat_of_not_stablyBirational (X Y : Scheme.{0}) [Variety 𝕜 X] [Variety 𝕜 Y]
    (h : ¬ Work.K3.StablyBirational 𝕜 X Y) : ¬ StablyBirat 𝕜 X Y :=
  fun hb => h (StablyBirat_to_stablyBirational X Y hb)

/-- **The distinguishing needed by the `cInv` count, at the function-field level.**

For two non-isomorphic `K`-trivial varieties of Picard number one over `𝕜` (the two centres of
the K3 link), Totaro's corollary gives that they are not stably birational; if moreover the
cylinder rigidity (F2) holds, their cylinder function fields are *not* isomorphic:
`κ(S)(t) ≄ κ(S')(t)`, equivalently `S × ℙ¹` and `S' × ℙ¹` are not stably birational. -/
theorem not_sameCylinderField_of_totaro {S S' : Scheme.{0}} [Variety 𝕜 S] [Variety 𝕜 S']
    (hrigid : CylinderRigid 𝕜 S S') (T : Work.K3.TotaroInputAt 𝕜 S S')
    (h : ¬ Work.K3.IsoOver 𝕜 S S') : ¬ SameCylinderField 𝕜 S S' :=
  not_sameCylinderField_of_cylinderRigid hrigid
    (not_stablyBirat_of_not_stablyBirational S S' (T.not_stablyBirat h))

end

end Work.K3Inputs
