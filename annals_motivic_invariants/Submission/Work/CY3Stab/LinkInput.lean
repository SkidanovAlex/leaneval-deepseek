import Submission.Work.CY3Stab.Defs
import Submission.Work.K3Inputs.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.LinkInput` — the `ℙ¹`-bundle structure of the CY3 link, at the cylinder level

The cylinder rigidity which the paper's stabilisation step needs — that the two exceptional
divisors of the link, after multiplication by `𝔸ᵏ`, still detect the non-stable-birationality of
the two K-trivial centres — follows from the *geometric* fact recorded in the K3 area as clue (F1):
each exceptional divisor of the L-link is a `ℙ¹`-bundle over its centre, i.e. its function field is
`κ(Z)(t)` (resp. `κ(Z')(t)`).

This file records that structure for the CY3 link (`CY3P1Bundle`), in exactly the shape of
`Work.K3Inputs.IsP1BundleOver`; with it, the residue-field comparison at the two cylinder points
becomes a *consequence* of `Work.CY3.TotaroInput` (`not_stablyBirat_of_not_iso`) and the delivered
cancellation `Work.CY3Stab.Prod.stablyBirational_of_resEquiv_cyl_of_p1Bundle` — see
`Submission/Work/CY3Stab/NOTES.md` §6.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.CY3Stab

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **(F1) for the CY3 link.**  The two exceptional divisors of the link are `ℙ¹`-bundles over the
two K-trivial threefolds of Picard rank one: `κ(y) ≅ κ(Z)(t)` and `κ(x) ≅ κ(Z')(t)` (paper
`lemma:L-link` (2) with `(L3)`).  This is a *named geometric input* in the same shape as the K3
area's `Work.K3Inputs.IsP1BundleOver`; it is what makes the two centres detectable after
multiplication by `𝔸ᵏ`. -/
structure CY3P1Bundle (𝕜 : Type) [Field 𝕜] (D : Work.CY3.CY3Data 𝕜) : Prop where
  /-- the target exceptional divisor `y` is a `ℙ¹`-bundle over `Z` -/
  isP1Bundle_y : Work.K3Inputs.IsP1BundleOver 𝕜 D.y D.Z
  /-- the source exceptional divisor `x` is a `ℙ¹`-bundle over `Z'` -/
  isP1Bundle_x : Work.K3Inputs.IsP1BundleOver 𝕜 D.x D.Z'

/-- **How a producer supplies (F1) for the exceptional divisor `y`**: it suffices to know that the
model `ZW` of the base point is a model of `Z × ℙ¹`, i.e. that `κ(z₀) ≅ RatFunc κ(Z)`, because
`CY3Data.resEquiv_y` identifies `κ(y)` with `κ(z₀)`.  (The `ℙ¹`-bundle form for `x` and `Z'` has no
counterpart in `CY3Data` and must be supplied by the construction of the link.) -/
theorem isP1BundleOver_y_of_z₀ {𝕜 : Type} [Field 𝕜] (D : Work.CY3.CY3Data 𝕜)
    (h : Work.K3Inputs.IsP1BundleOver 𝕜 D.z₀ D.Z) :
    Work.K3Inputs.IsP1BundleOver 𝕜 D.y D.Z := by
  obtain ⟨e₁, he₁⟩ := D.resEquiv_y
  obtain ⟨e₂, he₂⟩ := h
  refine ⟨e₁.trans e₂, ?_⟩
  rw [RingEquiv.toRingHom_trans', RingHom.comp_assoc, he₁, he₂]

end

end Work.CY3Stab
