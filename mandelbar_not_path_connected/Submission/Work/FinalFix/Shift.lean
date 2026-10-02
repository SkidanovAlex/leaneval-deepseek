/-
# `Work.FinalFix.Shift` — the Abel equation (`φa_shift`) of the parabolic flower

Area `Submission/Work/FinalFix/` of the mandelbar project.  This module fixes the *named
interface* of the attracting Fatou coordinate of the Leau–Fatou flower that the root-arc data
consumes:

> **`φa_shift`** — `fl.φa (F z) = fl.φa z + 1` for every `z` in the petal `fl.Pa`.

This is the field that `NOTES_LEAD_mandelbar_residuals.md` §3.1 asks the `FatouCoordFix` area to
add to the flower (it is the field `Work.FQC.PetalInput.φa_shift` of the `FQC` area, restated
there for the deformation), and it replaces the *false* interface hypothesis
`Set.MapsTo g fl.Pa fl.Pa`: the wide petal `Pa` of the constructed flower is not invariant under
the antiholomorphic square root `g (W) ≈ conj W + conj b` when `|Im b| > 1/2`, while the Abel
equation for the *second* return map `F = g ∘ g` does hold on `Pa` for the construction (where
`φa` is the honest attracting coordinate, `orbitCoord`).

`Work.Final.RootArc.phi_comp`, `phi_iterate`, `ecalleHeightAt_eq` and
`critHeight_eq_ecalleHeightAt` (in `Submission/Work/Final/RootArc.lean`) are stated with this
hypothesis; `Work.FinalFix.HasPhiShift.of_comp_self` records that the old hypothesis still
suffices *when it happens to hold*, so nothing that was provable before is lost.
-/
import Submission.Work.FatouCoord.Flower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.FinalFix

/-- **The Abel equation of the flower** (`φa_shift`): the attracting Fatou coordinate translates
by `1` along the second return map `F` on the petal. -/
def HasPhiShift (F g : ℂ → ℂ) {z₀ : ℂ} (fl : Work.FatouCoord.ParabolicFlower F g z₀) : Prop :=
  ∀ z ∈ fl.Pa, fl.φa (F z) = fl.φa z + 1

theorem hasPhiShift_iff {F g : ℂ → ℂ} {z₀ : ℂ}
    {fl : Work.FatouCoord.ParabolicFlower F g z₀} :
    HasPhiShift F g fl ↔ ∀ z ∈ fl.Pa, fl.φa (F z) = fl.φa z + 1 := Iff.rfl

/-- `φa_shift` only depends on the petal and on the Fatou coordinate: two flower records with the
same `Pa` and `φa` satisfy it simultaneously.  (This is how the statement transfers between the
`FatouCoord` flower and any sibling record, e.g. a version restated on the `g`-invariant
sub-petal `Pg` of `FatouCoordFix`.) -/
theorem HasPhiShift.transfer {F g : ℂ → ℂ} {z₀ : ℂ}
    {fl₁ fl₂ : Work.FatouCoord.ParabolicFlower F g z₀} (hPa : fl₁.Pa = fl₂.Pa)
    (hφa : fl₁.φa = fl₂.φa) (h : HasPhiShift F g fl₁) : HasPhiShift F g fl₂ := by
  intro z hz
  have hz' : z ∈ fl₁.Pa := by rw [hPa]; exact hz
  have h1 := h z hz'
  rwa [hφa] at h1

/-- **The old interface hypothesis still gives the Abel equation.**  If the antiholomorphic
square root `g` happens to preserve the petal `Pa` (the hypothesis that
`NOTES_LEAD_mandelbar_residuals.md` §3.1 identifies as false in general), then squaring the
antiholomorphic relation `φa ∘ g = conj ∘ φa + 1/2` gives `φa ∘ F = φa + 1`. -/
theorem HasPhiShift.of_comp_self {F g : ℂ → ℂ} {z₀ : ℂ}
    {fl : Work.FatouCoord.ParabolicFlower F g z₀} (h : MapsTo g fl.Pa fl.Pa)
    (hgg : F = g ∘ g) : HasPhiShift F g fl := by
  subst hgg
  exact fun _ hz => (fl.φa_fatou.1.comp_self h).2 _ hz

end Work.FinalFix
