/-
# ELRig — the main theorem `equatorLeak`

The equator-curve rigidity (EL part 4): the main theorem of the EL argument in the form consumed
by the mandelbar drive.

* `equatorLeak` : at a root-parabolic parameter `c` with its Fatou flower `fl`, the nest `nest` at
  the parabolic point, the lift data `L` of the two root rays and the tripod data `tr` at `b₂`,
  the equator `E = Ψ '' ℝ` of the repelling coordinate cannot be contained in the filled Julia
  set `K c`: there is a real `x` with `Ψ x ∉ K c`.

The proof is by contradiction: `Work.ELRig.rigidity` (R-f of the contract) is the statement that
`E ⊆ K c` is impossible.

The hypotheses after `fl` are **not** extra mathematical assumptions: they are the outputs of the
sibling work packages.  `nest : Z1Nest` and `tr : B2Data` are the outputs of ELNest/ELPull
(the nested pairs at `z₁`, the tripod at `b₂`, the certificate `C7`), and `L : RayLift` collects
R-a2 — see `Submission/Work/ELRig/RayLift.lean` for the provenance of each of its fields; only
`noReturn₁`/`noReturn₂` there are genuinely new input (the two rays meet the repelling petal in a
single arc, i.e. they project to simple closed curve in the Ecalle cylinder).  Everything else —
the plane topology `LiftSides` of the three regions, the identification of the `Ψ`-preimages of
the pair curve with the two lifts, the avoidance level, the petal side — is derived here.
-/
import Submission.Work.ELRig.Inputs
import Submission.Work.ELRig.RayLift
import Submission.Work.ELRig.Assembly
import Submission.Work.ELRig.rigidity
import Submission.Work.ELRig.Assembly
import Submission.Work.ELRig.exists_liftCurvesV3

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

namespace Work.EL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The main theorem of the equator-curve rigidity.**  At a root-parabolic parameter `c`, given
the Fatou flower of the parabolic point `z₁`, the nest at `z₁`, the lift data of the two root rays
and the tripod data at `b₂`, the equator `E = Ψ '' ℝ` of the repelling coordinate is not contained
in the filled Julia set: some point `Ψ x` of the equator is outside `K c`.  In this form the plane
topology `LiftSides` is supplied by the caller. -/
theorem equatorLeak_of_liftSides (hJ : Work.Top.JordanForm) {c : ℂ} (d : RootParabolic c)
    (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Z1Nest d.hN d.z₁ fl.Pa)
    (L : Work.ELRig.RayLift d fl)
    (lift : LiftSides d.hN d.z₁ L.γ₁ L.γ₂ L.R L.R₀)
    (tr : B2Data d.hN d.z₁) :
    ∃ x : ℝ, fl.Ψ (x : ℂ) ∉ K c := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact Work.ELRig.rigidity (c := c) d fl nest L.pa_ends
    (htail_of_nest d fl nest L h) tr h

/-- **The main theorem, in the contradiction-free form**, with the plane topology supplied by the
caller. -/
theorem equatorLeak_contra_of_liftSides (hJ : Work.Top.JordanForm) {c : ℂ} (d : RootParabolic c)
    (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Z1Nest d.hN d.z₁ fl.Pa)
    (L : Work.ELRig.RayLift d fl)
    (lift : LiftSides d.hN d.z₁ L.γ₁ L.γ₂ L.R L.R₀)
    (tr : B2Data d.hN d.z₁)
    (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ K c) : False :=
  Work.ELRig.rigidity (c := c) d fl nest L.pa_ends
    (htail_of_nest d fl nest L hE) tr hE

/-- **The main theorem, in the contradiction-free form** (contract signature). -/
theorem equatorLeak_contra (hJ : Work.Top.JordanForm) {c : ℂ} (d : RootParabolic c)
    (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Z1Nest d.hN d.z₁ fl.Pa)
    (L : Work.ELRig.RayLift d fl)
    (tr : B2Data d.hN d.z₁)
    (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ K c) : False :=
  equatorLeak_contra_of_liftSides hJ d fl nest L (L.liftSidesOf hE) tr hE

/-- **The main theorem of the equator-curve rigidity** (the contract's `equatorLeak`): the only
inputs beyond the root-parabolic data `d` and the flower `fl` are the nest `nest` at `z₁`
(ELNest), the lift data `L` of the two root rays (R-a2, `Work.ELRig.RayLift`) and the tripod data
`tr` at `b₂` (ELNest/ELPull).  Everything else is derived here: the plane topology `LiftSides`
(`RayLift.liftSidesOf`), the identification of the `Ψ`-preimages of the pair curve with the two
lifts (`RayLift.preimage_subset`), the petal side and the avoidance level (the flower's
`Ψ_ends`/`Ψ_small`), and R-a3 (`htail_of_nest`). -/
theorem equatorLeak (hJ : Work.Top.JordanForm) {c : ℂ} (d : RootParabolic c)
    (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Z1Nest d.hN d.z₁ fl.Pa)
    (L : Work.ELRig.RayLift d fl)
    (tr : B2Data d.hN d.z₁) :
    ∃ x : ℝ, fl.Ψ (x : ℂ) ∉ K c := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact equatorLeak_contra hJ d fl nest L tr h

/-- **The main theorem with the residual strand statement as the only input beyond the sibling
areas**: `nest` (ELNest), `tr` (ELNest/ELPull), and `hstrand : ∀ R, RayStrand d fl R` — R-a2's
"the two root rays meet the repelling half plane `{Re < -R}` in a single level-transversal arc"
(equivalently: they project to simple closed curves in the Ecalle cylinder).  This is the contract's
`equatorLeak (hJ) (d) (fl)` up to that one named statement. -/
theorem equatorLeak_of_strand (hJ : Work.Top.JordanForm) {c : ℂ} (d : RootParabolic c)
    (fl : ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁)
    (nest : Z1Nest d.hN d.z₁ fl.Pa)
    (tr : B2Data d.hN d.z₁)
    (hstrand : ∀ R : ℝ, Work.ELRig.RayStrand d fl R) :
    ∃ x : ℝ, fl.Ψ (x : ℂ) ∉ K c := by
  have h₁ : LandsN d.hN alpha1 d.z₁ := by
    rw [← nest.P0_spec.2.2, ← nest.P0_spec.1]; exact nest.P0.lands_a
  have h₂ : LandsN d.hN alpha2 d.z₁ := by
    rw [← nest.P0_spec.2.2, ← nest.P0_spec.2.1]; exact nest.P0.lands_b
  obtain ⟨L⟩ := exists_rayLift d fl h₁ h₂ hstrand
  exact equatorLeak hJ d fl nest L tr

end Work.EL
