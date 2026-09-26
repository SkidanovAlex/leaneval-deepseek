import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.annulus_of_planeHypothesis
import Submission.Work.Smooth.SphereJordan.annulusClosureCore
import Submission.Work.Smooth.SphereJordan.strictClause_of_closureClause
import Submission.Work.Smooth.SphereJordan.annulusInjectionTwoCutsAlt

/-!
# Pardon's planar annulus theorem

`Work.Smooth.SphereJordan.annulusTheoremOfPlaneHypothesis`: the planar **annulus theorem** — the
region between a simple closed plane curve `γ`, whose trace lies in the open unit disc, and the
boundary circle of the disc is a standard annulus.  Concretely, for a planar Schoenflies datum `S`
of `γ` there is a homeomorphism `Θ` of the closed unit disc which fixes the boundary circle
pointwise, carries the bounded side `S.V` onto the open half-disc and its closure onto the closed
half-disc.

The three ingredients, all proved in this workspace:

* `annulusInjectionTwoCuts` — the classical "two cuts" construction: from the planar
  Jordan–Schoenflies theorem `PlaneHypothesis`, an *injective* continuous self-map `F` of `𝔻`, fixing
  `∂𝔻` pointwise and carrying (up to the orientation sign `s = ±1`) the circle of radius `1/2` onto
  the curve `γ`;
* `annulusClosureCore_of_injection` — the reduction of the injection to a homeomorphism (Brouwer:
  an injective self-map of `𝔻` fixing `∂𝔻` is surjective), with the uniqueness of the spanning disc
  identifying the image of the half-disc with `closure S.V`;
* `strictClause_of_closureClause` — the passage from the closed clause to the strict (open) clause.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

theorem annulusTheoremOfPlaneHypothesis (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    ∃ Θ : Work.Smooth.SphereJordan.Disc ≃ₜ Work.Smooth.SphereJordan.Disc,
      (∀ θ : ℝ, Θ (Work.Smooth.SphereJordan.circlePoint θ) = Work.Smooth.SphereJordan.circlePoint θ) ∧
      (∀ x : Work.Smooth.SphereJordan.Disc,
        (((x : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ S.V) ↔
        ‖((Θ x : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1 / 2) ∧
      (∀ x : Work.Smooth.SphereJordan.Disc,
        (((x : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ closure S.V) ↔
        ‖((Θ x : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2) := by
  obtain ⟨F, s, hs', hFinj, hFbd, hFim⟩ :=
    Work.Smooth.SphereJordan.annulusInjectionTwoCutsAlt h hs hball S
  obtain ⟨Θ, hfix, hcl⟩ :=
    Work.Smooth.SphereJordan.annulusClosureCore_of_injection hball S F s hs' hFinj hFbd hFim
  have hstrict := Work.Smooth.SphereJordan.strictClause_of_closureClause h hs hball S hfix hcl
  exact ⟨Θ, hfix, hstrict, hcl⟩

end

end Work.Smooth.SphereJordan
