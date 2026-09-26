import Submission.Work.Drive.EpsForm.tilted_endgame

/-!
# The tilted endgame consumed: Pardon's `ε`-conclusion from an essential loop off the tilted slab

`Work.Drive.EpsForm.tilted_endgame` (proved) turns a loop off a slightly tilted slab into the side
classification needed for Pardon's `doublebubble2`: every point of the loop is its own `ε`-witness for
one of the two solid half-boxes.  This module records the two lines that make it *consumable*: an
**essential** loop off the tilted slab gives the conclusion of the ε-form
(`Work.Drive.EpsForm.CruxCoreEpsBody` / `Work.Drive.CountingHalfEpsBody`, the solid form), because the
endgame's disjunct is exactly the shape of that conclusion with the loop itself as the witness.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive.EpsForm

/-- **The ε-conclusion (solid form) from an essential loop off the tilted slab.** -/
theorem epsConclusion_of_essentialLoop_sdiff_tiltedSlab {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h ε R : ℝ} (hε : 0 < ε) (hv1 : ‖v‖ = 1)
    (hv : ‖v - Work.BoxShrink.shiftVσ σ 1‖ ≤ ε)
    (hR : ∀ y ∈ Submission.PBox s c σ, ‖y - c‖ ≤ R) (hsize : ε * R < h)
    {γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ)}
    (hess : Work.CoreTopology.IsEssential (Work.Smooth.Morse.torus ψ) γ)
    (hγ : ∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ \
      Work.Drive.EpsForm.tiltedSlab (inner ℝ v c + u) v h) :
    (∃ γ' : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
        Work.CoreTopology.IsEssential (Work.Smooth.Morse.torus ψ) γ' ∧
          ∀ t : ℝ, ∃ x : R3, x ∈ Submission.PBox s c σ ∧ x (σ 2) < c (σ 2) + u ∧
            dist (γ' t) x < ε) ∨
      (∃ γ' : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
        Work.CoreTopology.IsEssential (Work.Smooth.Morse.torus ψ) γ' ∧
          ∀ t : ℝ, ∃ x : R3, x ∈ Submission.PBox s c σ ∧ c (σ 2) + u < x (σ 2) ∧
            dist (γ' t) x < ε) :=
  (Work.Drive.EpsForm.tilted_endgame ψ s c σ u hε hv1 hv hR hsize γ hγ).elim
    (fun h => Or.inl ⟨γ, hess, h⟩) (fun h => Or.inr ⟨γ, hess, h⟩)

end Work.Drive.EpsForm
