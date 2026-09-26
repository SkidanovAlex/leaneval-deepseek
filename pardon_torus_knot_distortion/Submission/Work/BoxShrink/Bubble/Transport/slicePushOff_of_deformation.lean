import Mathlib
import Submission.Work.BoxShrink.Bubble.Basic
import Submission.Work.SurgeryInvariance.All

/-!
# `SlicePushOff` from a deformation of the surface

This file proves the geometric input `Work.BoxShrink.Bubble.SlicePushOff` from an *ambient
deformation of the torus surface* which pushes the region inside the box off the slicing plane.

The hypothesis is a one-parameter family `H r : ℝ³ → ℝ³` of self-maps of `ℝ³`, continuous in
`(r, x)`, starting at the identity (`H 0 = id`), preserving the surface `F = P.carrier`
(`hHmem`), and at time `1` carrying the region inside the box into the union of the two
half-regions (`hHmaps`).  Then every loop of `F` inside `boxRegion` is carried by `H 1` to a loop
of `F` inside `upperRegion ∪ lowerRegion`, with the *same* winding vector: the family `H`
restricted to the loop is a homotopy of closed curves of `F`, so
`Work.SurgeryInvariance.WindingOf.homotopic_eq` applies.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.BoxShrink.Bubble.Transport

noncomputable section

theorem slicePushOff_of_deformation
    {P : Work.CoreTopology.ParamTorus} {s : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (H : ℝ → LeanEval.KnotTheory.PardonDistortion.R3 → LeanEval.KnotTheory.PardonDistortion.R3)
    (hHcont : Continuous (Function.uncurry H)) (hH0 : ∀ x, H 0 x = x)
    (hHmem : ∀ (r : ℝ) (x : LeanEval.KnotTheory.PardonDistortion.R3),
      x ∈ P.carrier → H r x ∈ P.carrier)
    (hHmaps : ∀ x, x ∈ Work.BoxShrink.Core.boxRegion P s c σ →
      H 1 x ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u) :
    Work.BoxShrink.Bubble.SlicePushOff P s c σ u := by
  intro k hk
  obtain ⟨γ, hγ, hk⟩ := (Work.BoxShrink.Bubble.mem_realizedWindings (P := P)
    (X := Work.BoxShrink.Core.boxRegion P s c σ)).mp hk
  have hper : ∀ t : ℝ, γ (t + 2 * Real.pi) = γ t := γ.periodic
  refine ⟨{ γ := fun t => H 1 (γ t),
            cont := hHcont.comp (continuous_const.prodMk γ.cont),
            periodic := fun t => by
              show H 1 (γ (t + 2 * Real.pi)) = H 1 (γ t); rw [hper t],
            mem := fun t => hHmem 1 (γ t) (γ.mem t) }, ?_, ?_⟩
  · intro t; exact hHmaps (γ t) (hγ t)
  · have hhom : Work.CoreTopology.Homotopic P γ
        { γ := fun t => H 1 (γ t),
          cont := hHcont.comp (continuous_const.prodMk γ.cont),
          periodic := fun t => by
            show H 1 (γ (t + 2 * Real.pi)) = H 1 (γ t); rw [hper t],
          mem := fun t => hHmem 1 (γ t) (γ.mem t) } := by
      refine ⟨fun r t => H r (γ t), ?_, ?_, ?_, ?_, ?_⟩
      · exact hHcont.comp (continuous_fst.prodMk (γ.cont.comp continuous_snd))
      · intro r t; exact hHmem r (γ t) (γ.mem t)
      · intro t; exact hH0 (γ t)
      · intro t; rfl
      · intro r t
        show H r (γ (t + 2 * Real.pi)) = H r (γ t); rw [hper t]
    have := Work.SurgeryInvariance.WindingOf.homotopic_eq (P := P) hhom
    exact this.symm.trans hk

end

end Work.BoxShrink.Bubble.Transport
