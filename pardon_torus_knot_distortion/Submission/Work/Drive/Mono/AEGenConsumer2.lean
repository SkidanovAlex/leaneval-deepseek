import Mathlib
import Submission.Work.Drive.Mono.AEGen2
import Submission.Work.Drive.Mono.exists_level_of_ae_count

/-!
# The challenge from the crux with the junction genericity `CruxCoreWdAEG2`

`Work.Drive.Mono.CruxCoreWdAEG2` (`Mono/AEGen2.lean`) is Pardon's crux with the cutting level
required only almost everywhere and the box level required to be in general position *for the
junction route* (`Work.Drive.Mono.BoxGenE`).  This file proves that it suffices for the challenge,
exactly as `Mono/AEGenConsumer.lean` does for `CruxCoreWdAEG`; the only change is that the box level
is chosen inside the conull set of `BoxGenE` at a **shifted** centre `c'`:

* the shift `c' = c + τ • diagVec` of the centre is harmless because `HasEssBox` is open in the
  centre (`Work.Drive.Mono.boxGenE_pairSard`, G4 of the lead's `NOTES_LEAD_junctionGen.md`), and
  `Submission.BoxShrinkStatement`'s conclusion does not mention the centre;
* for a.e. shift `τ` and a.e. level `s` the shifted box satisfies `BoxGenE` (G1, G3 of
  `boxGenE_pairSard` and G2 `Work.Drive.Mono.ae_faceNoBend`, combined with the proved
  `Work.Drive.Mono.ae_boxGen`);
* the rest is the old proof at the new centre.

The shift property is isolated as the hypothesis `hboxshift`
(`∃ c', HasEssBox P r c' σ ∧ ∀ᵐ s, BoxGenE ψ c' σ s`), which is the only thing the G1–G5 inputs
have to supply. -/
open LeanEval.KnotTheory.PardonDistortion
open Set MeasureTheory
open scoped ENNReal Topology

namespace Work.Drive.Mono

noncomputable section

/-- **The generic-centre property**: at every box there is a centre, arbitrarily close in spirit to
the given one, at which `HasEssBox` still holds and `BoxGenE` holds for almost every level.  This is
the conjunction of G4 and G5 of the lead's design note. -/
def ShiftGoodCentre : Prop :=
  ∀ (ψ : Submission.Diffeo) (r : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)),
    Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ →
    ∃ c' : R3, Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c' σ ∧
      ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), BoxGenE ψ c' σ s

/-- **The box shrink from the `BoxGenE`-general-position a.e. crux.** -/
theorem boxShrink_of_cruxCoreWdAEG2 (hcl : Work.Drive.CleansDiscsAllWd)
    (h : ∀ p q : ℕ, CruxCoreWdAEG2 p q) (hboxshift : ShiftGoodCentre) :
    ∀ p q : ℕ, Submission.BoxShrinkStatement p q := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall r hr c σ hbox
  obtain ⟨c', hbox', hBG'⟩ := hboxshift ψ r c σ hbox
  have hP : ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      (BoxGenE ψ c' σ s ∧ Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
        {y : R3 | Submission.boxNorm c' σ y = s}) :=
    hBG'.and
      (Work.Smooth.OneManifold.aeSlicedAll_of_planeHypothesis
        Work.Smooth.Schoenflies.planeHypothesis ψ c' σ)
  obtain ⟨s, hs, ⟨hBG, hslice⟩, hS⟩ :=
    exists_level_of_ae_count K hd hbound r hr c' σ
      (fun s => BoxGenE ψ c' σ s ∧ Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
        {y : R3 | Submission.boxNorm c' σ y = s}) hP
  have hs0 : 0 < s := lt_trans hr hs.1
  have hsle : s ≤ (1 + Submission.eps) * r := le_of_lt hs.2
  obtain ⟨u, hu, huA, hU⟩ :=
    Work.BoxShrink.exists_plane_level_of_ae K c' σ hd hbound hr hs0 hsle
      (h p q hp hq hc ψ K d hd hbound himg hsmall (hcl ψ) r hr c' σ hbox' s hs.1 hs.2 hslice hBG hS)
  have hu' : |u| < Submission.eps * r := abs_lt.mpr hu
  rcases huA hu' hU with hup | hlow
  · exact ⟨_, _, Work.BoxShrink.hasEssBox_of_upperHalf
      (P := Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
      hr hs.1 hs.2 hu' hup⟩
  · exact ⟨_, _, Work.BoxShrink.hasEssBox_of_lowerHalf
      (P := Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
      hr hs.1 hs.2 hu' hlow⟩

open LeanEval.KnotTheory.PardonDistortion in
open scoped ENNReal in
/-- **Pardon's distortion bound for torus knots from the `BoxGenE`-general-position a.e. crux.** -/
theorem pardon_of_cruxCoreWdAEG2 (h : ∀ p q : ℕ, CruxCoreWdAEG2 p q)
    (hboxshift : ShiftGoodCentre)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
    (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
      ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)) :
    (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Submission.theorem_of_core
    (Submission.CoreStatement_of_boxShrink
      (boxShrink_of_cruxCoreWdAEG2 Work.Drive.cleansDiscsAllWd h hboxshift))
    p q hp hq hc K hclass

end

end Work.Drive.Mono
