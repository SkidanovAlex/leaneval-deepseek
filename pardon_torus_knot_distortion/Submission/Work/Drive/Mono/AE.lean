import Mathlib
import Submission.Work.Drive.Final.crux_core_wd
import Submission.Work.BoxShrink.cruxAE
import Submission.Work.Drive.cleansDiscsAllWd
import Submission.Work.Drive.pardon_of_cleansW_sphere

/-!
# Pardon's crux at almost every cutting level, and the reduction of the challenge to it

The workspace's chain to Pardon's distortion bound reduces the challenge to Pardon's **crux**
(`Work.Drive.Final.CruxCoreWd`): at every configuration carrying the counting data of the pinching
family, and for **every** plane level `u` with `|u| < ε r`, one of the two open halves of the box
cut by the plane `{y (σ 2) = c (σ 2) + u}` contains an essential loop of the surface.

Pardon himself never needs the statement at *every* level: he chooses his cutting plane in general
position (his "technical convenience").  The counting of the pinching family is only available when
the plane level avoids the *critical values* of the height `y (σ 2) ∘ K` restricted to the box —
at a tangency the knot can graze the slab, which no count of the crux controls (see
`Submission/Work/Drive/Mono/NOTES_H381_count_decoration.md` §4bis).  The workspace has the
machinery to make that choice: `Work.BoxShrink.exists_plane_level_of_ae` produces a level `u` that
lies *simultaneously* in an arbitrary conull set `A` and where the one-dimensional coarea bound (the
count `hU` of the crux) holds.

This file records the resulting **strict weakening of the crux**:

* `Work.Drive.Mono.CruxCoreWdAE` — the same statement as `Work.Drive.Final.CruxCoreWd` except that
  the plane level is required only for almost every `u`;
* `Work.Drive.Mono.cruxCoreWdAE_of_cruxCoreWd` — the ordinary crux implies its a.e. form (so every
  route to `CruxCoreWd` remains available);
* `Work.Drive.Mono.boxShrink_of_cruxCoreWdAE` and `Work.Drive.Mono.pardon_of_cruxCoreWdAE` — the
  a.e. form **suffices** for the challenge: the level `u` is chosen from the conull set by
  `exists_plane_level_of_ae` (after the level `s` and its sphere have been produced by
  `Work.BoxShrink.SweepNice.of_aeAll`, whose own pigeonhole level `u` is discarded), and the exact
  half-box loop is converted to Pardon's box shrink by `hasEssBox_of_upperHalf` /
  `hasEssBox_of_lowerHalf`.
-/

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set
open scoped ENNReal Topology

namespace Work.Drive.Mono

noncomputable section

/-- **Pardon's crux at almost every cutting level.**  Identical to
`Work.Drive.Final.CruxCoreWd` except that the plane level `u` is required only on a conull set: the
conclusion must hold for almost every `u` with `|u| < ε r` satisfying the count `hU`.

This is the honest form of the crux for the *counting* route: the count `hU` at a tangency of the
knot with the plane controls nothing, so the level must be chosen in general position, and the
machinery of `Work.BoxShrink.exists_plane_level_of_ae` makes that choice compatible with the sweep
of the box. -/
def CruxCoreWdAE (p q : ℕ) : Prop :=
  ∀ (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
            Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
          ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
        ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
          |u| < Submission.eps * r →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          (∃ γ : Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ),
              Work.CoreTopology.IsEssential _ γ ∧
                ∀ t : ℝ, γ t ∈ Submission.PBox s c σ ∧ γ t (σ 2) < c (σ 2) + u) ∨
          (∃ γ : Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ),
              Work.CoreTopology.IsEssential _ γ ∧
                ∀ t : ℝ, γ t ∈ Submission.PBox s c σ ∧ c (σ 2) + u < γ t (σ 2))

/-- **The ordinary crux implies its almost-everywhere form.** -/
theorem cruxCoreWdAE_of_cruxCoreWd (h : ∀ p q : ℕ, Work.Drive.Final.CruxCoreWd p q) :
    ∀ p q : ℕ, CruxCoreWdAE p q := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hS
  exact Filter.Eventually.of_forall fun u hu hU =>
    h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU

/-- **The challenge from the a.e. crux**: the cutting level is chosen in the conull set by
`Work.BoxShrink.exists_plane_level_of_ae`, the box level `s` and its sphere come from
`Work.BoxShrink.SweepNice.of_aeAll`, and the exact half-box loop is converted into Pardon's box
shrink by `hasEssBox_of_upperHalf` / `hasEssBox_of_lowerHalf`. -/
theorem boxShrink_of_cruxCoreWdAE (hcl : Work.Drive.CleansDiscsAllWd)
    (h : ∀ p q : ℕ, CruxCoreWdAE p q) : ∀ p q : ℕ, Submission.BoxShrinkStatement p q := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall r hr c σ hbox
  obtain ⟨s, hs, hslice, hS, -, -⟩ :=
    Work.BoxShrink.SweepNice.of_aeAll
      (Work.Smooth.OneManifold.aeSlicedAll_of_planeHypothesis
        Work.Smooth.Schoenflies.planeHypothesis)
      p q hp hq hc ψ K d hd hbound himg hsmall r hr c σ
  have hs0 : 0 < s := lt_trans hr hs.1
  have hsle : s ≤ (1 + Submission.eps) * r := le_of_lt hs.2
  obtain ⟨u, hu, huA, hU⟩ :=
    Work.BoxShrink.exists_plane_level_of_ae K c σ hd hbound hr hs0 hsle
      (h p q hp hq hc ψ K d hd hbound himg hsmall (hcl ψ) r hr c σ hbox s hs.1 hs.2 hslice hS)
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
/-- **Pardon's distortion bound for torus knots from the a.e. crux.** -/
theorem pardon_of_cruxCoreWdAE (h : ∀ p q : ℕ, CruxCoreWdAE p q)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
    (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
      ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)) :
    (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  Submission.theorem_of_core
    (Submission.CoreStatement_of_boxShrink
      (boxShrink_of_cruxCoreWdAE Work.Drive.cleansDiscsAllWd h))
    p q hp hq hc K hclass

end

end Work.Drive.Mono
