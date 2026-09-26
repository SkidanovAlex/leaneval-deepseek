import Mathlib
import Submission.Work.Drive.Mono.Residual
import Submission.Work.Drive.Mono.Split
import Submission.Work.Drive.Final.sweep_mono
import Submission.Work.Drive.Mono.TiltedTraceDataWExists_holds

/-!
# The residual of Pardon's sweep in the form Pardon's own argument produces it

`Work.Drive.Mono.Residual` states the residual of the tilted sweep as the existence, at every crux
configuration, of tilt data together with the *trace data* `TiltedTraceDataW` (clause 1: the trace of
every non-exceptional level is a family of pairwise disjoint simple inessential closed curves;
clause 2: the genericity of the sweep height at the box sphere; clause 4: the no-jump at the
exceptional levels, i.e. Pardon's `2`-surgery count at the pinch).

The present file records a **strictly more economical form of the same residual**, which is the form
in which Pardon's argument actually produces the result:

> at every crux configuration there are tilt data (a thin slab) at which the winding span of the
> level region of the sweep is **constant** over the window,
> `W (region lam) = W (region lam0)` for every `lam ∈ [lam0, lam1]`.

Why this is the honest form:

* Pardon's proof of the persistence of the essential loop (`spherefamily`, Annals 174 (2011)) runs
  through *his* Lemma 2 (`mustbeinessential`): every sphere of the pinching family meets the knot in
  fewer than `I(F,β)` points, so every curve of `S_t ∩ F` **bounds a disc of `F`**; the invariant
  `W (F ∩ int S_t)` is then constant along the family, with no dichotomy and no `1`-Lipschitz bound
  (`Work.SurgeryInvariance.Sweep.windingSpan_eq`, `SurgeryStepZero.windingSpan_eq`, both proved).
  In the tilted-sweep vocabulary the same argument gives the constancy of `lam ↦ W (region lam)`:
  the level-jump identity `Work.Drive.Final.openTiltedSweepRegion_eq_union_strip_wall` splits
  `region μ = region ν ∪ strip ∪ wall_ν` for `μ < ν`, and the traces of the sweep (the wall
  `sweepWall` and the slab faces) are peeled off by Pardon's Lemma 2.
* Consequently **none of the machinery of `TiltedTraceDataW` is needed**: no local model of the trace
  (no `IsLocallyEuclidean`), no clause 2, and in particular **no clause 4** --- the pinch, i.e. the
  no-jump at the exceptional levels, is *vacuous* at a datum whose sweep span never vanishes, and
  the constancy gives exactly that.  The file `NOTES_H463_synthesis.md` of this directory records the
  audit behind this claim, including a machine-checkable obstruction showing that the constancy can
  *not* be deduced from the vanishing of the winding spans of the walls alone (an arcs/closure-chain
  phenomenon: for an arc, "zero winding span" is vacuous), so the counting enters through the
  disc-bounding form of Pardon's Lemma 2.

The reduction proved below is `SweepSpanConst → TiltedSweepMono`: the two fields `(D)` (the dichotomy
at the non-exceptional levels) and `(L)` (no level of vanishing span is reached from `⊤` just below)
of `TiltedSweepMono` are immediate consequences of the constancy and of
`W (region lam0) = ⊤`, which the crux's hypotheses supply.
-/

open LeanEval.KnotTheory.PardonDistortion
open scoped ENNReal

namespace Work.Drive.Mono

noncomputable section

/-- **The residual of the tilted sweep, in the constancy form.**  At every crux configuration there
are tilt data (in particular a *thin* slab, so that the sweep really cuts the box) at which the
winding span of the level region of the sweep is constant over the window.

This is the form of the residual which Pardon's own argument (Lemma 2 `mustbeinessential` + the
persistence of the essential loop) produces; see the module docstring. -/
def SweepSpanConst : Prop :=
  ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
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
        ∀ (u : ℝ) (_hu : |u| < Submission.eps * r),
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
            ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          ∃ (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
            TiltData ψ s c σ u v h R ℓ exc lam0 lam1 ∧
            ∀ lam ∈ Set.Icc lam0 lam1,
              Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
                  (Work.Drive.EpsFormSphere.openTiltedSweepRegion
                    (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) =
                Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
                  (Work.Drive.EpsFormSphere.openTiltedSweepRegion
                    (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam0)

/-- **The constancy form of the residual implies Pardon's tilted sweep `TiltedSweepMono`.**

The two fields of `TiltedSweepMono` are:

* `(D)` the dichotomy `W (region lam) = ⊥ ∨ W (region lam) = ⊤` at every non-exceptional level.
  With the constancy, `W (region lam) = W (region lam0)`, and `W (region lam0) = ⊤` because the
  level `lam0` is below the `ℓ`-range of the box, so the region there *is* the box region
  (`openTiltedSweepRegion_eq_boxRegion`), which contains an essential loop by `HasEssBox`
  (`containsEssentialLoop_boxRegion_of_hasEssBox`), while the box sphere carries no essential loop
  (`sphereTrace_inessential_of_countsWd`, the crux's count `hS`), so its span is `⊤`
  (`windingSpan_boxRegion_eq_top_of_sphereTrace_inessential`).
* `(L)` no level of vanishing span is reached from `⊤` just below.  This is *vacuous* under the
  constancy: no level of the window has vanishing span, since all of them have span
  `W (region lam0) = ⊤`. -/
theorem tiltedSweepMono_of_sweepSpanConst (h : SweepSpanConst) :
    Work.Drive.Final.TiltedSweepMono := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  have hd1 : 1 ≤ d := Work.Drive.EpsForm.distortionBound_one_le K d hbound
  obtain ⟨v, h, R, ℓ, lam0, lam1, exc, hdata, hconst⟩ :=
    h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  obtain ⟨hgen, hv1, hℓne, hℓv, hsize, hh, hRbox, hlow, hhigh, hl, hexc⟩ := hdata
  -- the start of the window has full span
  have hs0 : 0 < s := lt_trans hr hrs
  have hnoS : ¬ (Work.Drive.EpsSphere.torusOf ψ).ContainsEssentialLoop
      (Work.BoxShrink.Core.sphereSet c σ s) :=
    Work.EpsW.sphereTrace_inessential_of_countsWd p q hp hq hc ψ K hd himg hsmall hs0 c σ hslice
      hcl hS
  have hne : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
      (Work.BoxShrink.Core.boxRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ) ≠ ⊥ :=
    (Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mpr
      (Work.BoxShrink.Core.containsEssentialLoop_boxRegion_of_hasEssBox (le_of_lt hrs) hbox)
  have hstart : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion
        (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam0) = ⊤ := by
    rw [Work.Drive.EpsFormSphere.openTiltedSweepRegion_eq_boxRegion hlow]
    exact Work.Drive.EpsForm.windingSpan_boxRegion_eq_top_of_sphereTrace_inessential hs0 hslice
      hnoS hne
  refine ⟨v, h, R, ℓ, lam0, lam1, exc, hv1, hsize, hh, hRbox, hlow, hhigh, hl, hexc, ?_, ?_⟩
  · -- (D) the dichotomy at the non-exceptional levels, from the constancy
    intro lam hlam _
    rw [hconst lam hlam, hstart]
    exact Or.inr rfl
  · -- (L) the no-jump, vacuous because no level of the window has vanishing span
    intro lam hlam hbot
    have htop : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion
          (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊤ := by
      rw [hconst lam hlam, hstart]
    exact absurd (htop.symm.trans hbot) top_ne_bot


/-! ## The trace-data form of the residual implies the constancy form

The two residual forms are related: `TiltedTraceDataWExists` (clauses 1, 2 and 4 at the chosen data)
implies `SweepSpanConst`.  The dichotomy of clause 1 and the no-jump of clause 4 give, together with
the first field of `TiltedSweepMono`, that *no* level of the window has vanishing span
(`windingSpan_ne_bot_of_tiltedTraceDataW`); at a non-exceptional level the dichotomy of clause 1 then
makes the span `⊤`, and at an exceptional level the span is `⊤` as well, because it dominates the span
of a non-exceptional level just above it.  Hence the span takes the value `⊤` at every level of the
window, and the constancy follows. -/
theorem sweepSpanConst_of_tiltedTraceDataWExists (h : TiltedTraceDataWExists) : SweepSpanConst := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  set P := Work.Drive.EpsSphere.torusOf ψ with hP
  obtain ⟨v, h, R, ℓ, lam0, lam1, exc, hdata, hW⟩ :=
    h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
  obtain ⟨hgen, hv1, hℓne, hℓv, hsize, hh, hRbox, hlow, hhigh, hl, hexc⟩ := hdata
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv1
    exact one_ne_zero hv1.symm
  have hs0 : 0 < s := lt_trans hr hrs
  have hnoS : ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) :=
    Work.EpsW.sphereTrace_inessential_of_countsWd p q hp hq hc ψ K hd himg hsmall hs0 c σ hslice
      hcl hS
  have hne : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.boxRegion P s c σ) ≠ ⊥ :=
    (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr
      (Work.BoxShrink.Core.containsEssentialLoop_boxRegion_of_hasEssBox (le_of_lt hrs) hbox)
  have hstart : Work.SurgeryInvariance.WindingSpan P
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam0) = ⊤ := by
    rw [Work.Drive.EpsFormSphere.openTiltedSweepRegion_eq_boxRegion hlow]
    exact Work.Drive.EpsForm.windingSpan_boxRegion_eq_top_of_sphereTrace_inessential hs0 hslice
      hnoS hne
  have hneBot : ∀ lam ∈ Set.Icc lam0 lam1,
      Work.SurgeryInvariance.WindingSpan P
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam) ≠ ⊥ :=
    fun lam hlam => Work.Drive.Mono.windingSpan_ne_bot_of_tiltedTraceDataW (P := P)
      hv1 hℓne hℓv hW hstart lam hlam
  refine ⟨v, h, R, ℓ, lam0, lam1, exc,
    ⟨hgen, hv1, hℓne, hℓv, hsize, hh, hRbox, hlow, hhigh, hl, hexc⟩, ?_⟩
  intro lam hlam
  have htop : ∀ nu ∈ Set.Icc lam0 lam1, nu ∉ (exc : Set ℝ) →
      Work.SurgeryInvariance.WindingSpan P
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ nu) = ⊤ := by
    intro nu hnu hne'
    rcases windingSpan_bot_or_top_of_traceCurvesAt (P := P) hvne hℓv hℓne
      (hW.1 nu hnu hne') with hbot | htop'
    · exact absurd hbot (hneBot nu hnu)
    · exact htop'
  have hlamTop : Work.SurgeryInvariance.WindingSpan P
      (Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam) = ⊤ := by
    by_cases hle : lam ∈ (exc : Set ℝ)
    · -- an exceptional level dominates a non-exceptional level just above it
      obtain ⟨nu, hnuIcc, hnuNot⟩ :
          ∃ nu : ℝ, nu ∈ Set.Icc lam lam1 ∧ nu ∉ (exc : Set ℝ) := by
        obtain ⟨nu, hnu, hnuExc⟩ := (Set.Ico_infinite (hexc lam hle).2).exists_notMem_finite
          exc.finite_toSet
        exact ⟨nu, ⟨hnu.1, le_of_lt hnu.2⟩, hnuExc⟩
      have hmono := Work.SurgeryInvariance.WindingSpan_mono (P := P)
        (X := Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ nu)
        (Y := Work.Drive.EpsFormSphere.openTiltedSweepRegion P s c σ u v h ℓ lam)
        (Work.Drive.Final.sweep_anti hnuIcc.1)
      rw [htop nu ⟨le_trans hlam.1 hnuIcc.1, hnuIcc.2⟩ hnuNot] at hmono
      exact top_le_iff.mp hmono
    · exact htop lam hlam hle
  rw [hlamTop, hstart]

end

end Work.Drive.Mono
