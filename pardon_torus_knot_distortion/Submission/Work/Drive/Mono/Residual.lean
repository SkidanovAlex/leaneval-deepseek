import Mathlib
import Submission.Work.Drive.Mono.Split
import Submission.Work.Drive.EpsForm.tiltedSweepGenericity_holds_sized
import Submission.Work.Drive.EpsForm.distortionBound_one_le

/-!
# The residual of the tilted sweep, cut into four independently attackable clauses

`Work.Drive.Mono.Split` (`Submission/Work/Drive/Mono/Split.lean`) proves that the residual of the
tilted sweep — `Work.Drive.Final.TiltedSweepMono` — follows from the existence, at every crux
configuration, of the data of the sweep together with the three geometric clauses
`TraceCurvesAt` / `AboveGenericAt` / `NoJumpBelowAt` (`TiltedTraceDataW`).

This module packages that into four named statements, so that each can be attacked separately:

* `TiltData ψ s c σ u v h R ℓ exc lam0 lam1` — the conditions on the *tilt data*: the genericity of
  the sweep height (`Work.Drive.Final.TiltedGenericity`, proved upstream by
  `Work.Drive.EpsForm.tiltedSweepGenericity_holds_sized`), the size conditions of the sweep, and the
  window conditions (the range of `ℓ` on the box is contained in `(lam0, lam1)` and `exc` too).
* `DataExists` — **clause 0**: at every crux configuration there *is* tilt data satisfying
  `TiltData`.  (Only the genericity input is non-elementary; the size and window conditions are
  already produced by the upstream genericity theorem.)
* `TraceCurvesGeneric` — **clause 1**: at every non-exceptional level of the window the trace of the
  level is a finite family of pairwise disjoint simple *inessential* closed curves equal to the
  frontier of the level's removed set (Pardon's Lemma 2 at the level, from the level count
  `Work.Drive.EpsFormSphere.encard_frontier_tiltedSweptBall_lt_min`).
* `AboveGeneric` — **clause 2**: every point of the surface in the closed box and the closed slab at
  a non-exceptional level of the window is in the closure of the level's region or on the level's
  trace.
* `NoJumpExceptional` — **clause 4**: at every *exceptional* level of the window, no level just
  below a level of vanishing span carries the full span (Pardon's `2`-surgery count at the
  intermediate members of his family — the pinch).

The assembly `tiltedSweepMono_of_split` proves
`TraceCurvesGeneric → AboveGeneric → NoJumpExceptional → DataExists → TiltedSweepMono`.

The clause statements deliberately **drop** the hypothesis `Work.Sweep.IsDistortionBound K d`
(which is what makes the crux configuration vacuous once the theorem is known) and keep only
`1 ≤ d` — the single consequence of it which the level count uses.  They also do *not* assume the
counts as ENNReal estimates *of the theorem's own conclusion*, and every geometric hypothesis is
retained, so that each clause is testable.
-/

open LeanEval.KnotTheory.PardonDistortion
open scoped ENNReal

namespace Work.Drive.Mono

noncomputable section

/-- **The conditions on the tilt data of the sweep**: the genericity of the sweep height on the
surface, the size conditions of the sweep, and the window conditions. -/
def TiltData (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ) : Prop :=
  Work.Drive.Final.TiltedGenericity ψ s c σ u v h ℓ exc ∧
  ‖v‖ = 1 ∧ ℓ ≠ 0 ∧ ℓ v = 0 ∧
  ‖v - Work.BoxShrink.shiftVσ σ 1‖ * R < h ∧ 0 < h ∧
  (∀ y ∈ Submission.PBox s c σ, ‖y - c‖ ≤ R) ∧
  (∀ y ∈ Submission.PBox s c σ, lam0 < ℓ y) ∧
  (∀ y ∈ Submission.PBox s c σ, ℓ y < lam1) ∧ lam0 < lam1 ∧
  (∀ t ∈ exc, lam0 < t ∧ t < lam1)


end

noncomputable section

/-- **Clause 1**: at every non-exceptional level of the window the trace of the level is the union
of the ranges of finitely many pairwise disjoint simple closed curves of the surface, each
inessential in it (Pardon's Lemma 2 at the level, with the level count). -/
def TraceCurvesGeneric : Prop :=
  ∀ 
    (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d) (_hd1 : 1 ≤ d)
    (_himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (_hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (_hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3))
    (_hbox : Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ)
    (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r)
    (_hslice : Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
        {y : R3 | Submission.boxNorm c σ y = s})
    (u : ℝ) (_hu : |u| < Submission.eps * r)
    (_hS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)))
    (_hU : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)))
    (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ)
    (_hT : TiltData ψ s c σ u v h R ℓ exc lam0 lam1)
    (lam : ℝ) (_hlam : lam ∈ Set.Icc lam0 lam1) (_hne : lam ∉ (exc : Set ℝ)),
    TraceCurvesAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam

/-- **Clause 2**: at every non-exceptional level of the window, every point of the surface in the
closed box and the closed tilted slab at the level is in the closure of the level's region or on
the level's trace. -/
def AboveGeneric : Prop :=
  ∀ 
    (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d) (_hd1 : 1 ≤ d)
    (_himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (_hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (_hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3))
    (_hbox : Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ)
    (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r)
    (_hslice : Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
        {y : R3 | Submission.boxNorm c σ y = s})
    (u : ℝ) (_hu : |u| < Submission.eps * r)
    (_hS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)))
    (_hU : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)))
    (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ)
    (_hT : TiltData ψ s c σ u v h R ℓ exc lam0 lam1)
    (lam : ℝ) (_hlam : lam ∈ Set.Icc lam0 lam1) (_hne : lam ∉ (exc : Set ℝ)),
    AboveGenericAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam

/-- **Clause 4**: at every exceptional level of the window, no level just below a level of vanishing
span carries the full span. -/
def NoJumpExceptional : Prop :=
  ∀ 
    (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d) (_hd1 : 1 ≤ d)
    (_himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (_hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (_hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3))
    (_hbox : Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ)
    (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r)
    (_hslice : Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
        {y : R3 | Submission.boxNorm c σ y = s})
    (u : ℝ) (_hu : |u| < Submission.eps * r)
    (_hS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)))
    (_hU : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)))
    (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ)
    (_hT : TiltData ψ s c σ u v h R ℓ exc lam0 lam1)
    (lam : ℝ) (_hlam : lam ∈ Set.Icc lam0 lam1) (_he : lam ∈ (exc : Set ℝ)),
    NoJumpBelowAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam

/-- **Clause 0**: at every crux configuration there exist tilt data satisfying `TiltData`. -/
def DataExists : Prop :=
  ∀ 
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (hd : 0 ≤ d) (hd1 : 1 ≤ d)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    (r : ℝ) (hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hbox : Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ)
    (s : ℝ) (hrs : r < s) (hs : s < (1 + Submission.eps) * r)
    (hslice : Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
        {y : R3 | Submission.boxNorm c σ y = s})
    (u : ℝ) (hu : |u| < Submission.eps * r)
    (hS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)))
    (hU : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        K.curve t ∈ Submission.PBox s c σ ∧ (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
      ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)))
    (hbound : Work.Sweep.IsDistortionBound K d),
    ∃ (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
      TiltData ψ s c σ u v h R ℓ exc lam0 lam1

/-- **The assembly**: the four clauses prove `Work.Drive.Final.TiltedSweepMono` — hence, through
the proved chain of `Drive/Final`, Pardon's distortion bound. -/
theorem tiltedSweepMono_of_split (h1 : TraceCurvesGeneric) (h2 : AboveGeneric)
    (h3 : NoJumpExceptional) (h4 : DataExists) : Work.Drive.Final.TiltedSweepMono :=
  Work.Drive.Mono.tiltedSweepMono_of_traceDataW
    (fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
      by
        have hd1 : 1 ≤ d := Work.Drive.EpsForm.distortionBound_one_le K d hbound
        obtain ⟨v, h, R, ℓ, lam0, lam1, exc, hdata⟩ :=
          h4 p q hp hq hc ψ K d hd hd1 himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
              hbound
        obtain ⟨hgen, hv1, hℓne, hℓv, hsize, hh, hRbox, hlow, hhigh, hl, hexc⟩ := hdata
        refine ⟨v, h, R, ℓ, lam0, lam1, exc, hv1, hℓne, hℓv, hsize, hh, hRbox, hlow, hhigh, hl,
          hexc, ?_⟩
        have hT : TiltData ψ s c σ u v h R ℓ exc lam0 lam1 :=
          ⟨hgen, hv1, hℓne, hℓv, hsize, hh, hRbox, hlow, hhigh, hl, hexc⟩
        exact ⟨fun lam hlam hne => h1 p q hp hq hc ψ K d hd hd1 himg hsmall hcl r hr c σ hbox s
                hrs hs hslice u hu hS hU v h R ℓ exc lam0 lam1 hT lam hlam hne,
          fun lam hlam hne => h2 p q hp hq hc ψ K d hd hd1 himg hsmall hcl r hr c σ hbox s
                hrs hs hslice u hu hS hU v h R ℓ exc lam0 lam1 hT lam hlam hne,
          fun lam hlam he => h3 p q hp hq hc ψ K d hd hd1 himg hsmall hcl r hr c σ hbox s
                hrs hs hslice u hu hS hU v h R ℓ exc lam0 lam1 hT lam hlam he⟩)

/-- **The residual in the form in which it must be attacked: an existential over the data.**

Note (an important caveat, discovered after the clauses above were stated): the four clauses above
are *universally quantified over the data* satisfying `TiltData`.  That makes them stronger than the
existential form below, and *strictly* so: the upstream genericity statement
`Work.Drive.EpsForm.tiltedSweepGenericity_holds_sized` produces a slab half-width
`h = ε*R + R + |u| + 1`, which is larger than the radius of the box — so the box is *strictly inside*
the slab, the removed chunk inside the box is `{ℓ < lam}` and the level region is
`carrier ∩ PBox ∩ {ℓ > lam}`.  For such data the family of level surfaces is degenerate (the trench
never spans the box), clause 1 fails at the level at which the span of the region drops (the level
wall trace of the tilted plane is then *essential*), and clause 4 fails as well.  Hence the four
clauses are *false* as universally quantified statements over `TiltData`, while the existential form
below is the honest residual (the prover chooses the data, and the interesting data are those with a
genuinely thin slab cutting the box).

The existential form carries exactly what `tiltedSweepMono_of_traceDataW` consumes (`TiltData` plus
`TiltedTraceDataW`), and the three clauses of the four-clause spelling are the three conjuncts of
`TiltedTraceDataW`. -/
def TiltedTraceDataWExists : Prop :=
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
            TiltedTraceDataW (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ exc lam0 lam1

/-- **The existential residual implies the four-clause assembly's hypothesis**: the tuple of
`Work.Drive.Mono.tiltedSweepMono_of_traceDataW` is the `TiltData` conjunction followed by
`TiltedTraceDataW`. -/
theorem tiltedSweepMono_of_traceDataWExists (h : TiltedTraceDataWExists) :
    Work.Drive.Final.TiltedSweepMono :=
  Work.Drive.Mono.tiltedSweepMono_of_traceDataW
    (fun p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU =>
      by
        obtain ⟨v, h, R, ℓ, lam0, lam1, exc, hdata, hW⟩ :=
          h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
        obtain ⟨hgen, hv1, hℓne, hℓv, hsize, hh, hRbox, hlow, hhigh, hl, hexc⟩ := hdata
        exact ⟨v, h, R, ℓ, lam0, lam1, exc, hv1, hℓne, hℓv, hsize, hh, hRbox, hlow, hhigh, hl,
          hexc, hW⟩)

end

end Work.Drive.Mono
