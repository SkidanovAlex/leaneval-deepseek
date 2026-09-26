import Submission.Work.Drive.EpsFormSphere.Defs
import Submission.Work.Drive.EpsFormSphere.Convert
import Submission.Work.Drive.EpsFormSphere.countingHalfEpsSphere
import Submission.Work.BoxShrink.PinchOff.CirclesCase
import Submission.Work.CountedPinch.Defs
import Submission.Work.Smooth.Plane.Slicing

namespace Work.Drive.EpsFormSphere

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

noncomputable section

/-- The "closed half" spelling of the crux's conclusion: an essential loop of the surface lying in
the closure of the upper half-region, or in the closure of the lower one. -/
def ClosedHalfCrux : Prop :=
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
          (∃ γ : Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ),
              Work.CoreTopology.IsEssential _ γ ∧
                ∀ t : ℝ, γ t ∈ closure
                  (Work.BoxShrink.Core.upperRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ u)) ∨
          (∃ γ : Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ),
              Work.CoreTopology.IsEssential _ γ ∧
                ∀ t : ℝ, γ t ∈ closure
                  (Work.BoxShrink.Core.lowerRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ u))

/-- **The crux follows from its "closed half" form.** -/
-- (the reduction `ClosedHalfCrux ⟹ CountingHalfEpsSphere`)
theorem cruxEpsFormW_of_closedHalf (h : ClosedHalfCrux) :
    Work.Drive.EpsSphere.CountingHalfEpsSphere := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    ε hε
  exact Work.Drive.EpsFormSphere.thickHalf_of_closedHalf
    (h p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU)
    ε hε


/-! ## The two cases of the conclusion-side analysis

The trace of the cutting plane in the box is (generically) a finite disjoint union of *circles* and
of *arcs closed at the ends* whose endpoints lie on the box sphere.  The circle case is settled by
the proved machinery of `Work.BoxShrink.PinchOff.CirclesCase` (`bubbleHalf_of_trace_circles_holds`
from the slice's inessentiality); the arcs case is the honest gap (see
`Submission/Work/EpsW/NOTES_cruxEpsFormW.md`).  Both statements below are *instances* of the crux
(their conclusion is the crux's conclusion and their hypotheses are the crux's plus one extra
hypothesis), hence weaker than the deliverable. -/

/-- The *circles* case: at a configuration whose slice is covered by finitely many pairwise disjoint
simple closed curves of the surface, the crux's conclusion holds. -/
def CirclesCaseEps : Prop :=
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
          ¬ (Work.Drive.EpsSphere.torusOf ψ).ContainsEssentialLoop
              (Work.BoxShrink.Core.sliceRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ u) →
          Work.BoxShrink.PinchOff.SliceCirclesOnly ψ s c σ u →
          ∀ ε : ℝ, 0 < ε → Work.Drive.EpsSphere.ThickHalf (Work.Drive.EpsSphere.torusOf ψ) s c σ u ε

/-- The *arcs* case: at a configuration whose slice's closure is a finite disjoint union of
embedded arcs closed at the ends (`Work.CountedPinch.SliceArcsBody`), the crux's conclusion holds. -/
def ArcsCaseEps : Prop :=
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
          Work.CountedPinch.SliceArcsBody (Work.Drive.EpsSphere.torusOf ψ)
            (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
              (Work.CoreTopology.standardCurve p q)) s c σ u →
          ∀ ε : ℝ, 0 < ε → Work.Drive.EpsSphere.ThickHalf (Work.Drive.EpsSphere.torusOf ψ) s c σ u ε

/-- **The slice carries no essential loop**, at the configurations of the crux: Pardon's Lemma 2 at
the flat disc, from the plane count.  (The workspace's `Work.Drive.sliceTrace_inessential_of_countsW`
needs a planar innermost/cleaning datum for the flat disc; supplying it from the convexity of the
disc and the weak cut-and-paste `CleansDiscsW` is the content of this residual.) -/
def SliceInessential : Prop :=
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
          Work.Smooth.Plane.SlicedPlane (Work.Drive.EpsSphere.torusOf ψ)
            (Work.BoxShrink.Core.cutDisc s c σ u) →
          ¬ (Work.Drive.EpsSphere.torusOf ψ).ContainsEssentialLoop
              (Work.BoxShrink.Core.sliceRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ u)

/-- **The case in which the cutting plane is in general position** (transverse along the slice, and
the flat disc sliced by the surface): the crux's conclusion holds.  This case is discharged by the
proved capstone `Work.BoxShrink.PinchOff.regionEquivalent_halves_of_tameSlice`: the slice's
inessentiality (`SliceInessential`) gives the push-off, hence the exact form, hence the ε-form. -/
def PlanePosCaseEps : Prop :=
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
          Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
          Work.Smooth.Plane.SlicedPlane (Work.Drive.EpsSphere.torusOf ψ)
            (Work.BoxShrink.Core.cutDisc s c σ u) →
          ∀ ε : ℝ, 0 < ε → Work.Drive.EpsSphere.ThickHalf (Work.Drive.EpsSphere.torusOf ψ) s c σ u ε

/-- **The complementary case** (the cutting plane not in general position): the crux's conclusion.
This is the degenerate half of the case analysis; nothing in the crux's hypotheses supplies the
plane's general position, so this case must be handled by an argument of its own. -/
def DegeneratePlaneCaseEps : Prop :=
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
          ¬ (Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u ∧
              Nonempty (Work.Smooth.Plane.PlaneSlicing (Work.Drive.EpsSphere.torusOf ψ)
                (Work.BoxShrink.Core.cutDisc s c σ u))) →
          ∀ ε : ℝ, 0 < ε → Work.Drive.EpsSphere.ThickHalf (Work.Drive.EpsSphere.torusOf ψ) s c σ u ε

/-- **The crux from its two cases.**  The case split is on whether the cutting plane is in general
position (transverse along the slice *and* the flat disc sliced by the surface). -/
theorem cruxEpsFormW_of_cases (h1 : PlanePosCaseEps) (h2 : DegeneratePlaneCaseEps) :
    Work.Drive.EpsSphere.CountingHalfEpsSphere := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
    ε hε
  by_cases hpos : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u ∧
      Nonempty (Work.Smooth.Plane.PlaneSlicing (Work.Drive.EpsSphere.torusOf ψ)
        (Work.BoxShrink.Core.cutDisc s c σ u))
  · obtain ⟨hT, hPl⟩ := hpos
    exact h1 p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
      hT hPl ε hε
  · exact h2 p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice u hu hS hU
      (fun h => hpos h) ε hε

end

end Work.Drive.EpsFormSphere
