import Submission.Work.BoxShrink.Bubble.Reduce
import Submission.Work.BoxShrink.Bubble.DiscRoute
import Submission.Work.BoxShrink.Bubble.Toolkit.regionEquivalent_of_surgeryStepZero
import Submission.Work.BoxShrink.Core.Bubble.Defs
import Submission.Work.SurgeryInvariance.WindingOf.homotopic_eq

/-!
# The pinch: three equivalent shapes of the push-off, and the surgery bookkeeping

The remaining content of the chapter is the push-off `Work.BoxShrink.Bubble.SlicePushOff`: the
loops of the region inside the box can be transported into the two half-regions
`upperRegion ∪ lowerRegion = boxRegion ∖ sliceRegion`.  This file records the *shapes* in which
that content can be stated and consumed, all fully proved:

* `Work.BoxShrink.Bubble.slicePushOff_iff_homotopic`: **the push-off is a free-homotopy
  statement.**  `SlicePushOff P s c σ u` holds if and only if every closed curve of the surface
  inside the box is *freely homotopic in the surface* to a closed curve lying in the two
  half-regions.  This is the form in which Pardon's pinch is actually performed (a deformation of
  the loops of `F`, not a bookkeeping of winding vectors), and it removes the winding bookkeeping
  from the construction: a solver of the pinch only has to exhibit, for each curve, a homotopy.
  (`Work.BoxShrink.Bubble.homotopic_of_windingOf_eq` is the covering-space half of the
  equivalence: on a torus, two closed curves with the same winding vector are freely homotopic.)

* `Work.BoxShrink.Bubble.pushOffDatum_iff_slicePushOff` (`Reduce.lean`): the push-off is Pardon's
  double-bubble datum for this configuration, `Work.BoxShrink.Core.DoubleBubbleDatum P s c σ u`.

* `Work.BoxShrink.Bubble.bubble_of_physicalBubbleSweep`: **the field from the *spatial* pinch.**
  If every configuration carries a family of regions of the library's
  `Work.SurgeryInvariance.Sweep` (between exceptional parameters the region is moved by an ambient
  isotopy of `ℝ³` preserving `F`; at an exceptional parameter it gains or loses the interior of an
  embedded disc of `F`) with the prescribed endpoints, then the field follows
  (`Work.SurgeryInvariance.Sweep.toLoops`).  This is the form in which Pardon's proof delivers the
  pinch — a one-parameter family of embedded spheres, pinched along the disc `cutDisc s c σ u` —
  and the two local models of `Sweep` are weaker than the two local models of `SweepLoops`, so a
  future construction of the pinching family may be checked in the spatial vocabulary.

* `Work.BoxShrink.Bubble.surgeryStepZero_of_open_sdiff`: **the surgery bookkeeping, spelled out.**
  If `A' ⊆ A` are open in the surface and the changed piece `A \ A'` is *again* open in the surface
  with vanishing winding span, then `A` is obtained from `A'` by that single `2`-surgery.  The
  openness of `A \ A'` is **not** automatic: `A \ A'` is the part of the open set `A` off the open
  set `A'`, and `A'` need not be closed in `A`.  This is exactly the obstruction of
  `Obstruction.surgeryStepZero_eq_self_or_empty` (a `SurgeryStepZero` only removes a piece clopen in
  the region, so no chain of them removes the slice from a connected region), and it is why the
  family must contain a genuine loop transport.

## What is *not* proved here

The push-off itself: it is the pinch, and it needs the one-parameter family of spheres.  See
`PLAN.md`, stretches 11-16: a chain of `2`-surgeries alone can never remove the slice from a
connected region (`Work.BoxShrink.Bubble.Obstruction.surgeryStepZero_eq_self_or_empty` together with
`Work.BoxShrink.Bubble.Sharp.sliceRegion_inter_eq_of_surgeryStepZero`), the deformation supported in
a neighbourhood of the slice is impossible (the boundary of its support would have to lie in
`upperRegion ∪ lowerRegion` while the slice's points are limits of both half-regions), and, most
importantly, **stretch 16 of `PLAN.md` records a counterexample showing that the push-off is FALSE
as stated**: with only `hS` and `hZ` the conclusion fails, so the field
`Work.BoxShrink.Core.BubbleInput.bubble` must be restated (Pardon's own hypotheses give the
inessentiality of `S_t ∩ F` at *every* time, not just at the two endpoints).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Filter
open scoped Topology

namespace Work.BoxShrink.Bubble

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The push-off as a homotopy statement -/

/-- **Two closed curves of the torus with the same winding vector are freely homotopic in the
surface.**  Both curves admit lifts to the parameter plane (`Work.TorusCover.ParamTorus_exists_liftOf`);
if the lifts advance by the same period shift, the straight-line interpolation of the two lifted
parameter curves is still periodic and descends to a homotopy in the surface.  (On the torus, the
free homotopy class of a closed curve is its winding vector.) -/
theorem homotopic_of_windingOf_eq {γ γ' : Work.CoreTopology.ClosedCurve P}
    (h : Work.SurgeryInvariance.windingOf P γ = Work.SurgeryInvariance.windingOf P γ') :
    Work.CoreTopology.Homotopic P γ γ' := by
  classical
  obtain ⟨L⟩ : Nonempty (Work.CoreTopology.LiftOf P γ) :=
    Work.TorusCover.ParamTorus_exists_liftOf P γ
  obtain ⟨L'⟩ : Nonempty (Work.CoreTopology.LiftOf P γ') :=
    Work.TorusCover.ParamTorus_exists_liftOf P γ'
  have hw : L.winding = L'.winding := by
    rw [← Work.SurgeryInvariance.windingOf_eq P γ L, ← Work.SurgeryInvariance.windingOf_eq P γ' L']
    exact h
  refine ⟨fun s t => P.psi ((1 - s) * L.Θ t + s * L'.Θ t)
      ((1 - s) * L.Φ t + s * L'.Φ t), ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity
    exact P.cont.comp
      (((continuous_const.sub continuous_fst).mul
          (L.contΘ.comp continuous_snd)).add
        (continuous_fst.mul (L'.contΘ.comp continuous_snd)) |>.prodMk
        (((continuous_const.sub continuous_fst).mul
            (L.contΦ.comp continuous_snd)).add
          (continuous_fst.mul (L'.contΦ.comp continuous_snd))))
  · -- the homotopy stays on the surface
    intro s t
    exact P.psi_mem_carrier _ _
  · -- it starts at `γ`
    intro t
    simpa only [sub_zero, one_mul, zero_mul, add_zero, Prod.fst, Prod.snd] using L.lifts t
  · -- and ends at `γ'`
    intro t
    simpa only [sub_self, zero_mul, one_mul, zero_add, Prod.fst, Prod.snd] using L'.lifts t
  · -- it is a family of closed curves
    intro s t
    obtain ⟨hp1, hp2⟩ := L.period_shift_winding t
    obtain ⟨hp1', hp2'⟩ := L'.period_shift_winding t
    rw [← hw] at hp1' hp2'
    have hq1 : L.Θ (t + 2 * Real.pi) = L.Θ t + (L.winding.1 : ℝ) * (2 * Real.pi) := hp1
    have hq2 : L.Φ (t + 2 * Real.pi) = L.Φ t + (L.winding.2 : ℝ) * (2 * Real.pi) := hp2
    have hq1' : L'.Θ (t + 2 * Real.pi) = L'.Θ t + (L.winding.1 : ℝ) * (2 * Real.pi) := hp1'
    have hq2' : L'.Φ (t + 2 * Real.pi) = L'.Φ t + (L.winding.2 : ℝ) * (2 * Real.pi) := hp2'
    refine (P.psi_eq_iff _ _ _ _).mpr ⟨?_, ?_⟩
    · -- the first parameter advances by an integer multiple of `2π`
      refine ⟨L.winding.1, ?_⟩
      linear_combination (1 - s) * hq1 + s * hq1'
    · -- the second parameter advances by an integer multiple of `2π`
      refine ⟨L.winding.2, ?_⟩
      linear_combination (1 - s) * hq2 + s * hq2'

/-- **The push-off in homotopy form.**  The loops of the region inside the box can be transported
into the two half-regions if and only if every loop of the region is freely homotopic in the
surface to a loop lying in the two half-regions.  This is the shape of Pardon's pinch which a
construction has to produce, with no winding bookkeeping left. -/
theorem slicePushOff_iff_homotopic {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    SlicePushOff P s c σ u ↔
      ∀ γ : Work.CoreTopology.ClosedCurve P,
        (∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.boxRegion P s c σ) →
        ∃ γ' : Work.CoreTopology.ClosedCurve P,
          (∀ t : ℝ, γ' t ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∪
            Work.BoxShrink.Core.lowerRegion P s c σ u) ∧
          Work.CoreTopology.Homotopic P γ γ' := by
  constructor
  · intro h γ hγ
    obtain ⟨γ', hγ', hwind⟩ := h ⟨γ, hγ, rfl⟩
    exact ⟨γ', hγ', homotopic_of_windingOf_eq (P := P) hwind.symm⟩
  · intro h k hk
    obtain ⟨γ, hγ, rfl⟩ := hk
    obtain ⟨γ', hγ', hhom⟩ := h γ hγ
    exact ⟨γ', hγ', (Work.SurgeryInvariance.WindingOf.homotopic_eq hhom).symm⟩

/-! ## The surgery bookkeeping -/

/-- **A single `2`-surgery, spelled out.**  If `A` and `A'` are open in the surface, `A' ⊆ A`, and
the changed piece `A ∖ A'` is again open in the surface and carries no essential loop, then `A` is
obtained from `A'` by that single surgery.  (The openness of the changed piece is *not* automatic:
`A ∖ A'` is the part of the open set `A` off the open set `A'`, and `A'` need not be closed in `A` —
this is exactly the content of `Work.BoxShrink.Bubble.Obstruction`, and the reason a pinch cannot be
assembled from `2`-surgeries alone.) -/
theorem surgeryStepZero_of_open_sdiff {A A' : Set R3}
    (hA : Work.SurgeryInvariance.IsOpenInCarrier P A)
    (hA' : Work.SurgeryInvariance.IsOpenInCarrier P A')
    (hsub : A' ⊆ A) (hdiff : Work.SurgeryInvariance.IsOpenInCarrier P (A \ A'))
    (hspan : Work.SurgeryInvariance.WindingSpan P (A \ A') = ⊥) :
    Work.SurgeryInvariance.SurgeryStepZero P A A' :=
  ⟨A \ A', hspan, hA, hA', hdiff,
    Or.inl ⟨(by
      ext x
      constructor
      · intro hx
        by_cases h : x ∈ A'
        · exact Or.inl h
        · exact Or.inr ⟨hx, h⟩
      · rintro (h | h)
        · exact hsub h
        · exact h.1), Set.disjoint_sdiff_right⟩⟩

/-! ## The field from the spatial pinch -/

/-- **The field from a family of regions with the local models of `Work.SurgeryInvariance.Sweep`.**
This is the *spatial* form of Pardon's pinch: between exceptional parameters the region is moved by
an ambient isotopy of `ℝ³` preserving `F`, and at an exceptional parameter it gains or loses the
interior of an embedded disc of `F`.  The conversion to the loop-level local models is
`Work.SurgeryInvariance.Sweep.toLoops`. -/
noncomputable def bubble_of_physicalBubbleSweep
    (h : ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
      ∃ sw : Work.SurgeryInvariance.Sweep P,
        sw.region 0 = Work.BoxShrink.Core.boxRegion P s c σ ∧
        sw.region 1 = Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u) :
    ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
      ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
      Work.BoxShrink.Core.BubbleSweep P s c σ u :=
  fun P s c σ u hS hZ =>
    ⟨(h P s c σ u hS hZ).choose.toLoops,
      (h P s c σ u hS hZ).choose_spec.1,
      (h P s c σ u hS hZ).choose_spec.2⟩

/-- **The field from the pinch in homotopy form.**  If every loop of the region inside the box is
freely homotopic in the surface to a loop of the two half-regions, then Pardon's double bubble for
this configuration exists.  This is the shape a construction of the pinch should produce
(`Work.BoxShrink.Bubble.slicePushOff_iff_homotopic` turns it into the geometric input). -/
noncomputable def bubble_of_homotopyPushOff {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : ∀ γ : Work.CoreTopology.ClosedCurve P,
      (∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.boxRegion P s c σ) →
      ∃ γ' : Work.CoreTopology.ClosedCurve P,
        (∀ t : ℝ, γ' t ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u) ∧
        Work.CoreTopology.Homotopic P γ γ') :
    Work.BoxShrink.Core.BubbleSweep P s c σ u :=
  bubble_of_slicePushOff (slicePushOff_iff_homotopic.mpr h)

end

end Work.BoxShrink.Bubble
