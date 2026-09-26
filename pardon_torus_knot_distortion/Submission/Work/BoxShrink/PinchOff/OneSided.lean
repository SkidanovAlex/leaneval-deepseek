import Submission.Work.BoxShrink.PinchOff.Perp
import Submission.Work.BoxShrink.PinchOff.CirclesCase
import Submission.Work.BoxShrink.PinchOff.Thickened
import Submission.Work.BoxShrink.Pinch.Trace
import Submission.Work.BoxShrink.PinchOff.exists_halfDown_loop_of_nonpos_loop_in_box
import Submission.Work.BoxShrink.PinchOff.exists_halfUp_loop_of_nonneg_loop_in_box

/-!
# The one-sided push-off, and what it discharges

The local move of Pardon's pinch which the workspace *does* have in full is the push-off of a loop
lying on one side of the cutting plane: the descent (or ascent) field of the plane coordinate pushes
any loop of the box region with `G ≤ 0` (resp. `G ≥ 0`) into the lower (resp. upper) half-region,
with the same winding vector, staying inside the box.  This is
`Work.BoxShrink.PinchOff.exists_halfDown_loop_of_nonpos_loop_in_box` and its mirror
`exists_halfUp_loop_of_nonneg_loop_in_box`, both with the *box-local* transversality hypothesis
`TransverseSlice` (the global `TransverseTrace` they generalize is refuted for all configurations).

This module records the form in which the rest of the chapter consumes them (`HalfPush`), and
derives:

* `windingSpan_lowerSide_le_halfDown`, `windingSpan_upperSide_le_halfUp` — the winding span of the
  one-sided parts of the box region is contained in that of the corresponding half-region;
* `windingSpan_slice_le_halfDown`, `windingSpan_slice_le_halfUp` — the slice of the cutting plane
  (which lies on *both* sides) has its span in *each* half-region: this is the box-local form of
  `Work.BoxShrink.PinchOff.traceMultipleRealisable_of_trace_loop_in_box`, whose hypothesis
  `TransverseTrace` is refuted for all configurations;
* `tracePerpRealisable_of_mem_halves` and `tracePerpRealisable_of_slice_loop_in_box` — the two
  configurations of the parent's factored residual which are discharged by a class realised in the
  halves, in the vocabulary of `Perp.lean` (so that the whole chain of that module applies).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-- **The one-sided push-off at a configuration**, in the form the chapter consumes: every loop of
the box region lying on or below the cutting plane is carried to a loop of the lower half-region
with the same winding vector, and dually on or above it to the upper half-region. -/
def HalfPush (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  (∀ γ : Work.CoreTopology.ClosedCurve (surface ψ),
      (∀ t : ℝ, γ t ∈ Omega ψ s c σ) →
      (∀ t : ℝ, (γ t) (σ 2) ≤ c (σ 2) + u) →
      ∃ γ' : Work.CoreTopology.ClosedCurve (surface ψ),
        (∀ t : ℝ, γ' t ∈ HalfDown ψ s c σ u) ∧
          Work.SurgeryInvariance.windingOf (surface ψ) γ' =
            Work.SurgeryInvariance.windingOf (surface ψ) γ) ∧
  (∀ γ : Work.CoreTopology.ClosedCurve (surface ψ),
      (∀ t : ℝ, γ t ∈ Omega ψ s c σ) →
      (∀ t : ℝ, c (σ 2) + u ≤ (γ t) (σ 2)) →
      ∃ γ' : Work.CoreTopology.ClosedCurve (surface ψ),
        (∀ t : ℝ, γ' t ∈ HalfUp ψ s c σ u) ∧
          Work.SurgeryInvariance.windingOf (surface ψ) γ' =
            Work.SurgeryInvariance.windingOf (surface ψ) γ)

/-- The lower side of the box region: the points of `Ω` on or below the cutting plane. -/
def LowerSide (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Set R3 :=
  Omega ψ s c σ ∩ {x : R3 | x (σ 2) ≤ c (σ 2) + u}

/-- The upper side of the box region: the points of `Ω` on or above the cutting plane. -/
def UpperSide (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Set R3 :=
  Omega ψ s c σ ∩ {x : R3 | c (σ 2) + u ≤ x (σ 2)}

/-! ## The winding span of the one-sided parts -/

/-- **The lower side of the box region has its winding span in the lower half-region.** -/
theorem windingSpan_lowerSide_le_halfDown (h : HalfPush ψ s c σ u) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (LowerSide ψ s c σ u) ≤
      Work.SurgeryInvariance.WindingSpan (surface ψ) (HalfDown ψ s c σ u) := by
  rw [Work.SurgeryInvariance.WindingSpan, Submodule.span_le]
  rintro v ⟨γ, hγ, rfl⟩
  have h1 : ∀ t : ℝ, γ t ∈ Omega ψ s c σ ∧ (γ t) (σ 2) ≤ c (σ 2) + u := fun t => by
    simpa [LowerSide, Set.mem_ofPred_eq] using hγ t
  obtain ⟨γ', hγ', hw⟩ := h.1 γ (fun t => (h1 t).1) (fun t => (h1 t).2)
  refine Submodule.subset_span ⟨γ', hγ', ?_⟩
  simpa using congrArg (fun w : ℤ × ℤ => ((((w.1 : ℤ) : ℚ), (((w.2 : ℤ) : ℚ))))) hw

/-- **The upper side of the box region has its winding span in the upper half-region.** -/
theorem windingSpan_upperSide_le_halfUp (h : HalfPush ψ s c σ u) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (UpperSide ψ s c σ u) ≤
      Work.SurgeryInvariance.WindingSpan (surface ψ) (HalfUp ψ s c σ u) := by
  rw [Work.SurgeryInvariance.WindingSpan, Submodule.span_le]
  rintro v ⟨γ, hγ, rfl⟩
  have h1 : ∀ t : ℝ, γ t ∈ Omega ψ s c σ ∧ c (σ 2) + u ≤ (γ t) (σ 2) := fun t => by
    simpa [UpperSide, Set.mem_ofPred_eq] using hγ t
  obtain ⟨γ', hγ', hw⟩ := h.2 γ (fun t => (h1 t).1) (fun t => (h1 t).2)
  refine Submodule.subset_span ⟨γ', hγ', ?_⟩
  simpa using congrArg (fun w : ℤ × ℤ => ((((w.1 : ℤ) : ℚ), (((w.2 : ℤ) : ℚ))))) hw

/-! ## The slice lies in both one-sided parts -/

/-- The slice is contained in the lower side of the box region. -/
theorem sigma_subset_lowerSide : Sigma ψ s c σ u ⊆ LowerSide ψ s c σ u := by
  intro x hx
  obtain ⟨hc, hb, hG⟩ := Work.BoxShrink.Core.mem_sliceRegion.mp hx
  exact ⟨Work.BoxShrink.Core.mem_boxRegion.mpr ⟨hc, hb⟩, le_of_eq hG⟩

/-- The slice is contained in the upper side of the box region. -/
theorem sigma_subset_upperSide : Sigma ψ s c σ u ⊆ UpperSide ψ s c σ u := by
  intro x hx
  obtain ⟨hc, hb, hG⟩ := Work.BoxShrink.Core.mem_sliceRegion.mp hx
  exact ⟨Work.BoxShrink.Core.mem_boxRegion.mpr ⟨hc, hb⟩, le_of_eq hG.symm⟩

/-- **The slice has its winding span in the lower half-region** (box-local form of the discharge in
`TraceInBox.lean`). -/
theorem windingSpan_slice_le_halfDown (h : HalfPush ψ s c σ u) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Sigma ψ s c σ u) ≤
      Work.SurgeryInvariance.WindingSpan (surface ψ) (HalfDown ψ s c σ u) :=
  le_trans (Work.SurgeryInvariance.WindingSpan_mono (surface ψ) sigma_subset_lowerSide)
    (windingSpan_lowerSide_le_halfDown h)

/-- **The slice has its winding span in the upper half-region.** -/
theorem windingSpan_slice_le_halfUp (h : HalfPush ψ s c σ u) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Sigma ψ s c σ u) ≤
      Work.SurgeryInvariance.WindingSpan (surface ψ) (HalfUp ψ s c σ u) :=
  le_trans (Work.SurgeryInvariance.WindingSpan_mono (surface ψ) sigma_subset_upperSide)
    (windingSpan_upperSide_le_halfUp h)

/-! ## The discharged configurations of the factored residual -/

/-- **A nonzero trace-line class already realised in the halves discharges the residual.** -/
theorem tracePerpRealisable_of_mem_halves (v : ℚ × ℚ) (hv : v ≠ 0)
    (hvL : ∃ L : Submodule ℚ (ℚ × ℚ),
      Work.BoxShrink.Pinch.TraceLine (surface ψ) c σ u L ∧ v ∈ L)
    (hvmem : v ∈ Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)) :
    Work.BoxShrink.Pinch.TracePerpRealisable (surface ψ) s c σ u := by
  refine Or.inr ⟨v, hv, hvL, le_trans inf_le_right ?_⟩
  refine le_trans (ker_crossLin_le_span hv) ?_
  rw [Submodule.span_le]
  simpa using hvmem

/-- **A trace-line class realised by a loop of the slice inside the box discharges the residual**,
with the box-local transversality `TransverseSlice` (through `HalfPush`) in place of the refuted
global `TransverseTrace`. -/
theorem tracePerpRealisable_of_slice_loop_in_box (h : HalfPush ψ s c σ u) (v : ℚ × ℚ)
    (hv : v ≠ 0)
    (hvL : ∃ L : Submodule ℚ (ℚ × ℚ),
      Work.BoxShrink.Pinch.TraceLine (surface ψ) c σ u L ∧ v ∈ L)
    (hreal : ∃ γ : Work.CoreTopology.ClosedCurve (surface ψ),
      (∀ t : ℝ, γ t ∈ Sigma ψ s c σ u) ∧
      ((((Work.SurgeryInvariance.windingOf (surface ψ) γ).1 : ℤ) : ℚ),
        (((Work.SurgeryInvariance.windingOf (surface ψ) γ).2 : ℤ) : ℚ)) = v) :
    Work.BoxShrink.Pinch.TracePerpRealisable (surface ψ) s c σ u := by
  obtain ⟨γ, hγ, hγv⟩ := hreal
  refine tracePerpRealisable_of_mem_halves v hv hvL ?_
  have hvSig : v ∈ Work.SurgeryInvariance.WindingSpan (surface ψ) (Sigma ψ s c σ u) := by
    rw [← hγv]
    exact Submodule.subset_span ⟨γ, hγ, rfl⟩
  exact (Work.SurgeryInvariance.WindingSpan_mono (surface ψ) Set.subset_union_right)
    ((windingSpan_slice_le_halfDown h) hvSig)

/-! ## The one-sided push-off holds under box-local transversality -/

/-- **The one-sided push-off at a configuration holds under `TransverseSlice` alone** (the global
`TransverseTrace` of the older statements is refuted for all configurations), by the two delegated
and proved push-offs of this directory. -/
theorem halfPush_holds (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u) :
    HalfPush ψ s c σ u :=
  ⟨fun γ hbox hle => exists_halfDown_loop_of_nonpos_loop_in_box hT γ hbox hle,
    fun γ hbox hge => exists_halfUp_loop_of_nonneg_loop_in_box hT γ hbox hge⟩

/-- **A loop of the slice, pushed off the plane inside the box**, with the box-local
`TransverseSlice`: this is `Work.BoxShrink.PinchOff.exists_halves_loop_of_slice_loop_in_box` of
`TraceInBox.lean` with the refuted global `TransverseTrace` replaced by the box-local hypothesis, so
that it applies at the configurations of the challenge. -/
theorem exists_halves_loop_of_slice_loop_in_box_holds
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (γ : Work.CoreTopology.ClosedCurve (surface ψ))
    (hγ : ∀ t : ℝ, γ t ∈ Sigma ψ s c σ u) :
    ∃ γ' : Work.CoreTopology.ClosedCurve (surface ψ),
      (∀ t : ℝ, γ' t ∈ Halves ψ s c σ u) ∧
        Work.SurgeryInvariance.windingOf (surface ψ) γ' =
          Work.SurgeryInvariance.windingOf (surface ψ) γ := by
  obtain ⟨γ', hγ', hw⟩ := exists_halfDown_loop_of_nonpos_loop_in_box hT γ
    (fun t => Sigma_subset_Omega (hγ t))
    (fun t => le_of_eq (Work.BoxShrink.Core.mem_sliceRegion.mp (hγ t)).2.2)
  exact ⟨γ', fun t => Or.inr (hγ' t), hw⟩

/-- **The lower side of the box region has its winding span in the lower half-region**,
unconditionally under `TransverseSlice`. -/
theorem windingSpan_lowerSide_le_halfDown_holds
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (LowerSide ψ s c σ u) ≤
      Work.SurgeryInvariance.WindingSpan (surface ψ) (HalfDown ψ s c σ u) :=
  windingSpan_lowerSide_le_halfDown (halfPush_holds hT)

/-- **The upper side of the box region has its winding span in the upper half-region**,
unconditionally under `TransverseSlice`. -/
theorem windingSpan_upperSide_le_halfUp_holds
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (UpperSide ψ s c σ u) ≤
      Work.SurgeryInvariance.WindingSpan (surface ψ) (HalfUp ψ s c σ u) :=
  windingSpan_upperSide_le_halfUp (halfPush_holds hT)

/-- **The slice of the cutting plane has its winding span in each of the two half-regions**,
unconditionally under `TransverseSlice`.  This is the box-local form of the discharged case of the
pinch residual of `TraceInBox.lean`. -/
theorem windingSpan_slice_le_halfDown_holds
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Sigma ψ s c σ u) ≤
      Work.SurgeryInvariance.WindingSpan (surface ψ) (HalfDown ψ s c σ u) :=
  windingSpan_slice_le_halfDown (halfPush_holds hT)

/-- **The slice of the cutting plane has its winding span in the upper half-region**,
unconditionally under `TransverseSlice`. -/
theorem windingSpan_slice_le_halfUp_holds
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Sigma ψ s c σ u) ≤
      Work.SurgeryInvariance.WindingSpan (surface ψ) (HalfUp ψ s c σ u) :=
  windingSpan_slice_le_halfUp (halfPush_holds hT)

/-- **The discharged configuration of the residual: a nonzero trace-line class realised by a loop of
the slice discharges it**, under the box-local `TransverseSlice` (in place of the refuted global
`TransverseTrace`). -/
theorem tracePerpRealisable_of_slice_loop_in_box_holds
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u) (v : ℚ × ℚ) (hv : v ≠ 0)
    (hvL : ∃ L : Submodule ℚ (ℚ × ℚ),
      Work.BoxShrink.Pinch.TraceLine (surface ψ) c σ u L ∧ v ∈ L)
    (hreal : ∃ γ : Work.CoreTopology.ClosedCurve (surface ψ),
      (∀ t : ℝ, γ t ∈ Sigma ψ s c σ u) ∧
      ((((Work.SurgeryInvariance.windingOf (surface ψ) γ).1 : ℤ) : ℚ),
        (((Work.SurgeryInvariance.windingOf (surface ψ) γ).2 : ℤ) : ℚ)) = v) :
    Work.BoxShrink.Pinch.TracePerpRealisable (surface ψ) s c σ u :=
  tracePerpRealisable_of_slice_loop_in_box (halfPush_holds hT) v hv hvL hreal

/-! ## The closed halves and the open halves have the same winding span

Under `TransverseSlice` the one-sided push-off identifies the span of a *closed* half-region — the form
in which Pardon's Lemma `doublebubble2` states its conclusion, `Thickened.lean` — with that of the
corresponding *open* half-region.  (Without transversality the two differ: at the tangent witness the
meridian lies in the closed upper half but no loop of the open upper half has its class.) -/

/-- The upper side of the box region is the closed upper half-region of `Thickened.lean`. -/
theorem upperSide_eq_closedHalfUp :
    UpperSide ψ s c σ u = closedHalfUp ψ s c σ u := by
  ext x
  simp only [UpperSide, closedHalfUp, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Work.BoxShrink.Bubble.planeCoord_apply]
  constructor
  · rintro ⟨hx, hle⟩
    exact ⟨hx, by linarith⟩
  · rintro ⟨hx, hle⟩
    exact ⟨hx, by linarith⟩

/-- The lower side of the box region is the closed lower half-region of `Thickened.lean`. -/
theorem lowerSide_eq_closedHalfDown :
    LowerSide ψ s c σ u = closedHalfDown ψ s c σ u := by
  ext x
  simp only [LowerSide, closedHalfDown, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Work.BoxShrink.Bubble.planeCoord_apply]
  constructor
  · rintro ⟨hx, hle⟩
    exact ⟨hx, by linarith⟩
  · rintro ⟨hx, hle⟩
    exact ⟨hx, by linarith⟩

/-- **The closed upper half and the open upper half realise the same winding vectors**, under
`TransverseSlice` (via the one-sided push-off and monotonicity). -/
theorem windingSpan_closedHalfUp_eq_halfUp_holds
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (closedHalfUp ψ s c σ u) =
      Work.SurgeryInvariance.WindingSpan (surface ψ) (HalfUp ψ s c σ u) := by
  rw [← upperSide_eq_closedHalfUp]
  refine le_antisymm (windingSpan_upperSide_le_halfUp_holds hT) ?_
  refine Work.SurgeryInvariance.WindingSpan_mono (surface ψ) fun x hx => ?_
  obtain ⟨hc, hb, hlt⟩ := Work.BoxShrink.Core.mem_upperRegion.mp hx
  exact ⟨Work.BoxShrink.Core.mem_boxRegion.mpr ⟨hc, hb⟩, le_of_lt hlt⟩

/-- **The closed lower half and the open lower half realise the same winding vectors**, under
`TransverseSlice`. -/
theorem windingSpan_closedHalfDown_eq_halfDown_holds
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (closedHalfDown ψ s c σ u) =
      Work.SurgeryInvariance.WindingSpan (surface ψ) (HalfDown ψ s c σ u) := by
  rw [← lowerSide_eq_closedHalfDown]
  refine le_antisymm (windingSpan_lowerSide_le_halfDown_holds hT) ?_
  refine Work.SurgeryInvariance.WindingSpan_mono (surface ψ) fun x hx => ?_
  obtain ⟨hc, hb, hlt⟩ := Work.BoxShrink.Core.mem_lowerRegion.mp hx
  exact ⟨Work.BoxShrink.Core.mem_boxRegion.mpr ⟨hc, hb⟩, le_of_lt hlt⟩

/-- **The thickened (paper-faithful) residual under `TransverseSlice` is the open one.**  Under
`TransverseSlice` the closed halves of `Thickened.lean` carry an essential loop exactly when the open
halves do, so `ClosedHalfS` and `BubbleHalf` agree wherever the cutting plane is transverse; the two
differ exactly at the non-transverse configurations (where a loop of a closed half may run along the
trace, as the meridian does at the tangent witness). -/
theorem closedHalfS_iff_bubbleHalf_of_transverseSlice
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u) :
    ((surface ψ).ContainsEssentialLoop (closedHalfUp ψ s c σ u) ∨
        (surface ψ).ContainsEssentialLoop (closedHalfDown ψ s c σ u)) ↔
      ((surface ψ).ContainsEssentialLoop (HalfUp ψ s c σ u) ∨
        (surface ψ).ContainsEssentialLoop (HalfDown ψ s c σ u)) := by
  have hup := windingSpan_closedHalfUp_eq_halfUp_holds hT
  have hdn := windingSpan_closedHalfDown_eq_halfDown_holds hT
  constructor
  · rintro (h | h)
    · exact Or.inl ((Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mp
        (by rw [← hup]; exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mpr h))
    · exact Or.inr ((Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mp
        (by rw [← hdn]; exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mpr h))
  · rintro (h | h)
    · exact Or.inl ((Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mp
        (by rw [hup]; exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mpr h))
    · exact Or.inr ((Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mp
        (by rw [hdn]; exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff _ _).mpr h))

end

end Work.BoxShrink.PinchOff
