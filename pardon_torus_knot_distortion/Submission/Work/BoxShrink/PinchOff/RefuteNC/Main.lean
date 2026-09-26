import Submission.Work.BoxShrink.PinchOff.RefuteNC.Config
import Submission.Work.BoxShrink.PinchOff.RefuteNC.transverseSlice_nc
import Submission.Work.BoxShrink.PinchOff.RefuteNC.meridianLoop_nc
import Submission.Work.BoxShrink.PinchOff.RefuteNC.halfUp_inessential
import Submission.Work.BoxShrink.PinchOff.RefuteNC.halfDown_inessential
import Submission.Work.BoxShrink.PinchOff.RefuteNC.slice_inessential_nc
import Submission.Work.BoxShrink.PinchOff.RefuteNC.tameClosedSlice_nc
import Submission.Work.BoxShrink.PinchOff.RefuteNC.trace_nc
import Submission.Work.BoxShrink.PinchOff.RefuteNC.traceClass_nc
import Submission.Work.BoxShrink.PinchOff.RefuteNC.not_isCompact_slice_nc

/-!
# The residual of the pinch is false without the hypothesis on the box sphere

The configuration `ncCtr, ncCyc3, ncRad, ncU` of `RefuteNC/Config.lean` satisfies

* `TransverseSlice` (`RefuteNC.transverseSlice_nc`),
* `TameClosedSlice` (`RefuteNC.tameClosedSlice_nc`),
* `¬ ContainsEssentialLoop Σ` (`RefuteNC.slice_inessential_nc`),

and the box region carries the meridian class `(0,1)` (`RefuteNC.meridianLoop_nc`) while the two
half-regions carry **no** essential loop at all (`RefuteNC.halfUp_inessential`,
`RefuteNC.halfDown_inessential`).  Since `(0,1)` is a period of the cutting plane's trace
(`RefuteNC.trace_nc`), whose every class lies on the line `ℚ·(0,1)` (`RefuteNC.trace_nc`,
`RefuteNC.traceClass_nc`), the residual

  `TracePerpSliceBox = (TransverseSlice → TameClosedSlice → hZ → ⊤ ≤ ⊥ ∨ perp alternative)`

is **false** at this configuration: the first alternative is `W(Ω) ≤ W(Ω⁺ ∪ Ω⁻) = ⊥` against
`(0,1) ≠ 0 ∈ W(Ω)`, and in the second the class `v` is a nonzero multiple of `(0,1)`, so
`ker (crossLin v) = ℚ v = ℚ·(0,1)` meets `W(Ω)` in `ℚ·(0,1) ≠ ⊥` while `W(Ω⁺ ∪ Ω⁻) = ⊥`.

Consequently the whole uncounted residual family of the delivered chapter — `TracePerpSliceBox`,
`TraceClosedSliceResidual`, `TraceClosedNonCompactSlice`, and the parent chapter's
`TracePerpRealisableAll` — is refuted.  The missing hypothesis is exactly `hS`, the inessentiality
of the trace of the **box sphere** (`∂PBox`): Pardon's counting is what supplies it, through his
Lemma 2 (`mustbeinessential`).  Here the box sphere's trace contains the level set `{y = 9/10}`,
whose components are two essential circles of the torus, so `hS` fails; on the other hand the
cutting plane is in perfect general position, and it is its trace that realises the class which the
box region keeps and the halves lose.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **The two half-regions of the configuration carry no essential loop.** -/
theorem halves_inessential_nc :
    Work.SurgeryInvariance.WindingSpan (surface idDiffeo)
      (Halves idDiffeo ncRad ncCtr ncCyc3 ncU) = ⊥ := by
  have h := Work.SurgeryInvariance.Span.union_eq_sup (P := surface idDiffeo)
    (X := Work.BoxShrink.Core.upperRegion (surface idDiffeo) ncRad ncCtr ncCyc3 ncU)
    (Y := Work.BoxShrink.Core.lowerRegion (surface idDiffeo) ncRad ncCtr ncCyc3 ncU)
    (Work.BoxShrink.Core.isOpenInCarrier_upperRegion (surface idDiffeo) ncRad ncCtr ncCyc3 ncU)
    (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion (surface idDiffeo) ncRad ncCtr ncCyc3 ncU)
    (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion (surface idDiffeo) ncRad ncCtr ncCyc3 ncU)
  rw [show Halves idDiffeo ncRad ncCtr ncCyc3 ncU =
      Work.BoxShrink.Core.upperRegion (surface idDiffeo) ncRad ncCtr ncCyc3 ncU ∪
        Work.BoxShrink.Core.lowerRegion (surface idDiffeo) ncRad ncCtr ncCyc3 ncU from rfl,
    h, RefuteNC.halfUp_inessential, RefuteNC.halfDown_inessential, sup_bot_eq]

/-- **The box region of the configuration realises the meridian class `(0,1)`.** -/
theorem zeroOne_mem_omega_nc :
    ((0 : ℚ), (1 : ℚ)) ∈ Work.SurgeryInvariance.WindingSpan (surface idDiffeo)
      (Omega idDiffeo ncRad ncCtr ncCyc3) := by
  obtain ⟨γ, hγ, hw⟩ := RefuteNC.meridianLoop_nc
  have h := zzClass_mem_windingSpan (P := surface idDiffeo)
    (X := Omega idDiffeo ncRad ncCtr ncCyc3) hγ
  have hzz : zzClass (P := surface idDiffeo) γ = ((0 : ℚ), (1 : ℚ)) := by
    rw [zzClass, hw, zzCast]; norm_num
  rwa [hzz] at h

/-- **A line of `ℚ²` containing a nonzero vector is spanned by it.** -/
theorem eq_span_of_finrank_le_one {L : Submodule ℚ (ℚ × ℚ)} {v : ℚ × ℚ}
    (hv : v ∈ L) (hfin : Module.finrank ℚ ↥L ≤ 1) (hvne : v ≠ 0) :
    L = Submodule.span ℚ {v} := by
  have hge : Submodule.span ℚ {v} ≤ L := Submodule.span_le.mpr (by rintro y rfl; exact hv)
  have h1 : Module.finrank ℚ ↥(Submodule.span ℚ {v}) = 1 := by
    rw [show (Submodule.span ℚ {v} : Submodule ℚ (ℚ × ℚ)) = ℚ ∙ v from rfl]
    exact finrank_span_singleton hvne
  exact (Submodule.eq_of_le_of_finrank_le hge (by rw [h1]; exact hfin)).symm

/-- **A nonzero vector of the line `ℚ·(0,1)` spans that line.** -/
theorem span_eq_of_mem_span {v : ℚ × ℚ} (hv : v ∈ Submodule.span ℚ {((0 : ℚ), (1 : ℚ))})
    (hvne : v ≠ 0) :
    Submodule.span ℚ {v} = Submodule.span ℚ {((0 : ℚ), (1 : ℚ))} := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
  have hcne : c ≠ 0 := by
    rintro rfl
    exact hvne (by simpa using hc.symm)
  rw [← hc]
  exact Submodule.span_singleton_smul_eq (IsUnit.mk0 c hcne) _

/-- **The class `(0,1)` is not realised in the halves.** -/
theorem zeroOne_notMem_halves_nc :
    ((0 : ℚ), (1 : ℚ)) ∉ Work.SurgeryInvariance.WindingSpan (surface idDiffeo)
      (Halves idDiffeo ncRad ncCtr ncCyc3 ncU) := by
  rw [halves_inessential_nc]
  exact fun h => (by norm_num : ((0 : ℚ), (1 : ℚ)) ≠ 0) (Submodule.mem_bot ℚ |>.mp h)

/-- **The residual `TracePerpRealisable` is false at the configuration.** -/
theorem not_tracePerpRealisable_nc :
    ¬ Work.BoxShrink.Pinch.TracePerpRealisable (surface idDiffeo) ncRad ncCtr ncCyc3 ncU := by
  rintro (hle | ⟨v, hvne, ⟨L, hL, hvL⟩, hineq⟩)
  · exact zeroOne_notMem_halves_nc (hle zeroOne_mem_omega_nc)
  · -- the trace line contains `(0,1)`, so it *is* `ℚ·(0,1)`, and `v` is a nonzero multiple of it
    have h01 : ((0 : ℚ), (1 : ℚ)) ∈ L := hL.2 0 1 RefuteNC.trace_nc.1
    have hline : L = Submodule.span ℚ {((0 : ℚ), (1 : ℚ))} :=
      eq_span_of_finrank_le_one h01 hL.1 (by norm_num)
    have hvspan : v ∈ Submodule.span ℚ {((0 : ℚ), (1 : ℚ))} := hline ▸ hvL
    have hspanv : Submodule.span ℚ {v} = Submodule.span ℚ {((0 : ℚ), (1 : ℚ))} :=
      span_eq_of_mem_span hvspan hvne
    have hker : LinearMap.ker (Work.BoxShrink.Pinch.crossLin v) =
        Submodule.span ℚ {((0 : ℚ), (1 : ℚ))} := by
      rw [ker_crossLin_eq_span hvne, hspanv]
    have hmem : ((0 : ℚ), (1 : ℚ)) ∈ Work.SurgeryInvariance.WindingSpan (surface idDiffeo)
        (Omega idDiffeo ncRad ncCtr ncCyc3) ⊓
          LinearMap.ker (Work.BoxShrink.Pinch.crossLin v) :=
      ⟨zeroOne_mem_omega_nc, by rw [hker]; exact Submodule.subset_span (Set.mem_singleton _)⟩
    exact zeroOne_notMem_halves_nc (hineq hmem)

/-- **The honest residual `TraceClosedSliceResidual` is false.** -/
theorem not_traceClosedSliceResidual : ¬ TraceClosedSliceResidual := fun h =>
  not_tracePerpRealisable_nc
    (h idDiffeo ncRad ncCtr ncCyc3 ncU RefuteNC.transverseSlice_nc
      RefuteNC.tameClosedSlice_nc RefuteNC.slice_inessential_nc)

/-- **The non-compact case `TraceClosedNonCompactSlice` of the residual is false.** -/
theorem not_traceClosedNonCompactSlice : ¬ TraceClosedNonCompactSlice := fun h =>
  not_tracePerpRealisable_nc
    (h idDiffeo ncRad ncCtr ncCyc3 ncU RefuteNC.transverseSlice_nc
      RefuteNC.tameClosedSlice_nc RefuteNC.not_isCompact_slice_nc
      RefuteNC.slice_inessential_nc)

/-- **The box-local residual `TracePerpSliceBox` is false.** -/
theorem not_tracePerpSliceBox : ¬ TracePerpSliceBox := by
  intro h
  rcases h idDiffeo ncRad ncCtr ncCyc3 ncU RefuteNC.transverseSlice_nc
      RefuteNC.tameClosedSlice_nc RefuteNC.slice_inessential_nc with hle | hperp
  · exact zeroOne_notMem_halves_nc (hle zeroOne_mem_omega_nc)
  · obtain ⟨v, _n, γ, hvne, hγtrace, _hγmem, _hdisj, hvspan, hineq⟩ := hperp
    -- every class of a trace curve lies on `ℚ·(0,1)`, so `v` does too
    have hv : v ∈ Submodule.span ℚ {((0 : ℚ), (1 : ℚ))} := by
      refine Submodule.span_le.mpr (fun x hx => ?_) hvspan
      obtain ⟨i, rfl⟩ := hx
      exact RefuteNC.traceClass_nc (γ i) (hγtrace i)
    have hspanv : Submodule.span ℚ {v} = Submodule.span ℚ {((0 : ℚ), (1 : ℚ))} :=
      span_eq_of_mem_span hv hvne
    have hker : LinearMap.ker (Work.BoxShrink.Pinch.crossLin v) =
        Submodule.span ℚ {((0 : ℚ), (1 : ℚ))} := by
      rw [ker_crossLin_eq_span hvne, hspanv]
    have hmem : ((0 : ℚ), (1 : ℚ)) ∈ Work.SurgeryInvariance.WindingSpan (surface idDiffeo)
        (Omega idDiffeo ncRad ncCtr ncCyc3) ⊓
          LinearMap.ker (Work.BoxShrink.Pinch.crossLin v) :=
      ⟨zeroOne_mem_omega_nc, by rw [hker]; exact Submodule.subset_span (Set.mem_singleton _)⟩
    exact zeroOne_notMem_halves_nc (hineq hmem)

/-- **The parent chapter's `TracePerpAll` (K2 for every parametrised torus) is false**: it carries
no hypothesis on the box sphere either. -/
theorem not_tracePerpAll : ¬ Work.BoxShrink.Pinch.TracePerpAll := by
  intro h
  rcases h (surface idDiffeo) ncRad ncCtr ncCyc3 ncU RefuteNC.slice_inessential_nc with
    ⟨v, hvne, ⟨L, hL, hvL⟩, hineq⟩ | hle
  · have h01 : ((0 : ℚ), (1 : ℚ)) ∈ L := hL.2 0 1 RefuteNC.trace_nc.1
    have hline : L = Submodule.span ℚ {((0 : ℚ), (1 : ℚ))} :=
      eq_span_of_finrank_le_one h01 hL.1 (by norm_num)
    have hvspan : v ∈ Submodule.span ℚ {((0 : ℚ), (1 : ℚ))} := hline ▸ hvL
    have hspanv : Submodule.span ℚ {v} = Submodule.span ℚ {((0 : ℚ), (1 : ℚ))} :=
      span_eq_of_mem_span hvspan hvne
    have hker : LinearMap.ker (Work.BoxShrink.Pinch.crossLin v) =
        Submodule.span ℚ {((0 : ℚ), (1 : ℚ))} := by
      rw [ker_crossLin_eq_span hvne, hspanv]
    exact zeroOne_notMem_halves_nc
      (hineq ⟨zeroOne_mem_omega_nc, by
        rw [hker]; exact Submodule.subset_span (Set.mem_singleton _)⟩)
  · exact zeroOne_notMem_halves_nc (hle zeroOne_mem_omega_nc)

/-- **The parent chapter's `TracePerpRealisableAll` is false** (it has no hypothesis on the box
sphere). -/
theorem not_tracePerpRealisableAll :
    ¬ Work.BoxShrink.Pinch.TracePerpRealisableAll := fun h =>
  not_tracePerpRealisable_nc
    (h (surface idDiffeo) ncRad ncCtr ncCyc3 ncU RefuteNC.slice_inessential_nc)

/-! ## The per-class bound in the honest tameness is false too -/

/-- **The per-class bound (`CompactSlice.TracePeriodBoundNC` with `TameSlice` replaced by the honest
`TameClosedSlice`)**: a trace class realised in the box region is realised in the two half-regions.

This is the form the "finger move" of the chapter's §16.5/§20 produces, and the form the assignment
names as "a trace class carried by the box region is carried by the halves"; `PerpCases.lean` links
it to the perpendicular residual (`tracePeriodBound_of_traceClassBound`) and `CompactSlice.lean`
isolates it as `TracePeriodBoundNC`. -/
def TracePeriodBoundClosedNC : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (k l : ℤ)
    (L : Submodule ℚ (ℚ × ℚ)),
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → TameClosedSlice ψ s c σ u →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    Work.BoxShrink.Pinch.TracePeriod (surface ψ) c σ u k l → (k, l) ≠ 0 →
    Work.BoxShrink.Pinch.TraceLine (surface ψ) c σ u L →
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ⊓
        Submodule.span ℚ {(((k : ℚ)), ((l : ℚ)))} ≤
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)

/-- **The per-class bound is FALSE** — so it is *not* interchangeable with the dimension bound
`KeyTameClosed`: at the configuration of `RefuteNC/Config.lean` the class `(0,1)` is a period of the
trace of the cutting plane and is realised in the box region, but the two half-regions realise
nothing at all.  This is the exact sense in which the "finger move" form of the datum is too strong
and only Pardon's *conclusion* (equivalently the dimension bound) can be true. -/
theorem not_tracePeriodBoundClosedNC : ¬ TracePeriodBoundClosedNC := by
  intro h
  have hmem : ((0 : ℚ), (1 : ℚ)) ∈ Work.SurgeryInvariance.WindingSpan (surface idDiffeo)
      (Omega idDiffeo ncRad ncCtr ncCyc3) ⊓
        Submodule.span ℚ {(((0 : ℤ) : ℚ), ((1 : ℤ) : ℚ))} :=
    ⟨zeroOne_mem_omega_nc, Submodule.subset_span (Set.mem_singleton _)⟩
  have := h idDiffeo ncRad ncCtr ncCyc3 ncU 0 1 (Submodule.span ℚ {((0 : ℚ), (1 : ℚ))})
    RefuteNC.transverseSlice_nc RefuteNC.tameClosedSlice_nc RefuteNC.slice_inessential_nc
    RefuteNC.trace_nc.1 (by norm_num) RefuteNC.trace_nc.2
  exact zeroOne_notMem_halves_nc (this hmem)

end

end Work.BoxShrink.PinchOff
