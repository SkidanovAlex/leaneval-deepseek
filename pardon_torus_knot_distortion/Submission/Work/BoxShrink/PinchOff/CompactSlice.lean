import Submission.Work.BoxShrink.PinchOff.tracePerpRealisable_of_sliceArcsOnly
import Submission.Work.BoxShrink.PinchOff.PerpCases
import Submission.Work.BoxShrink.PinchOff.CirclesCase

/-!
# The residual is *exactly* the non-compact slice, i.e. the case in which the trace leaves the box

The hypothesis `SliceArcsOnly` of `ArcsOnly.lean` asks for a cover of the slice by *finitely many*
arcs `a j : ArcInterval → ℝ³` (`ArcInterval = Icc 0 1`) whose images lie in the slice.  Since
`ArcInterval` is compact, such a cover exhibits the slice as a finite union of compact sets, hence
**compact** — and the arcs of a genuine trace (those whose endpoints lie on the box sphere `{B = s}`,
where the box is *open*, `PBox r c σ = {boxNorm < s}`) are open at their endpoints, so no such cover
exists for them.  Consequently

* `not_sliceArcsOnly_of_not_isCompact` — `SliceArcsOnly` *fails* at every configuration whose slice
  is not compact.  The "arcs case" of the residual therefore cannot be described by `SliceArcsOnly`;
  the honest hypothesis is `¬ IsCompact (Sigma …)`, and this is the one used below;
* `isCircleUnion_sigma_of_isCompact`, `sliceCirclesOnly_of_isCompact` and
  `tracePerpRealisable_of_isCompact_slice` — if the slice *is* compact, then (under the box-local
  transversality, which makes it locally Euclidean) it is a finite disjoint union of circles, so the
  **circles-only theorem applies and the residual is settled with no further input**;
* `tracePerpSlice_iff_nonCompactSlice` — hence the whole residual `TracePerpSlice` is *equivalent*
  to its non-compact-slice case, i.e. to the case in which the trace of the cutting plane genuinely
  leaves the box.  This is the case of Pardon's finger move: it is the only place where the arcs,
  the closing circles and the convexity of the box can enter;
* `tracePerpSlice_of_nonCompact` — with the three obligations of `PerpCases.lean` *restricted* to
  the non-compact configurations, and no obligation left in the compact case.

The mathematics of the compact case is the classification of compact one-dimensional subsets of the
surface (`Work.Smooth.OneManifold.isCircleUnion_of_isCompact_of_isLocallyEuclidean`), the local
Euclidean structure of the slice under `TransverseSlice`
(`isLocallyEuclidean_sigma_of_transverseSlice`), and the peeling of
`CirclesCase.lean`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-! ## `SliceArcsOnly` forces the slice to be compact -/

/-- **`SliceArcsOnly` is impossible for a slice that is not compact.**  The arcs of `SliceArcsOnly`
are parametrised on the compact interval, so a finite cover by them makes the slice compact; a
genuine arc of the trace (its endpoints on the box sphere `{boxNorm = s}`, which the box excludes)
is open at its ends and cannot be covered. -/
theorem not_sliceArcsOnly_of_not_isCompact (h : ¬ IsCompact (Sigma ψ s c σ u)) :
    ¬ SliceArcsOnly ψ s c σ u :=
  fun hA => h (isCompact_sigma_of_sliceArcsOnly hA)

/-! ## A compact slice is a finite union of circles -/

/-- **A compact slice is a finite disjoint union of embedded circles** of the surface: under the
box-local transversality the slice is locally Euclidean of dimension one
(`isLocallyEuclidean_sigma_of_transverseSlice`), and the classification of compact one-dimensional
subsets applies. -/
theorem isCircleUnion_sigma_of_isCompact
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u) (hc : IsCompact (Sigma ψ s c σ u)) :
    Work.Smooth.Morse.IsCircleUnion ψ (Sigma ψ s c σ u) :=
  Work.Smooth.OneManifold.isCircleUnion_of_isCompact_of_isLocallyEuclidean ψ
    sigma_subset_carrier hc (isLocallyEuclidean_sigma_of_transverseSlice hT)

/-- **A compact slice is covered by circles only.** -/
theorem sliceCirclesOnly_of_isCompact
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u) (hc : IsCompact (Sigma ψ s c σ u)) :
    SliceCirclesOnly ψ s c σ u := by
  obtain ⟨n, γ, hsimple, hdisj, hcover⟩ := isCircleUnion_sigma_of_isCompact hT hc
  refine ⟨n, γ, hsimple, hdisj, ?_, ?_⟩
  · intro i t
    rw [hcover]
    exact Set.mem_iUnion.mpr ⟨i, ⟨t, rfl⟩⟩
  · intro x hx
    rw [hcover] at hx
    simpa using hx

/-- **The residual at a compact slice, unconditionally**: the circles-only theorem of
`CirclesCase.lean`. -/
theorem tracePerpRealisable_of_isCompact_slice
    (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u) (hc : IsCompact (Sigma ψ s c σ u))
    (hZ : ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u)) :
    Work.BoxShrink.Pinch.TracePerpRealisable (surface ψ) s c σ u :=
  tracePerpRealisable_of_trace_circles_holds hZ (sliceCirclesOnly_of_isCompact hT hc)

/-! ## The residual is exactly its non-compact-slice case -/

/-- **The residual in the case in which the trace leaves the box** — the honest form of Pardon's
finger move.  This is the *only* remaining content of `TracePerpSlice`: at a compact slice the
residual is a theorem (`tracePerpRealisable_of_isCompact_slice`), and `SliceArcsOnly` is
unsatisfiable (`not_sliceArcsOnly_of_not_isCompact`). -/
def TraceNonCompactSlice : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → Work.BoxShrink.Pinch.TameSlice ψ s c σ u →
    ¬ IsCompact (Sigma ψ s c σ u) →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    Work.BoxShrink.Pinch.TracePerpRealisable (surface ψ) s c σ u

/-- **The residual follows from its non-compact-slice case.** -/
theorem tracePerpSlice_of_nonCompactSlice (h : TraceNonCompactSlice) : TracePerpSlice := by
  classical
  exact fun ψ s c σ u hT hTa hZ =>
    if hc : IsCompact (Sigma ψ s c σ u) then
      tracePerpRealisable_of_isCompact_slice hT hc hZ
    else h ψ s c σ u hT hTa hc hZ

/-- **The residual *is* its non-compact-slice case** (`TracePerpSlice` gives it back by
specialisation). -/
theorem nonCompactSlice_of_tracePerpSlice (h : TracePerpSlice) : TraceNonCompactSlice :=
  fun ψ s c σ u hT hTa _ hZ => h ψ s c σ u hT hTa hZ

/-- **The equivalence**: the two forms of the residual are the same statement. -/
theorem tracePerpSlice_iff_nonCompactSlice : TracePerpSlice ↔ TraceNonCompactSlice :=
  ⟨nonCompactSlice_of_tracePerpSlice, tracePerpSlice_of_nonCompactSlice⟩

/-- The corrected residual, in the parent chapter's vocabulary. -/
theorem smoothHalfSTame_of_nonCompactSlice (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : TraceNonCompactSlice) : SmoothHalfSTame :=
  smoothHalfSTame_of_tracePerpSlice hnice (tracePerpSlice_of_nonCompactSlice h)

/-- The corrected residual in the parent chapter's own name for it. -/
theorem pushOffHalfTame_of_nonCompactSlice (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : TraceNonCompactSlice) : Work.BoxShrink.Pinch.PushOffHalfTame :=
  smoothHalfSTame_of_nonCompactSlice hnice h

/-! ## The three obligations of `PerpCases.lean`, restricted to the non-compact slice

Since the compact case is now a theorem, each obligation only has to be proved where the trace
leaves the box. -/

/-- **(K0) for the non-compact slice.** -/
def TraceLineTamedNC : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → Work.BoxShrink.Pinch.TameSlice ψ s c σ u →
    ¬ IsCompact (Sigma ψ s c σ u) →
    ∃ L : Submodule ℚ (ℚ × ℚ), Work.BoxShrink.Pinch.TraceLine (surface ψ) c σ u L

/-- **The per-class finger move for the non-compact slice.** -/
def TracePeriodBoundNC : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (k l : ℤ)
    (L : Submodule ℚ (ℚ × ℚ)),
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → Work.BoxShrink.Pinch.TameSlice ψ s c σ u →
    ¬ IsCompact (Sigma ψ s c σ u) →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    Work.BoxShrink.Pinch.TracePeriod (surface ψ) c σ u k l → (k, l) ≠ 0 →
    Work.BoxShrink.Pinch.TraceLine (surface ψ) c σ u L →
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ⊓
        Submodule.span ℚ {(((k : ℚ)), ((l : ℚ)))} ≤
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)

/-- **The dichotomy for the non-compact slice.** -/
def TraceInessentialHalfOrDropNC : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → Work.BoxShrink.Pinch.TameSlice ψ s c σ u →
    ¬ IsCompact (Sigma ψ s c σ u) →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    (∀ k l : ℤ, Work.BoxShrink.Pinch.TracePeriod (surface ψ) c σ u k l → (k, l) = 0) →
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ≤
        Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) ∨
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) ≠ ⊥

/-- **The non-compact residual, from the three restricted obligations.**  The proof is the exact
case analysis of `PerpCases.lean`; the only difference is the extra `¬ IsCompact` hypothesis, which
is what remains after the compact case is discharged. -/
theorem nonCompactSlice_of_traceLine_periodBound_discharge (h0 : TraceLineTamedNC)
    (hA : TracePeriodBoundNC) (hB : TraceInessentialHalfOrDropNC) : TraceNonCompactSlice := by
  intro ψ s c σ u hT hTa hnc hZ
  by_cases hper : ∃ k l : ℤ,
    Work.BoxShrink.Pinch.TracePeriod (surface ψ) c σ u k l ∧ (k, l) ≠ 0
  · obtain ⟨k, l, hp, hne⟩ := hper
    obtain ⟨L, hL⟩ := h0 ψ s c σ u hT hTa hnc
    exact tracePerpRealisable_of_traceLine_periodBound hL hp hne
      (hA ψ s c σ u k l L hT hTa hnc hZ hp hne hL)
  · push Not at hper
    rcases hB ψ s c σ u hT hTa hnc hZ hper with hle | hne
    · exact Or.inl hle
    · exact tracePerpRealisable_of_noTracePeriod_of_halves_ne_bot hper hne

/-- **The residual, from the three obligations restricted to the non-compact slice.** -/
theorem tracePerpSlice_of_traceLine_periodBound_discharge_nonCompact (h0 : TraceLineTamedNC)
    (hA : TracePeriodBoundNC) (hB : TraceInessentialHalfOrDropNC) : TracePerpSlice :=
  tracePerpSlice_of_nonCompactSlice
    (nonCompactSlice_of_traceLine_periodBound_discharge h0 hA hB)

/-- The corrected residual, from the three restricted obligations. -/
theorem smoothHalfSTame_of_traceLine_periodBound_discharge_nonCompact
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice) (h0 : TraceLineTamedNC)
    (hA : TracePeriodBoundNC) (hB : TraceInessentialHalfOrDropNC) : SmoothHalfSTame :=
  smoothHalfSTame_of_nonCompactSlice hnice
    (nonCompactSlice_of_traceLine_periodBound_discharge h0 hA hB)

end

end Work.BoxShrink.PinchOff
