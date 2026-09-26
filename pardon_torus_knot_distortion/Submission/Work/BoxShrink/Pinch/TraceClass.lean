import Submission.Work.BoxShrink.Pinch.Bridge
import Submission.Work.BoxShrink.Pinch.LocalForm
import Submission.Work.BoxShrink.Pinch.PushOffNoJump
import Submission.Work.BoxShrink.Pinch.PerpForm

/-!
# The residual of the pinch, with the trace class *realised*

`Trace.lean` isolated the two ingredients of Pardon's pinch: **(K0)** the periods of the trace of
the cutting plane lie in a line `L` (`TraceLine`), and **(K2)** every class of the box region
perpendicular to a nonzero `v ∈ L` is realised in the two half-regions (`TracePerpRealisable`,
`TraceMultipleRealisable`).  The class `v` is only required to *lie in* the line `L` there, not to be
realised by an actual loop of the trace.

This module records that **that weaker requirement makes the residual equivalent to the goal**: if
the line `L` happens to be nonzero and the two half-regions are inessential, the residual of
`TraceMultipleRealisable` is satisfied by *any* nonzero class of `L` which the box region does not
realise, which is precisely the assertion `dim W(box) ≤ 1` — i.e. `PinchNoJump`.  The honest form of
(K2), and the one which the crossing-number argument actually proves, requires

  `v ∈ WindingSpan P (planeTrace P c σ u)`,

so that `v` is a class *carried by a loop of the trace*.  This module

* proves that the two conditions on the trace are equivalent modulo the dimension bound (K0):
  `exists_traceLine_iff_finrank_le_one` says
  `(∃ L, TraceLine P c σ u L) ↔ finrank (WindingSpan P (planeTrace P c σ u)) ≤ 1`,
  i.e. (K0) is exactly "the trace of the plane carries no two independent essential loops";
* states the residual in the honest form, `TraceClassBound` / `TraceClassBoundAll`;
* proves the whole endgame from it: `pinchNoJumpAll_of_traceClassBoundAll`,
  `pinchNoJump_of_traceClassBoundAll`, `smoothHalfS_of_traceClassBoundAll`,
  `pushOffHalf_of_boxDichotomy_traceClassBoundAll`,
  `cruxStatement_of_boxDichotomy_traceClassBoundAll`,
  `pardon_torus_knot_distortion_of_traceClassBoundAll`;
* proves the two degenerate instances of the residual;
* and relates it to the chapter's `TraceMultipleRealisable`
  (`traceMultipleRealisable_of_traceClassBound`: the honest form gives the chapter's, given (K0)).

## Why the realised class is the right hypothesis

Let `γ` be a loop of the box region whose winding is a multiple of the class `v` of a trace circle.
Because the oriented trace of the plane is the boundary of the two sides of `F` it has vanishing
homology class, `[T] = 0`; hence the *total* crossing number of `γ` with `T` vanishes automatically.
What is not automatic — and what has to be proved — is that the crossing number of `γ` with *each
component* of the trace vanishes, which is precisely `⟨winding γ, [c]⟩ = 0`, i.e. that `v` is a
multiple of the trace class.  For such a `γ` the crossings of `γ` with the slice come in pairs of
opposite sign and can be cancelled (Pardon's finger move, `hZ`), which gives a loop of a half with
the same winding class: this is `TraceClassBound`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.Pinch

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The trace of the cutting plane -/

/-- **The trace of the cutting plane** as a subset of the surface: the points of `F` lying on the
plane `{y (σ 2) = c (σ 2) + u}`.  (`tracePreimage` is its preimage in the parameter plane.) -/
def planeTrace (P : Work.CoreTopology.ParamTorus) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Set R3 :=
  P.carrier ∩ Work.BoxShrink.Core.cutPlane c σ u

@[simp] theorem mem_planeTrace {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {y : R3} :
    y ∈ planeTrace P c σ u ↔ y ∈ P.carrier ∧ y (σ 2) = c (σ 2) + u := Iff.rfl

/-- The trace of the plane is the union of the slice and the parts of the two half-regions of the
box that lie on its boundary; the *values* of the trace function are the same as those of
`Work.BoxShrink.Pinch.tracePreimage`. -/
theorem tracePreimage_eq_planePreimage (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    tracePreimage P c σ u = planePreimage P (Work.BoxShrink.Core.cutPlane c σ u) := rfl

/-- `TracePeriod` is literally `PeriodRealised` for the cutting plane. -/
theorem tracePeriod_iff_periodRealised (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (k l : ℤ) :
    TracePeriod P c σ u k l ↔ PeriodRealised P (Work.BoxShrink.Core.cutPlane c σ u) k l := by
  constructor
  · rintro ⟨q, hq, hper, hmem⟩
    exact ⟨q, hq, hper, fun t => (mem_planePreimage).mp (hmem t)⟩
  · rintro ⟨q, hq, hper, hmem⟩
    exact ⟨q, hq, hper, fun t => (mem_planePreimage).mpr (hmem t)⟩

/-- The winding span of the trace does not change if the surface is intersected in as well: every
loop of the parametrisation already lies on the carrier. -/
theorem windingSpan_planeTrace (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Work.SurgeryInvariance.WindingSpan P (planeTrace P c σ u) =
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.cutPlane c σ u) := by
  refine le_antisymm (Work.SurgeryInvariance.WindingSpan_mono P Set.inter_subset_right) ?_
  rw [Work.SurgeryInvariance.WindingSpan, Submodule.span_le]
  rintro v ⟨γ, hγ, rfl⟩
  exact Submodule.subset_span ⟨γ, fun t => ⟨γ.mem t, hγ t⟩, rfl⟩

/-- **A trace period is a class of the winding span of the trace.** -/
theorem tracePeriod_mem_windingSpan {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} {k l : ℤ}
    (h : TracePeriod P c σ u k l) :
    (((k : ℚ), (l : ℚ)) : ℚ × ℚ) ∈
      Work.SurgeryInvariance.WindingSpan P (planeTrace P c σ u) := by
  have hspan : Work.SurgeryInvariance.WindingSpan P (planeTrace P c σ u) =
      periodSpan P (Work.BoxShrink.Core.cutPlane c σ u) := by
    rw [windingSpan_planeTrace, ← periodSpan_eq_windingSpan]
  rw [hspan]
  exact Submodule.subset_span
    ⟨k, l, (tracePeriod_iff_periodRealised c σ u k l).mp h, rfl⟩

/-! ## (K0) is a dimension bound -/

/-- **The trace line contains the whole winding span of the trace.**  (`TraceLine` asks only that it
contain the realised periods; the span of the periods *is* the winding span.) -/
theorem windingSpan_planeTrace_le_of_traceLine {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {L : Submodule ℚ (ℚ × ℚ)} (h : TraceLine P c σ u L) :
    Work.SurgeryInvariance.WindingSpan P (planeTrace P c σ u) ≤ L := by
  rw [windingSpan_planeTrace, ← periodSpan_eq_windingSpan]
  refine Submodule.span_le.mpr ?_
  rintro v ⟨k, l, hper, rfl⟩
  exact h.2 k l ((tracePeriod_iff_periodRealised c σ u k l).mpr hper)

/-- **The winding span of the trace itself is a trace line**, as soon as it has dimension at most
one. -/
theorem traceLine_windingSpan {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (planeTrace P c σ u)) ≤ 1) :
    TraceLine P c σ u (Work.SurgeryInvariance.WindingSpan P (planeTrace P c σ u)) :=
  ⟨h, fun _ _ hper => tracePeriod_mem_windingSpan hper⟩

/-- **(K0) is exactly the dimension bound `dim W(trace) ≤ 1`.**  There is a trace line if and only
if the trace of the cutting plane carries no two loops with independent winding vectors, i.e. its
winding span is at most one-dimensional. -/
theorem exists_traceLine_iff_finrank_le_one (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    (∃ L : Submodule ℚ (ℚ × ℚ), TraceLine P c σ u L) ↔
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (planeTrace P c σ u)) ≤ 1 := by
  constructor
  · rintro ⟨L, hL⟩
    exact le_trans (Submodule.finrank_mono (windingSpan_planeTrace_le_of_traceLine hL)) hL.1
  · intro h
    exact ⟨_, traceLine_windingSpan h⟩

/-- **(K0), in the form the residual consumes it**: for every configuration the trace's winding
span is at most one-dimensional.  (This is the statement to prove for the smooth tori of the
challenge; it is the dimension form of
`Work.BoxShrink.Pinch.DisjointLoopsWindingDet`.) -/
def TraceSpanLeOne : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (planeTrace P c σ u)) ≤ 1

/-- `TraceLineAll` and `TraceSpanLeOne` are the same statement. -/
theorem traceLineAll_iff_traceSpanLeOne : TraceLineAll ↔ TraceSpanLeOne := by
  constructor
  · intro h P c σ u
    exact (exists_traceLine_iff_finrank_le_one (P := P) c σ u).mp (h P c σ u)
  · intro h P c σ u
    exact (exists_traceLine_iff_finrank_le_one (P := P) c σ u).mpr (h P c σ u)

/-- **(K0) for the smooth tori of the challenge**: with the cutting plane transverse along the
whole trace, the trace's winding span is at most one-dimensional — the trace of the plane carries no
two loops with independent winding vectors.  This is the dimension form of
`Work.BoxShrink.Pinch.DisjointLoopsWindingDet` (which gives it for two *disjoint* trace loops, and
hence for loops in distinct components of the trace). -/
def TraceSpanLeOneSmooth : Prop :=
  ∀ (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    TransverseTrace ψ c σ u →
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (planeTrace (Work.Smooth.Morse.torus ψ) c σ u)) ≤ 1

/-- **(K0) for the smooth tori, in the line form** of the chapter (`TraceLineSmooth`). -/
theorem traceLineSmooth_of_traceSpanLeOneSmooth (h : TraceSpanLeOneSmooth) : TraceLineSmooth :=
  fun ψ c σ u hT => ⟨_, traceLine_windingSpan (P := Work.Smooth.Morse.torus ψ) (h ψ c σ u hT)⟩

/-! ## The residual, with the trace class realised -/

/-- **The residual of the pinch, honest form.**

**WARNING (added later; see `EXP/README.md`).**  In the case `WindingSpan (planeTrace) = ⊥` this
statement reduces (`traceClassBound_iff_box_le_halves_of_traceSpan_bot`) to the *span inequality*
`W(boxRegion) ≤ W(halves)`, and that inequality is **false** for the box/plane geometry: at the
standard torus of revolution with `σ = swap 1 2`, `s = 1.8`, `u = 0` the sphere trace is inessential
(so `hS` holds), the slice is inessential (`hZ`), the region inside the box realises the whole of
`H₁(T²;ℚ)` while the union of the two half-regions realises only a *line* — the divide-and-conquer
discretisation in `EXP/` reproduces both published facts at `s = 3/2` and this configuration at
`s = 1.8`.  The `+1` bound of `SliceSpanStep.lean` (`PinchNoJump`) is not affected (it holds with
equality there), and neither is the conclusion `BubbleHalf`; the residual of the area has to be
stated in one of those two forms, not as an equality or containment of the two spans.  The
definition is kept as the record of the route that session 5 took.

Either every class of the box region is realised in
the two half-regions, or there is a nonzero class `v` *of the trace* — realised by a loop of the
trace of the cutting plane — whose multiples realised in the box region are realised in the
halves.

This differs from `Work.BoxShrink.Pinch.TraceMultipleRealisable` in the requirement
`v ∈ WindingSpan P (planeTrace P c σ u)` in place of `∃ L, TraceLine ∧ v ∈ L`: the latter is
satisfied by *any* class of a nonzero trace line which the box region does not carry, which (when
the halves are inessential) is the assertion to be proved. -/
def TraceClassBound (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≤
      Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u) ∨
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      v ∈ Work.SurgeryInvariance.WindingSpan P (planeTrace P c σ u) ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ⊓
          Submodule.span ℚ {v} ≤
        Work.SurgeryInvariance.WindingSpan P
          (Work.BoxShrink.Core.upperRegion P s c σ u ∪
            Work.BoxShrink.Core.lowerRegion P s c σ u)

/-- The residual for every configuration whose slice carries no essential loop. -/
def TraceClassBoundAll : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
      TraceClassBound P s c σ u

/-- **The honest residual gives Pardon's dimension bound.** -/
theorem pinchNoJumpAll_of_traceClassBoundAll (h : TraceClassBoundAll) : PinchNoJumpAll := by
  intro P s c σ u _hS hZ
  rcases h P s c σ u hZ with hle | ⟨v, hv, _hvT, hperp⟩
  · exact Nat.le_add_right_of_le (Submodule.finrank_mono hle)
  · exact finrank_le_succ_of_inf_span_le hv hperp

/-- **The honest residual gives the chapter's residual**, once (K0) is known: a realised trace class
lies in every trace line. -/
theorem traceMultipleRealisable_of_traceLine_traceClassBound {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (h0 : ∃ L : Submodule ℚ (ℚ × ℚ), TraceLine P c σ u L)
    (h : TraceClassBound P s c σ u) : TraceMultipleRealisable P s c σ u := by
  rcases h with hle | ⟨v, hv, hvT, hperp⟩
  · exact Or.inl hle
  · obtain ⟨L, hL⟩ := h0
    exact Or.inr ⟨v, hv, ⟨L, hL, windingSpan_planeTrace_le_of_traceLine hL hvT⟩, hperp⟩

/-- **The chapter's residual from the honest one and (K0).** -/
theorem traceMultipleRealisableAll_of_traceSpanLeOne_traceClassBoundAll
    (h0 : TraceSpanLeOne) (h : TraceClassBoundAll) : TraceMultipleRealisableAll :=
  fun P s c σ u hZ =>
    traceMultipleRealisable_of_traceLine_traceClassBound
      ((exists_traceLine_iff_finrank_le_one (P := P) c σ u).mpr (h0 P c σ u))
      (h P s c σ u hZ)

/-- **Pardon's dimension bound for the smooth tori, from the honest residual.** -/
theorem pinchNoJump_of_traceClassBoundAll (h : TraceClassBoundAll) : PinchNoJump := by
  intro ψ s c σ u hS hZ
  exact pinchNoJumpAll_of_traceClassBoundAll h (Work.Smooth.Morse.torus ψ) s c σ u hS hZ

/-- **Pardon's Lemma 3 for the smooth tori, from the honest residual.** -/
theorem smoothHalfS_of_traceClassBoundAll (h1 : Equation1Input) (hnice : BoxSliceNice)
    (h : TraceClassBoundAll) : SmoothHalfS :=
  smoothHalfS_of_pinchNoJump h1 hnice (pinchNoJump_of_traceClassBoundAll h)

/-- **The caller's field `Work.BoxShrink.Bubble.PushOffHalf`, from the honest residual.** -/
theorem pushOffHalf_of_boxDichotomy_traceClassBoundAll (hdich : BoxDichotomyInput)
    (h : TraceClassBoundAll) : Work.BoxShrink.Bubble.PushOffHalf :=
  pushOffHalf_of_boxDichotomy_noJump hdich (pinchNoJumpAll_of_traceClassBoundAll h)

/-- **The crux, from the honest residual.** -/
theorem cruxStatement_of_boxDichotomy_traceClassBoundAll
    (hcleanD : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (hdich : BoxDichotomyInput) (h : TraceClassBoundAll)
    (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ p q : ℕ, Work.BoxShrink.CruxStatement p q :=
  cruxStatement_of_boxDichotomy_noJump hcleanD hdich (pinchNoJumpAll_of_traceClassBoundAll h)
    hclean hae

/-- **Pardon's Theorem 1.1 from the honest residual.** -/
theorem pardon_torus_knot_distortion_of_traceClassBoundAll
    (hdisc : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.InnermostDisk.CleansInSphere
        (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (Work.BoxShrink.Core.cutDisc s c σ u))
    (h1 : Equation1Input) (hnice : BoxSliceNice) (h : TraceClassBoundAll)
    (hclean : Work.BoxShrink.CleansDiscsAll) (hae : Work.BoxShrink.AeSlicedAll) :
    ∀ (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q) (K : Knot)
      (_hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
        ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)),
      (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  pardon_torus_knot_distortion_of_smoothHalfS hdisc
    (smoothHalfS_of_traceClassBoundAll h1 hnice h) hclean hae

/-- **The chapter's residual `Work.BoxShrink.Pinch.TraceMultipleTame` from the honest residual**,
given (K0). -/
theorem traceMultipleTame_of_traceLineAll_traceClassBoundAll (h0 : TraceLineAll)
    (h : TraceClassBoundAll) : TraceMultipleTame := by
  intro ψ s c σ u _hT _htame _hS hZ
  exact traceMultipleRealisable_of_traceLine_traceClassBound
    (h0 (Work.Smooth.Morse.torus ψ) c σ u) (h (Work.Smooth.Morse.torus ψ) s c σ u hZ)

/-- **The deliverable's `Work.BoxShrink.Pinch.PushOffHalfTame` from the honest residual and
(K0)**, through the chapter's `TraceMultipleTame`: no hypothesis outside the two documented
geometric inputs of the residual and (K0) is used. -/
theorem pushOffHalfTame_of_traceLineAll_traceClassBoundAll (h0 : TraceLineAll)
    (h1 : Equation1Input) (hnice : BoxSliceNice) (h : TraceClassBoundAll) :
    PushOffHalfTame :=
  pushOffHalfTame_of_traceMultipleTame h1 hnice
    (traceMultipleTame_of_traceLineAll_traceClassBoundAll h0 h)

/-- **The residual in the local form of the deliverable**: the honest (K2) for the smooth tori of
the challenge, with the two documented geometric hypotheses (`TransverseSlice`, `TameSlice`) of the
configuration and the two inessentiality hypotheses.  Its second branch asks for a class `v` *of the
trace* (realised by a loop of the cutting plane), which is what the crossing-number argument
supplies. -/
def TraceClassBoundTame : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    TransverseSlice ψ s c σ u → TameSlice ψ s c σ u →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) →
    TraceClassBound (Work.Smooth.Morse.torus ψ) s c σ u

/-- **The deliverable's `Work.BoxShrink.Pinch.PushOffHalfTame` from the honest residual**, with
Pardon's equation (1) and the general position of the box-sphere trace.  Note that **(K0) is *not*
needed** for this route: the second branch of `TraceClassBound` already bounds the dimension drop. -/
theorem pushOffHalfTame_of_traceClassBoundTame (h1 : Equation1Input) (hnice : BoxSliceNice)
    (h : TraceClassBoundTame) : PushOffHalfTame := by
  intro ψ s c σ u hT htame hS hZ
  refine bubbleHalf_of_dichotomy_noJump
    (pardonDichotomy_boxRegion_of_equation1 h1 (hnice ψ s c σ) hS) ?_
  rcases h ψ s c σ u hT htame hS hZ with hle | ⟨v, hv, _hvT, hperp⟩
  · exact Nat.le_add_right_of_le (Submodule.finrank_mono hle)
  · exact finrank_le_succ_of_inf_span_le hv hperp

/-- (K2) for every parametrised torus gives the tame form, hence (with the two classical inputs) the
deliverable. -/
theorem traceClassBoundTame_of_traceClassBoundAll (h : TraceClassBoundAll) : TraceClassBoundTame :=
  fun _ _ _ _ _ _ _ _ hZ => h _ _ _ _ _ hZ

/-! ## The residual split into its two independent cases

The residual `TraceClassBoundTame` is the conjunction of two statements: the case in which the trace
of the plane carries a nonzero class (the classic finger move, in which the crossing number with the
trace is what has to be cancelled), and the case in which the whole trace is contractible (in which
the pinch is a trivial `2`-surgery and the invariant should not drop at all). -/

/-- **(K2), case `W(trace) ≠ ⊥`**: every multiple of a class *of the trace*, realised by a loop of
the box region, is realised in the two half-regions.  This is the case the crossing-number argument
addresses. -/
def TraceClassBoundSpanNeBot : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    TransverseSlice ψ s c σ u → TameSlice ψ s c σ u →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) →
    Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
      (planeTrace (Work.Smooth.Morse.torus ψ) c σ u) ≠ ⊥ →
    TraceClassBound (Work.Smooth.Morse.torus ψ) s c σ u

/-- **(K2), case `W(trace) = ⊥`**: if the cutting plane meets the surface only in contractible
curves, then the invariant of the region inside the box does not drop at all — the pinch is a
trivial `2`-surgery.  (By `traceClassBound_iff_box_le_halves_of_traceSpan_bot` this is what the
residual says in that configuration.) -/
def TraceClassBoundSpanBot : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    TransverseSlice ψ s c σ u → TameSlice ψ s c σ u →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) →
    Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
      (planeTrace (Work.Smooth.Morse.torus ψ) c σ u) = ⊥ →
    Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) ≤
      Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
          Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u)

/-- **The two cases of the residual give the residual**, and hence (with Pardon's equation (1) and
the general position of the box-sphere trace) the deliverable. -/
theorem traceClassBoundTame_of_spanNeBot_spanBot (h1 : TraceClassBoundSpanNeBot)
    (h0 : TraceClassBoundSpanBot) : TraceClassBoundTame := by
  intro ψ s c σ u hT htame hS hZ
  by_cases hbot : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
      (planeTrace (Work.Smooth.Morse.torus ψ) c σ u) = ⊥
  · exact Or.inl (h0 ψ s c σ u hT htame hS hZ hbot)
  · exact h1 ψ s c σ u hT htame hS hZ hbot

/-! ## The two forms compared, and the partial instances

`TraceMultipleRealisable` and `TraceClassBound` differ exactly in the condition on `v`.  Below:
the two coincide in the case that matters (`W(trace) ≠ 0`, where the line of (K0) *is* the span of
the trace's classes), while in the degenerate case `W(trace) = ⊥` — the cutting plane cutting the
surface only in contractible curves — the chapter's form can be satisfied by a class that no loop
of the trace realises. -/

/-- **In the presence of (K0) and of a trace class, the two forms coincide.**  If the trace carries
a nonzero class, then the line of `TraceLine` is the span of that class, so a class lying in the
line is a multiple of a realised trace class. -/
theorem traceClassBound_of_traceRealisable_span_ne_bot {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (hvT : Work.SurgeryInvariance.WindingSpan P (planeTrace P c σ u)
      ≠ ⊥) (h : TraceMultipleRealisable P s c σ u) : TraceClassBound P s c σ u := by
  rcases h with hle | ⟨v, hv, ⟨L, hL, hvL⟩, hperp⟩
  · exact Or.inl hle
  · obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hvT
    have hwL : w ∈ L := windingSpan_planeTrace_le_of_traceLine hL hwW
    have hvle : Submodule.span ℚ {v} ≤ L := Submodule.span_le.mpr (by simpa using hvL)
    have hwle : Submodule.span ℚ {w} ≤ L := Submodule.span_le.mpr (by simpa using hwL)
    have hfw : Module.finrank ℚ ↥(Submodule.span ℚ {w}) = 1 := finrank_span_singleton hw0
    have hfv : Module.finrank ℚ ↥(Submodule.span ℚ {v}) = 1 := finrank_span_singleton hv
    have hge : 1 ≤ Module.finrank ℚ ↥L := hfw ▸ Submodule.finrank_mono hwle
    have hLw : Submodule.span ℚ {w} = L :=
      Submodule.eq_of_le_of_finrank_eq hwle (hfw.trans (le_antisymm hge hL.1))
    have hLv : Submodule.span ℚ {v} = L :=
      Submodule.eq_of_le_of_finrank_eq hvle
        (hfv.trans (le_antisymm (hfv ▸ Submodule.finrank_mono hvle) hL.1))
    refine Or.inr ⟨w, hw0, hwW, ?_⟩
    rw [hLw, ← hLv]
    exact hperp

/-- **The chapter's residual is satisfied trivially when the trace is contractible and a
half-region carries an essential loop.**  In that case a nonzero class of the halves lies on *any*
line (in particular on a trace line, of which the plane's trace has `⊥` as one), so the second
branch of `TraceMultipleRealisable` needs no geometry at all — this is the sense in which the
condition `∃ L, TraceLine ∧ v ∈ L` is weaker than realising `v` by a loop of the trace. -/
theorem traceMultipleRealisable_of_traceSpan_bot_halves_ne_bot {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hbot : Work.SurgeryInvariance.WindingSpan P (planeTrace P c σ u) = ⊥)
    (hne : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u) ≠ ⊥) :
    TraceMultipleRealisable P s c σ u := by
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine Or.inr ⟨v, hv0, ⟨Submodule.span ℚ {v}, ?_, Submodule.mem_span_singleton_self v⟩, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [finrank_span_singleton hv0]
    · intro k l hper
      have hmem := tracePeriod_mem_windingSpan hper
      rw [hbot] at hmem
      have h0 : ((k : ℚ), (l : ℚ)) = 0 := by simpa using hmem
      rw [h0]
      exact Submodule.zero_mem _
  · exact le_trans inf_le_right (Submodule.span_le.mpr (by simpa using hvW))

/-- **A partial instance of the honest residual**: if a nonzero class of the trace is itself
realised by a loop of one of the half-regions, then the multiples of that class realised in the box
region are realised in the halves.  (This is the case in which the trace circle inside the box —
rather than only its conjunction with the pinch — already survives to a half.) -/
theorem traceClassBound_of_traceClass_mem_halves {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {u : ℝ} {v : ℚ × ℚ} (hv0 : v ≠ 0)
    (hvT : v ∈ Work.SurgeryInvariance.WindingSpan P (planeTrace P c σ u))
    (hvH : v ∈ Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u)) :
    TraceClassBound P s c σ u :=
  Or.inr ⟨v, hv0, hvT,
    le_trans inf_le_right (Submodule.span_le.mpr (by simpa using hvH))⟩

theorem inf_span_singleton_eq_bot_of_notMem {W : Submodule ℚ (ℚ × ℚ)} {v : ℚ × ℚ}
    (hv : v ∉ W) : W ⊓ Submodule.span ℚ {v} = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro x ⟨hxW, hxv⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxv
  rw [← hc]
  by_cases hc0 : c = 0
  · simp [hc0]
  · exact absurd (by
      have hmem : c⁻¹ • (c • v) ∈ W := W.smul_mem c⁻¹ (hc ▸ hxW)
      rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at hmem) hv

/-- **The chapter's residual degenerates to the goal when the trace is contractible and the halves
are inessential.**  In that case `TraceMultipleRealisable` is equivalent to `W(box) ≠ ⊤` — i.e. to
the assertion that the invariant does not jump from `⊤` to `⊥` — because its second branch may use
*any* class outside the box region's span, realised by a loop of the trace or not.  The honest form
`TraceClassBound` in the same configuration is `W(box) ≤ W(halves)`
(`traceClassBound_iff_box_le_halves_of_traceSpan_bot` below). -/
theorem traceMultipleRealisable_iff_box_ne_top_of_traceSpan_bot {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hbot : Work.SurgeryInvariance.WindingSpan P (planeTrace P c σ u) = ⊥)
    (hhalves : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u) = ⊥) :
    TraceMultipleRealisable P s c σ u ↔
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≠ ⊤ := by
  constructor
  · intro h htop
    rcases h with hle | ⟨v, hv, _hL, hperp⟩
    · rw [hhalves] at hle
      have hb : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊥ :=
        le_antisymm hle bot_le
      rw [htop] at hb
      exact bot_ne_top hb.symm
    · have hmem : v ∈ Work.SurgeryInvariance.WindingSpan P
          (Work.BoxShrink.Core.boxRegion P s c σ) ⊓ Submodule.span ℚ {v} :=
        ⟨by rw [htop]; exact Submodule.mem_top, Submodule.mem_span_singleton_self v⟩
      have := hperp hmem
      rw [hhalves] at this
      exact hv (by simpa using this)
  · intro htop
    obtain ⟨v, -, hvmem⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr htop)
    have hv0 : v ≠ 0 := fun h => hvmem (h ▸ Submodule.zero_mem _)
    have hTL : TraceLine P c σ u (Submodule.span ℚ {v}) := by
      refine ⟨?_, ?_⟩
      · rw [finrank_span_singleton hv0]
      · intro k l hper
        have hmem := tracePeriod_mem_windingSpan hper
        rw [hbot] at hmem
        have h0 : ((k : ℚ), (l : ℚ)) = 0 := by simpa using hmem
        rw [h0]
        exact Submodule.zero_mem _
    refine Or.inr ⟨v, hv0,
      ⟨Submodule.span ℚ {v}, hTL, Submodule.mem_span_singleton_self v⟩, ?_⟩
    rw [inf_span_singleton_eq_bot_of_notMem hvmem, hhalves]

/-- **The honest residual in the contractible-trace case is the strong conclusion**: with
`W(trace) = ⊥` its second branch is impossible, so it asserts that the invariant does not drop at
all — which is what the pinch gives when the cutting plane meets the surface only in contractible
curves. -/
theorem traceClassBound_iff_box_le_halves_of_traceSpan_bot {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hbot : Work.SurgeryInvariance.WindingSpan P (planeTrace P c σ u) = ⊥) :
    TraceClassBound P s c σ u ↔
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≤
        Work.SurgeryInvariance.WindingSpan P
          (Work.BoxShrink.Core.upperRegion P s c σ u ∪
            Work.BoxShrink.Core.lowerRegion P s c σ u) := by
  constructor
  · rintro (hle | ⟨v, hv, hvT, _⟩)
    · exact hle
    · rw [hbot] at hvT
      exact (hv (by simpa using hvT)).elim
  · exact Or.inl

/-! ## The degenerate instances -/

/-- **If the box region carries no essential loop the residual holds trivially.** -/
theorem traceClassBound_of_windingSpan_bot {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊥) :
    TraceClassBound P s c σ u :=
  Or.inl (h ▸ bot_le)

/-- **If the cutting plane misses the surface inside the box the residual holds trivially**: the
box region *is* the union of the two half-regions. -/
theorem traceClassBound_of_sliceRegion_empty {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.BoxShrink.Core.sliceRegion P s c σ u = ∅) :
    TraceClassBound P s c σ u :=
  Or.inl (le_of_eq (by
    rw [Work.BoxShrink.Core.boxRegion_eq_union, h, Set.union_empty]))

end

end Work.BoxShrink.Pinch
