import Submission.Work.BoxShrink.PinchOff.PerpCases
import Submission.Work.BoxShrink.PinchOff.CompactSlice
import Submission.Work.BoxShrink.PinchOff.SliceCover
import Submission.Work.BoxShrink.Pinch.TraceClass

/-!
# The honest per-class residual, and the exact gap between it and the perpendicular one

`Perp.lean` states the residual with the trace class ranging over a *trace line*:
`∃ v ≠ 0, (∃ L, TraceLine … L ∧ v ∈ L) ∧ W(Ω) ⊓ ker (cross · v) ≤ W(Ω₊ ∪ Ω₋)`.  The parent chapter's
honest form instead lets the class range over the *winding span of the trace*
(`v ∈ W(planeTrace P c σ u)`), which is a class that always exists when the trace is essential and
which needs **no trace line at all**.  This module records:

* `tracePerpRealisable_iff_traceClassBound_of_traceLine` — **the two forms are the same statement**
  at every configuration which admits a trace line and whose trace carries a nonzero class: a trace
  line contains the whole trace span (`Work.BoxShrink.Pinch.windingSpan_planeTrace_le_of_traceLine`)
  and is at most one-dimensional, so all its nonzero classes are collinear
  (`span_singleton_eq_of_mem_of_finrank_le_one`);
* `traceHonestSlice_iff_traceClassBoundTame` — the honest residual of this chapter is the parent
  chapter's `TraceClassBoundTame`, verbatim (the same disjunction with the same class condition);
* `keyTame_of_traceHonestSlice` and `smoothHalfSTame_of_traceHonestSlice` — **the honest per-class
  residual gives the deliverable's tamed dimension bound *and* Pardon's Lemma 3 conclusion**,
  through the linear algebra of the intersection form
  (`Work.BoxShrink.Pinch.finrank_le_succ_of_inf_span_le`: a one-dimensional kernel can lose at most
  one dimension), with no trace line and no (K0) anywhere;
* the correction this implies: the perpendicular residual needs a trace line, and *the box-local
  form of (K0) is false* (a tangency of the cutting plane **outside** the box leaves a trace of rank
  two — `README.md` §11.2(A)); at such a configuration the perpendicular residual degenerates to
  `W(Ω) ≤ W(Ω₊ ∪ Ω₋)` (`tracePerpRealisable_iff_of_noTraceLine`).  The honest form has no such
  degeneration: at a rank-two trace `v` may be taken in `W(planeTrace) ∩ W(Ω₊ ∪ Ω₋)`, and the
  universal crossing-number statement behind it, `W(Ω) ⊓ (W(planeTrace))^⊥ ≤ W(Ω₊ ∪ Ω₋)`, is
  vacuous there.  This is why the requester's route should use the honest form (or the parent's
  `TraceClassBoundTame`) at configurations without a trace line, and why `TraceLineTamed` is named
  as an obligation in `PerpCases.lean`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-! ## The honest residual -/

/-- **The honest per-class residual**: at every transverse, tame configuration whose two cuts carry
no essential loop, either the box region does not drop to the halves, or a nonzero class *of the
trace* has all its multiples in the box region realised in the halves.  This is the parent chapter's
`Work.BoxShrink.Pinch.TraceClassBoundTame`, and unlike the perpendicular form it needs no trace
line. -/
def TraceHonestSlice : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → Work.BoxShrink.Pinch.TameSlice ψ s c σ u →
    ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ≤
        Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) ∨
      ∃ v : ℚ × ℚ, v ≠ 0 ∧
        v ∈ Work.SurgeryInvariance.WindingSpan (surface ψ)
          (Work.BoxShrink.Pinch.planeTrace (surface ψ) c σ u) ∧
        Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ⊓ Submodule.span ℚ {v} ≤
          Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)

/-- **The honest residual of this chapter *is* the parent chapter's `TraceClassBoundTame`.** -/
theorem traceHonestSlice_iff_traceClassBoundTame :
    TraceHonestSlice ↔ Work.BoxShrink.Pinch.TraceClassBoundTame := Iff.rfl

/-! ## The honest residual gives the deliverable -/

/-- **The honest per-class residual gives the tamed dimension bound** `KeyTame`: in the second case
the intersection with the line `ℚ v` lies in the halves, and a nonzero class can lose at most one
dimension. -/
theorem keyTame_of_traceHonestSlice (h : TraceHonestSlice) : KeyTame := by
  intro ψ s c σ u hT hTa hS hZ
  rcases h ψ s c σ u hT hTa hS hZ with hle | ⟨v, hv, _hvT, hperp⟩
  · exact Nat.le_add_right_of_le (Submodule.finrank_mono hle)
  · exact Work.BoxShrink.Pinch.finrank_le_succ_of_inf_span_le hv hperp

/-- **The honest per-class residual gives Pardon's Lemma 3 conclusion** for the smooth tori, given
the general position of the box-sphere trace. -/
theorem smoothHalfSTame_of_traceHonestSlice (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : TraceHonestSlice) : SmoothHalfSTame :=
  smoothHalfSTame_of_keyTame hnice (keyTame_of_traceHonestSlice h)

/-- The same, in the parent chapter's own name for the corrected residual. -/
theorem pushOffHalfTame_of_traceHonestSlice (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h : TraceHonestSlice) : Work.BoxShrink.Pinch.PushOffHalfTame :=
  smoothHalfSTame_of_traceHonestSlice hnice h

/-! ## The two forms of the residual compared -/

/-- **At a configuration with a trace line and an essential trace, the perpendicular residual and
the honest one are the same statement.**  The trace line contains the whole trace span
(`Work.BoxShrink.Pinch.windingSpan_planeTrace_le_of_traceLine`) and has dimension at most one, so
every nonzero class of the trace is collinear with the class on the line. -/
theorem tracePerpRealisable_iff_traceClassBound_of_traceLine
    (hL : ∃ L : Submodule ℚ (ℚ × ℚ), Work.BoxShrink.Pinch.TraceLine (surface ψ) c σ u L)
    (hb : Work.SurgeryInvariance.WindingSpan (surface ψ)
      (Work.BoxShrink.Pinch.planeTrace (surface ψ) c σ u) ≠ ⊥) :
    Work.BoxShrink.Pinch.TracePerpRealisable (surface ψ) s c σ u ↔
      Work.BoxShrink.Pinch.TraceClassBound (surface ψ) s c σ u := by
  obtain ⟨L, hLdef⟩ := hL
  constructor
  · rintro (hle | ⟨v, hv, ⟨L', hL', hvL'⟩, hperp⟩)
    · exact Or.inl hle
    · -- a nonzero class `w` of the trace lies on `L'`, hence is collinear with `v`
      obtain ⟨w, hwT, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
      have hwL' : w ∈ L' := Work.BoxShrink.Pinch.windingSpan_planeTrace_le_of_traceLine hL' hwT
      have hwv : Submodule.span ℚ {w} = Submodule.span ℚ {v} :=
        (span_singleton_eq_of_mem_of_finrank_le_one hwL' hw0 hL'.1).trans
          (span_singleton_eq_of_mem_of_finrank_le_one hvL' hv hL'.1).symm
      refine Or.inr ⟨w, hw0, hwT, ?_⟩
      rw [hwv]
      rwa [ker_crossLin_eq_span hv] at hperp
  · rintro (hle | ⟨v, hv, hvT, hperp⟩)
    · exact Or.inl hle
    · refine Or.inr ⟨v, hv, ⟨L, hLdef, ?_⟩, ?_⟩
      · exact Work.BoxShrink.Pinch.windingSpan_planeTrace_le_of_traceLine hLdef hvT
      · rw [ker_crossLin_eq_span hv]
        exact hperp


/-! ## The rank-two case of the honest residual is weak

At a configuration whose trace spans all of `H₁(T²;ℚ)`, the honest residual's second branch asks
only for a direction in which `W(Ω)` does not meet the halves: it holds unless `W(Ω) = ⊤` *and* the
halves are inessential, i.e. unless Pardon's Lemma 3 conclusion fails.  So at rank-two traces the
honest residual carries **no geometry beyond the dichotomy**, while the perpendicular residual (whose
trace line does not exist there) degenerates to the strong `W(Ω) ≤ W(Ω₊ ∪ Ω₋)`. -/

/-- **A direction avoiding `W(Ω)`** whenever `W(Ω) ≠ ⊤` and `W(planeTrace) = ⊤`. -/
theorem exists_span_singleton_inf_eq_bot_of_span_top
    (htop : Work.SurgeryInvariance.WindingSpan (surface ψ)
      (Work.BoxShrink.Pinch.planeTrace (surface ψ) c σ u) = ⊤)
    (hbox : Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) ≠ ⊥ ∨
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ≠ ⊤) :
    ∃ v : ℚ × ℚ, v ≠ 0 ∧
      v ∈ Work.SurgeryInvariance.WindingSpan (surface ψ)
        (Work.BoxShrink.Pinch.planeTrace (surface ψ) c σ u) ∧
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ⊓ Submodule.span ℚ {v} ≤
        Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) := by
  rcases hbox with hH | hB
  · obtain ⟨v, hvH, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hH
    refine ⟨v, hv0, by rw [htop]; exact Submodule.mem_top, ?_⟩
    exact le_trans inf_le_right (Submodule.span_le.mpr (by simpa using hvH))
  · obtain ⟨v, -, hvW⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hB)
    have hv0 : v ≠ 0 := fun h0 => hvW (h0 ▸ Submodule.zero_mem _)
    refine ⟨v, hv0, by rw [htop]; exact Submodule.mem_top, ?_⟩
    rw [Work.BoxShrink.Pinch.inf_span_singleton_eq_bot_of_notMem hvW]
    exact bot_le

/-- **The rank-two case of the honest residual.**  If the trace of the cutting plane spans `ℚ²` and
either the halves carry an essential loop or the box region does not span `ℚ²`, then the honest
residual holds at the configuration.  The only configuration left is the one in which the box region
spans everything and the halves do not — i.e. the one forbidden by Pardon's Lemma 3 conclusion. -/
theorem traceClassBound_of_traceSpan_top
    (htop : Work.SurgeryInvariance.WindingSpan (surface ψ)
      (Work.BoxShrink.Pinch.planeTrace (surface ψ) c σ u) = ⊤)
    (hbox : Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) ≠ ⊥ ∨
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ≠ ⊤) :
    Work.BoxShrink.Pinch.TraceClassBound (surface ψ) s c σ u :=
  Or.inr (exists_span_singleton_inf_eq_bot_of_span_top htop hbox)


/-! ## The geometric input of the finger move, in its cleanest form

The per-class finger move has a trivially sufficient condition which is exactly the geometric
content: *the class of the trace is realised by a loop of one of the two half-regions*.  Everything
that has to be proved about the pinch in the rank-one case is therefore a statement of the form
"a curve of the surface with the trace's class can be found inside a half" — and the analysis of the
geometry (`README.md` §20) shows the two ways to produce it: the **level curves of the cutting
plane** next to a trace component (they have the trace's class, since a regular level set and a
neighbouring one cobound a collar) and the **annulus between two homologous trace components** (whose
interior lies on one side of the plane, because the cutting plane's coordinate cannot change sign on
a connected set that misses the trace). -/

/-- **The finger move is free once the trace's class is realised in the halves.** -/
theorem tracePeriodBound_of_traceClass_mem_halves {k l : ℤ}
    (h : ((((k : ℚ)), ((l : ℚ))) : ℚ × ℚ) ∈
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ⊓
        Submodule.span ℚ {(((k : ℚ)), ((l : ℚ)))} ≤
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) :=
  le_trans inf_le_right (Submodule.span_le.mpr (by simpa using h))

/-- **The geometric obligation of the rank-one case, in its cleanest form**: the class of a nonzero
trace period is realised by a loop of the two half-regions.  By
`tracePeriodBound_of_traceClass_mem_halves` this *is* the per-class finger move, and by
`tracePerpRealisable_of_traceLine_periodBound` it gives the residual's second alternative.  The two
constructions that produce such a loop are the level curves of the cutting plane next to the trace
and the annulus between two homologous trace components (`README.md` §20.4). -/
def TraceClassInHalves : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (k l : ℤ),
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → Work.BoxShrink.Pinch.TameSlice ψ s c σ u →
    ¬ IsCompact (Sigma ψ s c σ u) →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    Work.BoxShrink.Pinch.TracePeriod (surface ψ) c σ u k l → (k, l) ≠ 0 →
    ((((k : ℚ)), ((l : ℚ))) : ℚ × ℚ) ∈
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)

/-- **The per-class finger move from the geometric obligation.** -/
theorem tracePeriodBoundNC_of_traceClassInHalves (h : TraceClassInHalves) : TracePeriodBoundNC :=
  fun ψ s c σ u k l _ hT hTa hnc hZ hp hne _hL =>
    tracePeriodBound_of_traceClass_mem_halves (h ψ s c σ u k l hT hTa hnc hZ hp hne)


/-! ## The honest residual as the parent chapter's two halves, and the deliverable from them

The parent chapter splits its honest residual `TraceClassBoundTame` into the case
`W(planeTrace) ≠ ⊥` (`Work.BoxShrink.Pinch.TraceClassBoundSpanNeBot`: every multiple of a *trace
class* realised in the box region is realised in the halves — the per-class finger move) and the
contractible-trace case `W(planeTrace) = ⊥` (`…SpanBot`, in which the residual is the strong
`W(Ω) ≤ W(Ω₊ ∪ Ω₋)`).  Since `TraceHonestSlice` *is* `TraceClassBoundTame`, the residual of this
chapter is exactly that pair, and proving the pair gives the deliverable. -/

/-- **The honest residual of this chapter from the parent chapter's two halves.** -/
theorem traceHonestSlice_of_spanNeBot_spanBot
    (h1 : Work.BoxShrink.Pinch.TraceClassBoundSpanNeBot)
    (h0 : Work.BoxShrink.Pinch.TraceClassBoundSpanBot) : TraceHonestSlice :=
  traceHonestSlice_iff_traceClassBoundTame.mpr
    (Work.BoxShrink.Pinch.traceClassBoundTame_of_spanNeBot_spanBot h1 h0)

/-- **Pardon's Lemma 3 for the smooth tori from the parent chapter's two halves**, given the general
position of the box-sphere trace. -/
theorem smoothHalfSTame_of_spanNeBot_spanBot (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h1 : Work.BoxShrink.Pinch.TraceClassBoundSpanNeBot)
    (h0 : Work.BoxShrink.Pinch.TraceClassBoundSpanBot) : SmoothHalfSTame :=
  smoothHalfSTame_of_traceHonestSlice hnice (traceHonestSlice_of_spanNeBot_spanBot h1 h0)

/-- The same in the parent chapter's name for the corrected field. -/
theorem pushOffHalfTame_of_spanNeBot_spanBot (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (h1 : Work.BoxShrink.Pinch.TraceClassBoundSpanNeBot)
    (h0 : Work.BoxShrink.Pinch.TraceClassBoundSpanBot) : Work.BoxShrink.Pinch.PushOffHalfTame :=
  smoothHalfSTame_of_spanNeBot_spanBot hnice h1 h0


/-! ## The honest per-class residual in the tamed setting, without the (false) span branch

In the *tamed* setting (a compact slice) the honest residual of this chapter follows from the
perpendicular one **without** the parent chapter's `TraceClassBoundSpanBot`: if the trace of the
cutting plane is contractible, the slice is a finite union of inessential circles (a compact slice is
a union of circles by `sliceCirclesOnly_of_isCompact`, and each of them is a loop of the slice, hence
inessential by `hZ`), so the peeling gives `W(Ω) = W(Ω ∖ Σ) = W(Ω₊ ∪ Ω₋)`
(`windingSpan_omega_eq_halves_of_trace_circles`); if the trace is essential then the trace line *is*
the span of the trace (`windingSpan_planeTrace_le_of_traceLine` plus one-dimensionality), so the
perpendicular alternative transfers verbatim.  This is the route recommended in `README.md` §23.4. -/

/-- **The honest per-class residual at a tame configuration**, from the residual itself — no
`TraceClassBoundSpanBot`, and no trace line hypothesis. -/
theorem traceClassBound_of_tameSlice (hT : Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (hTa : Work.BoxShrink.Pinch.TameSlice ψ s c σ u)
    (hZ : ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u)) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ≤
        Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) ∨
      ∃ v : ℚ × ℚ, v ≠ 0 ∧
        v ∈ Work.SurgeryInvariance.WindingSpan (surface ψ)
          (Work.BoxShrink.Pinch.planeTrace (surface ψ) c σ u) ∧
        Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ⊓ Submodule.span ℚ {v} ≤
          Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) := by
  have hc : IsCompact (Sigma ψ s c σ u) := isCompact_sliceRegion_of_tameSlice hTa
  rcases tracePerpRealisable_of_isCompact_slice hT hc hZ with hle | ⟨v, hv, ⟨L, hL, hvL⟩, hperp⟩
  · exact Or.inl hle
  · by_cases hbot : Work.SurgeryInvariance.WindingSpan (surface ψ)
        (Work.BoxShrink.Pinch.planeTrace (surface ψ) c σ u) = ⊥
    · -- the trace is contractible: the slice is a union of inessential circles and peels away
      refine Or.inl ?_
      rw [windingSpan_omega_eq_halves_of_trace_circles_holds hZ
        (sliceCirclesOnly_of_isCompact hT hc)]
    · -- the trace is essential: its line is its span, so the class lies on the trace
      have hle' : Work.SurgeryInvariance.WindingSpan (surface ψ)
          (Work.BoxShrink.Pinch.planeTrace (surface ψ) c σ u) ≤ L :=
        Work.BoxShrink.Pinch.windingSpan_planeTrace_le_of_traceLine hL
      have hsv : v ∈ Work.SurgeryInvariance.WindingSpan (surface ψ)
          (Work.BoxShrink.Pinch.planeTrace (surface ψ) c σ u) := by
        -- `v ∈ L` and `W(planeTrace) ≠ ⊥` with `finrank L ≤ 1` force `L = W(planeTrace)`
        obtain ⟨w, hwT, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
        have hwL : w ∈ L := hle' hwT
        have hsp : Submodule.span ℚ {w} = L :=
          span_singleton_eq_of_mem_of_finrank_le_one hwL hw0 hL.1
        have hsp' : Submodule.span ℚ {v} = L :=
          span_singleton_eq_of_mem_of_finrank_le_one hvL hv hL.1
        have hwW : Submodule.span ℚ {w} ≤ Work.SurgeryInvariance.WindingSpan (surface ψ)
            (Work.BoxShrink.Pinch.planeTrace (surface ψ) c σ u) :=
          Submodule.span_le.mpr (by simpa using hwT)
        have hvsp : v ∈ Submodule.span ℚ {w} := by
          rw [hsp, ← hsp']
          exact Submodule.mem_span_singleton_self v
        exact hwW hvsp
      exact Or.inr ⟨v, hv, hsv, by rwa [ker_crossLin_eq_span hv] at hperp⟩

/-- **The honest residual from the compact-slice theorem** (the tamed setting assumed for every
configuration). -/
theorem traceHonestSlice_of_tameSlice
    (htame : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TameSlice ψ s c σ u) : TraceHonestSlice :=
  fun ψ s c σ u hT _hTa _hS hZ => traceClassBound_of_tameSlice hT (htame ψ s c σ u) hZ

/-- **Pardon's Lemma 3 for the smooth tori from the tamed honest residual**, with no use of the
refuted span branch. -/
theorem smoothHalfSTame_of_tameSlice_honest (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (htame : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TameSlice ψ s c σ u) : SmoothHalfSTame :=
  smoothHalfSTame_of_traceHonestSlice hnice (traceHonestSlice_of_tameSlice htame)

end

end Work.BoxShrink.PinchOff
