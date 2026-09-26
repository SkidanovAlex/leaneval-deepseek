import Submission.Work.BoxShrink.PinchOff.Perp
import Submission.Work.BoxShrink.Pinch.TraceClass

/-!
# The perpendicular residual: exact case analysis, and the reduction to three named obligations

`Perp.lean` states the box-local residual `TracePerpSlice`: for every smooth configuration with a
transverse, tame slice carrying no essential loop, the parent chapter's factored form
`Work.BoxShrink.Pinch.TracePerpRealisable` holds, i.e.

  `W(Ω) ≤ W(Ω₊ ∪ Ω₋)`, or else some nonzero `v` on a *trace line* `L` has
  `W(Ω) ⊓ ker (cross · v) ≤ W(Ω₊ ∪ Ω₋)`.

This module makes the second alternative completely explicit.  The point is the elementary linear
algebra of the intersection form: for `v ≠ 0` the kernel of `cross · v` *is* the line `ℚ v`
(`ker_crossLin_eq_span`), and a line containing a nonzero trace period is *forced* to be the span of
that period (`traceLine_eq_span_of_tracePeriod`), because a trace line has dimension at most one.
Hence

* `tracePerpRealisable_of_traceLine_periodBound` / `traceLine_periodBound_of_tracePerpRealisable` —
  at a configuration whose trace has a nonzero period `(k,l)` and which admits a trace line, the
  second alternative is *equivalent* to the single per-class bound
  `W(Ω) ⊓ ℚ (k,l) ≤ W(Ω₊ ∪ Ω₋)`: the existential quantifiers over the trace class `v` and over the
  trace line disappear, and the identity of the trace class does not matter (any trace line works);
* `tracePerpRealisable_of_noTracePeriod_of_halves_ne_bot` and
  `tracePerpRealisable_of_noTracePeriod_of_box_ne_top` — at a configuration whose trace has *no*
  nonzero period every line is a trace line (`traceLine_span_of_noTracePeriod`), so the second
  alternative is witnessed by *any* nonzero class of the halves, and by any class outside `W(Ω)`
  (which exists as soon as `W(Ω) ≠ ⊤`).

Assembling, the residual is *exactly* the conjunction of three named obligations
(`tracePerpSlice_of_traceLine_periodBound_discharge`):

* `TraceLineTamed` — Pardon's (K0) under the box-local transversality: there is a trace line at
  every transverse, tame configuration.  This *is* needed by the residual, and the parent chapter's
  (K0) supplies it only under the global `TransverseTrace`, which is refuted for every configuration
  (`NotTransverse.lean`, `not_forall_transverseTrace`); naming it separates an obligation about the
  cutting plane from the geometric content of the pinch;
* `TracePeriodBound` — the per-class finger move: every multiple of the trace's class realised in
  the box region is realised in the halves.  This is the parent chapter's `TraceClassBoundSpanNeBot`
  (`tracePeriodBound_of_traceClassBound`), and it is where the crossing analysis has to enter;
* `TraceInessentialHalfOrDrop` — the dichotomy in the inessential-trace case: either the box region
  does not drop to the halves, or the halves carry an essential loop.  This is Pardon's Lemma 3
  restricted to the configurations whose trace is contractible, and its *second* disjunct is the one
  the residual's second alternative needs (`tracePerpRealisable_of_noTracePeriod_of_halves_ne_bot`),
  so no geometry enters here at all.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-! ## The linear algebra of the intersection form -/

/-- **A nonzero element of a subspace of dimension at most one spans it.**  In
`H₁(T²;ℚ) = ℚ²` this is the statement that two nonzero classes in a line are collinear. -/
theorem span_singleton_eq_of_mem_of_finrank_le_one {L : Submodule ℚ (ℚ × ℚ)} {v : ℚ × ℚ}
    (hv : v ∈ L) (hv0 : v ≠ 0) (hL : Module.finrank ℚ ↥L ≤ 1) :
    Submodule.span ℚ {v} = L := by
  refine Submodule.eq_of_le_of_finrank_le (Submodule.span_singleton_le_iff_mem v L |>.mpr hv) ?_
  rw [finrank_span_singleton hv0]
  exact hL

/-- **The kernel of the crossing functional with a nonzero class is the line spanned by it** (the
intersection form on `ℚ²` is symplectic, so the orthogonal companion of a line is that line). -/
theorem ker_crossLin_eq_span {v : ℚ × ℚ} (hv : v ≠ 0) :
    LinearMap.ker (Work.BoxShrink.Pinch.crossLin v) = Submodule.span ℚ {v} := by
  refine le_antisymm (ker_crossLin_le_span hv) ?_
  rw [Submodule.span_singleton_le_iff_mem v (LinearMap.ker (Work.BoxShrink.Pinch.crossLin v))]
  exact LinearMap.mem_ker.mpr (by simpa using Work.BoxShrink.Pinch.cross_self v)

/-- The cast of an integer pair of windings is nonzero as soon as the pair is. -/
theorem intPair_cast_ne_zero {k l : ℤ} (h : (k, l) ≠ 0) :
    ((((k : ℚ)), ((l : ℚ))) : ℚ × ℚ) ≠ 0 :=
  fun h0 => h (Work.SurgeryInvariance.intPair_cast_eq_zero_iff (k, l) |>.mp h0)

/-- **A trace line containing a nonzero trace period is the span of that period.** -/
theorem traceLine_eq_span_of_tracePeriod {L : Submodule ℚ (ℚ × ℚ)} {k l : ℤ}
    (hL : Work.BoxShrink.Pinch.TraceLine (surface ψ) c σ u L)
    (hp : Work.BoxShrink.Pinch.TracePeriod (surface ψ) c σ u k l) (hne : (k, l) ≠ 0) :
    L = Submodule.span ℚ {(((k : ℚ)), ((l : ℚ)))} :=
  (span_singleton_eq_of_mem_of_finrank_le_one (hL.2 k l hp) (intPair_cast_ne_zero hne) hL.1).symm

/-! ## The second alternative, per trace period -/

/-- **The per-class form of the second alternative.**  If `L` is a trace line and `(k,l) ≠ 0` is a
trace period, then the per-class bound `W(Ω) ⊓ ℚ (k,l) ≤ W(Ω₊ ∪ Ω₋)` gives the second alternative
of `TracePerpRealisable`, with `v` the period itself and the line `L`. -/
theorem tracePerpRealisable_of_traceLine_periodBound {k l : ℤ} {L : Submodule ℚ (ℚ × ℚ)}
    (hL : Work.BoxShrink.Pinch.TraceLine (surface ψ) c σ u L)
    (hp : Work.BoxShrink.Pinch.TracePeriod (surface ψ) c σ u k l) (hne : (k, l) ≠ 0)
    (h : Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ⊓
        Submodule.span ℚ {(((k : ℚ)), ((l : ℚ)))} ≤
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)) :
    Work.BoxShrink.Pinch.TracePerpRealisable (surface ψ) s c σ u := by
  refine Or.inr ⟨(((k : ℚ)), ((l : ℚ))), intPair_cast_ne_zero hne, ⟨L, hL, hL.2 k l hp⟩, ?_⟩
  rwa [ker_crossLin_eq_span (intPair_cast_ne_zero hne)]

/-- **The converse**: at a configuration whose trace has a nonzero period and which admits a trace
line, the second alternative can only hold in the per-class form along that period.  With the
previous theorem this is an equivalence, and it removes the existential quantifiers over the trace
class and the trace line from the residual. -/
theorem traceLine_periodBound_of_tracePerpRealisable {k l : ℤ}
    (hp : Work.BoxShrink.Pinch.TracePeriod (surface ψ) c σ u k l) (hne : (k, l) ≠ 0)
    (h : Work.BoxShrink.Pinch.TracePerpRealisable (surface ψ) s c σ u) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ≤
        Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) ∨
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ⊓
          Submodule.span ℚ {(((k : ℚ)), ((l : ℚ)))} ≤
        Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) := by
  rcases h with hle | ⟨v, hv, ⟨L', hL', hvL'⟩, hperp⟩
  · exact Or.inl hle
  · right
    have hL'sp : L' = Submodule.span ℚ {(((k : ℚ)), ((l : ℚ)))} :=
      traceLine_eq_span_of_tracePeriod hL' hp hne
    have hvL : v ∈ Submodule.span ℚ {(((k : ℚ)), ((l : ℚ)))} := by
      have := hvL'; rwa [hL'sp] at this
    have hfin : Module.finrank ℚ ↥(Submodule.span ℚ {(((k : ℚ)), ((l : ℚ)))}) ≤ 1 := by
      rw [finrank_span_singleton (intPair_cast_ne_zero hne)]
    have hvv : Submodule.span ℚ {v} = Submodule.span ℚ {(((k : ℚ)), ((l : ℚ)))} :=
      span_singleton_eq_of_mem_of_finrank_le_one hvL hv hfin
    rw [← hvv, ← ker_crossLin_eq_span hv]
    exact hperp

/-! ## The inessential-trace case: every line is a trace line -/

/-- **Every line is a trace line when the trace has no nonzero period.** -/
theorem traceLine_span_of_noTracePeriod {v : ℚ × ℚ} (hv : v ≠ 0)
    (h : ∀ k l : ℤ, Work.BoxShrink.Pinch.TracePeriod (surface ψ) c σ u k l → (k, l) = 0) :
    Work.BoxShrink.Pinch.TraceLine (surface ψ) c σ u (Submodule.span ℚ {v}) := by
  refine ⟨?_, ?_⟩
  · rw [finrank_span_singleton hv]
  · intro k l hper
    have h0 : (((k : ℚ)), ((l : ℚ))) = 0 :=
      (Work.SurgeryInvariance.intPair_cast_eq_zero_iff (k, l)).mpr (h k l hper)
    rw [h0]
    exact Submodule.zero_mem _

/-- **In the inessential-trace case the second alternative is witnessed by any nonzero class of the
halves**: the halves' span is contained in every line through one of its classes. -/
theorem tracePerpRealisable_of_noTracePeriod_of_halves_ne_bot
    (h : ∀ k l : ℤ, Work.BoxShrink.Pinch.TracePeriod (surface ψ) c σ u k l → (k, l) = 0)
    (hH : Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) ≠ ⊥) :
    Work.BoxShrink.Pinch.TracePerpRealisable (surface ψ) s c σ u := by
  obtain ⟨v, hvH, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hH
  refine Or.inr ⟨v, hv0, ⟨Submodule.span ℚ {v}, traceLine_span_of_noTracePeriod hv0 h,
    Submodule.mem_span_singleton_self v⟩, ?_⟩
  rw [ker_crossLin_eq_span hv0]
  exact le_trans inf_le_right (Submodule.span_le.mpr (by simpa using hvH))

/-- **In the inessential-trace case the second alternative is witnessed by any class outside the box
region's span**, which exists as soon as `W(Ω) ≠ ⊤`. -/
theorem tracePerpRealisable_of_noTracePeriod_of_box_ne_top
    (h : ∀ k l : ℤ, Work.BoxShrink.Pinch.TracePeriod (surface ψ) c σ u k l → (k, l) = 0)
    (hbox : Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ≠ ⊤) :
    Work.BoxShrink.Pinch.TracePerpRealisable (surface ψ) s c σ u := by
  obtain ⟨v, -, hvW⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hbox)
  have hv0 : v ≠ 0 := fun h0 => hvW (h0 ▸ Submodule.zero_mem _)
  refine Or.inr ⟨v, hv0, ⟨Submodule.span ℚ {v}, traceLine_span_of_noTracePeriod hv0 h,
    Submodule.mem_span_singleton_self v⟩, ?_⟩
  rw [ker_crossLin_eq_span hv0, Work.BoxShrink.Pinch.inf_span_singleton_eq_bot_of_notMem hvW]
  exact bot_le

/-! ## The three named obligations, and the reduction -/

/-- **(K0) under the box-local transversality.**  A trace line exists at every transverse, tame
configuration of the challenge.  The parent chapter proves this under the *global* transversality of
the cutting plane (`Work.BoxShrink.Pinch.traceLineSmooth_holds`, from `TransverseTrace`), which is
refuted for every configuration; the box-local form needed by `TracePerpSlice` is this statement. -/
def TraceLineTamed : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → Work.BoxShrink.Pinch.TameSlice ψ s c σ u →
    ∃ L : Submodule ℚ (ℚ × ℚ), Work.BoxShrink.Pinch.TraceLine (surface ψ) c σ u L

/-- **The per-class finger move**: at every transverse, tame configuration, every multiple of the
trace's class realised in the box region is realised in the two half-regions.  This is the content
of the residual which is *not* about the dichotomy, and it is the parent chapter's
`Work.BoxShrink.Pinch.TraceClassBoundSpanNeBot` (`tracePeriodBound_of_traceClassBound`). -/
def TracePeriodBound : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (k l : ℤ)
    (L : Submodule ℚ (ℚ × ℚ)),
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → Work.BoxShrink.Pinch.TameSlice ψ s c σ u →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    Work.BoxShrink.Pinch.TracePeriod (surface ψ) c σ u k l → (k, l) ≠ 0 →
    Work.BoxShrink.Pinch.TraceLine (surface ψ) c σ u L →
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ⊓
        Submodule.span ℚ {(((k : ℚ)), ((l : ℚ)))} ≤
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)

/-- **The dichotomy in the inessential-trace case**: either the box region does not drop to the
halves, or the halves carry an essential loop.  No geometry enters: the residual's second
alternative is satisfied by a nonzero class of the halves alone
(`tracePerpRealisable_of_noTracePeriod_of_halves_ne_bot`). -/
def TraceInessentialHalfOrDrop : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → Work.BoxShrink.Pinch.TameSlice ψ s c σ u →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    (∀ k l : ℤ, Work.BoxShrink.Pinch.TracePeriod (surface ψ) c σ u k l → (k, l) = 0) →
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ≤
        Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) ∨
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) ≠ ⊥

/-- **The residual, from its three named parts.**  This is the exact case analysis of the second
alternative: with a nonzero trace period the trace line is forced and the residual is the per-class
bound; without one, every line is a trace line and the residual is the dichotomy. -/
theorem tracePerpSlice_of_traceLine_periodBound_discharge (h0 : TraceLineTamed)
    (hA : TracePeriodBound) (hB : TraceInessentialHalfOrDrop) : TracePerpSlice := by
  intro ψ s c σ u hT hTa hZ
  by_cases hper : ∃ k l : ℤ,
    Work.BoxShrink.Pinch.TracePeriod (surface ψ) c σ u k l ∧ (k, l) ≠ 0
  · obtain ⟨k, l, hp, hne⟩ := hper
    obtain ⟨L, hL⟩ := h0 ψ s c σ u hT hTa
    exact tracePerpRealisable_of_traceLine_periodBound hL hp hne
      (hA ψ s c σ u k l L hT hTa hZ hp hne hL)
  · push Not at hper
    rcases hB ψ s c σ u hT hTa hZ hper with hle | hne
    · exact Or.inl hle
    · exact tracePerpRealisable_of_noTracePeriod_of_halves_ne_bot hper hne

/-- **The corrected residual from the three named parts**, by the chain of `Perp.lean`
(`smoothHalfSTame_of_tracePerpSlice`). -/
theorem smoothHalfSTame_of_traceLine_periodBound_discharge
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice) (h0 : TraceLineTamed) (hA : TracePeriodBound)
    (hB : TraceInessentialHalfOrDrop) : SmoothHalfSTame :=
  smoothHalfSTame_of_tracePerpSlice hnice
    (tracePerpSlice_of_traceLine_periodBound_discharge h0 hA hB)

/-- The same, in the parent chapter's own name for the corrected residual. -/
theorem pushOffHalfTame_of_traceLine_periodBound_discharge
    (hnice : Work.BoxShrink.Pinch.BoxSliceNice) (h0 : TraceLineTamed) (hA : TracePeriodBound)
    (hB : TraceInessentialHalfOrDrop) : Work.BoxShrink.Pinch.PushOffHalfTame :=
  smoothHalfSTame_of_traceLine_periodBound_discharge hnice h0 hA hB

/-- **The dichotomy is implied by Pardon's Lemma 3 conclusion** in the inessential-trace case: if
the box region's span is not contained in the halves', then it is nonzero, and the conclusion of
Pardon's Lemma 3 at the configuration gives a nonzero class of the halves. -/
theorem traceInessentialHalfOrDrop_of_bubbleHalf
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → Work.BoxShrink.Pinch.TameSlice ψ s c σ u →
      Work.BoxShrink.Bubble.BubbleHalf (surface ψ) s c σ u) :
    TraceInessentialHalfOrDrop := by
  intro ψ s c σ u hT hTa _hZ _
  by_cases hle : Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ≤
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)
  · exact Or.inl hle
  · refine Or.inr fun hbot => ?_
    have hcon : ¬ (surface ψ).ContainsEssentialLoop (Halves ψ s c σ u) :=
      (Work.SurgeryInvariance.WindingSpan_eq_bot_iff _ _).mp hbot
    have hbox : (surface ψ).ContainsEssentialLoop (Omega ψ s c σ) := by
      by_contra hc
      exact hle (by
        rw [(Work.SurgeryInvariance.WindingSpan_eq_bot_iff _ _).mpr hc]
        exact bot_le)
    rcases h ψ s c σ u hT hTa hbox with hup | hlo
    · exact hcon ((surface ψ).containsEssentialLoop_mono Set.subset_union_left hup)
    · exact hcon ((surface ψ).containsEssentialLoop_mono Set.subset_union_right hlo)

/-- **The per-class bound from the parent chapter's honest residual.**  At a configuration for which
a trace line exists, the chapter's residual `TraceClassBound` — whose second branch is the same
per-class bound but for a class of the *trace* rather than for the period itself — implies
`TracePeriodBound` at that configuration: by
`Work.BoxShrink.Pinch.windingSpan_planeTrace_le_of_traceLine` the trace's classes all lie on the
trace line, hence are collinear with the period. -/
theorem tracePeriodBound_of_traceClassBound {k l : ℤ} {L : Submodule ℚ (ℚ × ℚ)}
    (h : Work.BoxShrink.Pinch.TraceClassBound (surface ψ) s c σ u)
    (hL : Work.BoxShrink.Pinch.TraceLine (surface ψ) c σ u L)
    (hp : Work.BoxShrink.Pinch.TracePeriod (surface ψ) c σ u k l) (hne : (k, l) ≠ 0) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ⊓
        Submodule.span ℚ {(((k : ℚ)), ((l : ℚ)))} ≤
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) := by
  have hk : ((((k : ℚ)), ((l : ℚ))) : ℚ × ℚ) ∈ L := hL.2 k l hp
  rcases h with hle | ⟨v, hv0, hvT, hperp⟩
  · exact le_trans inf_le_left hle
  · have hTv : v ∈ Work.SurgeryInvariance.WindingSpan (surface ψ)
        (Work.BoxShrink.Pinch.planeTrace (surface ψ) c σ u) := hvT
    have hvL : v ∈ L :=
      Work.BoxShrink.Pinch.windingSpan_planeTrace_le_of_traceLine hL hTv
    have hvsp : Submodule.span ℚ {v} = Submodule.span ℚ {(((k : ℚ)), ((l : ℚ)))} := by
      rw [span_singleton_eq_of_mem_of_finrank_le_one hvL hv0 hL.1,
        span_singleton_eq_of_mem_of_finrank_le_one hk (intPair_cast_ne_zero hne) hL.1]
    rw [← hvsp]
    exact hperp


/-! ## Inhabited cases of the three obligations

The obligations are not vacuous, and each of them is *proved* in the situations the chapter can
reach.  In particular the inessential-trace case of (K0) is free: the bottom subspace is a trace
line whenever the trace has no nonzero period. -/

/-- **The inessential-trace case of (K0) is free** (`⊥` is a trace line when there is no nonzero
trace period).  So the obligation `TraceLineTamed` is only about the configurations whose trace
carries a nonzero period. -/
theorem exists_traceLine_of_noTracePeriod
    (h : ∀ k l : ℤ, Work.BoxShrink.Pinch.TracePeriod (surface ψ) c σ u k l → (k, l) = 0) :
    ∃ L : Submodule ℚ (ℚ × ℚ), Work.BoxShrink.Pinch.TraceLine (surface ψ) c σ u L := by
  refine ⟨⊥, ?_, ?_⟩
  · simp
  · intro k l hper
    have h0 : (((k : ℚ)), ((l : ℚ))) = 0 :=
      (Work.SurgeryInvariance.intPair_cast_eq_zero_iff (k, l)).mpr (h k l hper)
    rw [h0]
    exact Submodule.zero_mem _

/-- **The per-class bound is vacuous when the trace's class is not realised in the box region.** -/
theorem tracePeriodBound_of_period_notMem {k l : ℤ} {L : Submodule ℚ (ℚ × ℚ)}
    (h : ((((k : ℚ)), ((l : ℚ))) : ℚ × ℚ) ∉
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ)) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ⊓
        Submodule.span ℚ {(((k : ℚ)), ((l : ℚ)))} ≤
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) := by
  rw [Work.BoxShrink.Pinch.inf_span_singleton_eq_bot_of_notMem h]
  exact bot_le

/-- **The per-class bound is vacuous when the box region does not drop to the halves.** -/
theorem tracePeriodBound_of_le {k l : ℤ} {L : Submodule ℚ (ℚ × ℚ)}
    (h : Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ≤
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)) :
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ⊓
        Submodule.span ℚ {(((k : ℚ)), ((l : ℚ)))} ≤
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) :=
  le_trans inf_le_left h

/-- **The residual in the case in which the trace never carries a period**, with no (K0) obligation
left: the trace line is `⊥` at every configuration (`exists_traceLine_of_noTracePeriod`). -/
theorem tracePerpSlice_of_periodBound_discharge_noTrace (hA : TracePeriodBound)
    (hB : TraceInessentialHalfOrDrop)
    (h0 : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → Work.BoxShrink.Pinch.TameSlice ψ s c σ u →
      ∀ k l : ℤ, Work.BoxShrink.Pinch.TracePeriod (surface ψ) c σ u k l → (k, l) = 0) :
    TracePerpSlice :=
  tracePerpSlice_of_traceLine_periodBound_discharge
    (fun ψ s c σ u hT hTa => exists_traceLine_of_noTracePeriod (h0 ψ s c σ u hT hTa)) hA hB


/-- **When no trace line exists, the residual degenerates to the first alternative.**  The second
alternative of `TracePerpRealisable` asks for a nonzero class *on a trace line*; if the trace of the
cutting plane carries two independent classes there is no such line, and the residual is exactly
`W(Ω) ≤ W(Ω₊ ∪ Ω₋)`.  This is why the obligation `TraceLineTamed` is not cosmetic, and why at such a
configuration the honest per-class form of the parent chapter (`Work.BoxShrink.Pinch.TraceClassBound`,
whose class ranges over the *trace's* span rather than over a line) is the weaker statement. -/
theorem tracePerpRealisable_iff_of_noTraceLine
    (h : ¬ ∃ L : Submodule ℚ (ℚ × ℚ), Work.BoxShrink.Pinch.TraceLine (surface ψ) c σ u L) :
    Work.BoxShrink.Pinch.TracePerpRealisable (surface ψ) s c σ u ↔
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ≤
        Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) := by
  constructor
  · rintro (hle | ⟨v, _hv, ⟨L, hL, _⟩, _⟩)
    · exact hle
    · exact absurd ⟨L, hL⟩ h
  · exact Or.inl

end

end Work.BoxShrink.PinchOff
