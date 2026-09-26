import Submission.Work.BoxShrink.PinchOff.Basic
import Submission.Work.BoxShrink.PinchOff.Perp
import Submission.Work.BoxShrink.PinchOff.PerpCases
import Submission.Work.BoxShrink.Pinch.TraceClass
import Submission.Work.BoxShrink.PinchOff.TangentConfig

/-!
# The residual of the pinch, in linear-algebraic form: its exact failure condition

The parent chapter's honest residual `Work.BoxShrink.Pinch.TraceClassBound` is

> either `W(Ω) ≤ W(halves)`, or there is a *nonzero trace class* `v` — a nonzero vector of the
> winding span of the trace `F ∩ P` of the cutting plane — whose multiples realised in the box
> region are realised in the halves.

This module records the *exact* linear-algebraic content of that disjunction.  Writing

* `Wb` for `W(Ω)` (`BoxSpan`), `Wh` for `W(Ω₊ ∪ Ω₋)` (`HalvesSpan`) and `Wt` for `W(F ∩ P)`
  (`PlaneSpan`),

the second disjunct holds for a class `v ≠ 0` exactly when `v ∉ Wb` (the box region does not carry
`v`, so its perpendicular companion is free: `Wb ⊓ ℚv = ⊥`) **or** `v ∈ Wh` (the halves carry `v`
already, so `Wb ⊓ ℚv ≤ ℚv ≤ Wh`).  Consequently

  `TraceClassBound ↔ Wb ≤ Wh ∨ ¬ (Wt ≤ Wb) ∨ Wt ⊓ Wh ≠ ⊥`

and the residual **fails** exactly when the box region is not contained in the halves' span, it
contains the whole span of the trace, and the trace's span is disjoint from the halves':

  `¬ TraceClassBound ↔ ¬ (Wb ≤ Wh) ∧ Wt ≤ Wb ∧ Wt ⊓ Wh = ⊥`.

The usable consequences:

* `traceClassBound_of_trace_not_le` — the residual is free as soon as *one* trace class is not
  realised in the box region;
* `traceClassBound_of_trace_inf_ne_bot` — the residual is free as soon as *one* trace class is
  realised in the halves;
* `traceClassBound_of_le` — the residual is free when the box region does not drop;
* `not_traceClassBound_of_box_top_halves_bot` — **every** configuration with `W(Ω) = ⊤` and
  `W(Ω₊ ∪ Ω₋) = ⊥` refutes the residual, whatever the trace does;
* `traceClassBound_iff_of_traceSpan_bot` — when the trace's span vanishes the residual is exactly
  the span inclusion `W(Ω) ≤ W(halves)`.

The last point is the sharpest statement of what is missing: the residual can only fail when
`W(Ω)` is *not* contained in `W(halves)`, the trace's span is *contained* in `W(Ω)`, and the
trace's span is *disjoint* from `W(halves)`.  See `README.md` §27–28 for what this says about the
scanned families and about the box-local residual `TracePerpSliceBox` of this chapter.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)

/-! ## The three spans -/

/-- `Wb`: the winding span of the region of the surface inside the box. -/
def BoxSpan : Submodule ℚ (ℚ × ℚ) :=
  Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ)

/-- `Wh`: the winding span of the union of the two half-regions. -/
def HalvesSpan : Submodule ℚ (ℚ × ℚ) :=
  Work.SurgeryInvariance.WindingSpan P
    (Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u)

/-- `Wt`: the winding span of the trace of the cutting plane on the surface. -/
def PlaneSpan : Submodule ℚ (ℚ × ℚ) :=
  Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u)

/-! ## The intersection of a subspace with a line -/

/-- The intersection of a subspace with the line spanned by one of its elements is that line. -/
theorem inf_span_singleton_eq_of_mem {W : Submodule ℚ (ℚ × ℚ)} {v : ℚ × ℚ} (hv : v ∈ W) :
    W ⊓ Submodule.span ℚ {v} = Submodule.span ℚ {v} :=
  le_antisymm inf_le_right (le_inf (Submodule.span_singleton_le_iff_mem v W |>.mpr hv) le_rfl)

/-- **The perpendicular companion of a class is free exactly when the region does not carry it.**
For a subspace `W` and a class `v`, `W ⊓ ℚv ≤ Wh` holds if and only if `v ∉ W` (the intersection is
then `⊥`) or `v ∈ Wh` (the intersection is then `ℚv`, and `ℚv ≤ Wh`). -/
theorem inf_span_singleton_le_iff {W Wh : Submodule ℚ (ℚ × ℚ)} {v : ℚ × ℚ} :
    W ⊓ Submodule.span ℚ {v} ≤ Wh ↔ v ∉ W ∨ v ∈ Wh := by
  constructor
  · intro h
    by_cases hv : v ∈ W
    · refine Or.inr ?_
      rw [inf_span_singleton_eq_of_mem hv] at h
      exact Submodule.span_singleton_le_iff_mem v Wh |>.mp h
    · exact Or.inl hv
  · rintro (hv | hv)
    · rw [Work.BoxShrink.Pinch.inf_span_singleton_eq_bot_of_notMem hv]
      exact bot_le
    · exact le_trans inf_le_right (Submodule.span_singleton_le_iff_mem v Wh |>.mpr hv)

/-! ## The exact form of the residual -/

/-- **The residual `TraceClassBound`, in terms of the three spans.** -/
theorem traceClassBound_iff :
    Work.BoxShrink.Pinch.TraceClassBound P s c σ u ↔
      BoxSpan P s c σ ≤ HalvesSpan P s c σ u ∨
        ¬ (PlaneSpan P c σ u ≤ BoxSpan P s c σ) ∨
        PlaneSpan P c σ u ⊓ HalvesSpan P s c σ u ≠ ⊥ := by
  rw [Work.BoxShrink.Pinch.TraceClassBound]
  constructor
  · rintro (hle | ⟨v, hv0, hvT, hperp⟩)
    · exact Or.inl hle
    · rcases (inf_span_singleton_le_iff (W := BoxSpan P s c σ)
          (Wh := HalvesSpan P s c σ u)).mp hperp with h | h
      · exact Or.inr (Or.inl fun hle => h (hle hvT))
      · exact Or.inr (Or.inr fun hbot => hv0 (by
          have hv : v ∈ PlaneSpan P c σ u ⊓ HalvesSpan P s c σ u := ⟨hvT, h⟩
          rw [hbot] at hv
          exact hv))
  · rintro (hle | hnt | hinf)
    · exact Or.inl hle
    · obtain ⟨v, hvT, hvW⟩ := SetLike.not_le_iff_exists.mp hnt
      refine Or.inr ⟨v, fun h0 => hvW (h0 ▸ Submodule.zero_mem _), hvT, ?_⟩
      exact (inf_span_singleton_le_iff (W := BoxSpan P s c σ)
        (Wh := HalvesSpan P s c σ u)).mpr (Or.inl hvW)
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
      rw [Submodule.mem_inf] at hv
      refine Or.inr ⟨v, hv0, hv.1, ?_⟩
      exact (inf_span_singleton_le_iff (W := BoxSpan P s c σ)
        (Wh := HalvesSpan P s c σ u)).mpr (Or.inr hv.2)

/-- **The exact failure condition of the residual**: the box region's span is not contained in the
halves', the box region carries the whole span of the trace, and the trace's span meets the halves'
span trivially. -/
theorem not_traceClassBound_iff :
    ¬ Work.BoxShrink.Pinch.TraceClassBound P s c σ u ↔
      ¬ (BoxSpan P s c σ ≤ HalvesSpan P s c σ u) ∧
        PlaneSpan P c σ u ≤ BoxSpan P s c σ ∧
        PlaneSpan P c σ u ⊓ HalvesSpan P s c σ u = ⊥ := by
  rw [traceClassBound_iff P s c σ u]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · by_contra hle; exact h (Or.inl hle)
    · by_contra hnt; exact h (Or.inr (Or.inl hnt))
    · by_contra hne; exact h (Or.inr (Or.inr hne))
  · rintro ⟨h1, h2, h3⟩ (hle | hnt | hne)
    · exact h1 hle
    · exact hnt h2
    · exact hne h3

/-! ## The usable criteria -/

/-- **The residual is free when a trace class is not realised in the box region.** -/
theorem traceClassBound_of_trace_not_le (h : ¬ (PlaneSpan P c σ u ≤ BoxSpan P s c σ)) :
    Work.BoxShrink.Pinch.TraceClassBound P s c σ u :=
  (traceClassBound_iff P s c σ u).mpr (Or.inr (Or.inl h))

/-- **The residual is free when a trace class is realised in the halves.** -/
theorem traceClassBound_of_trace_inf_ne_bot (h : PlaneSpan P c σ u ⊓ HalvesSpan P s c σ u ≠ ⊥) :
    Work.BoxShrink.Pinch.TraceClassBound P s c σ u :=
  (traceClassBound_iff P s c σ u).mpr (Or.inr (Or.inr h))

/-- **The residual is free when the box region does not drop.** -/
theorem traceClassBound_of_le (h : BoxSpan P s c σ ≤ HalvesSpan P s c σ u) :
    Work.BoxShrink.Pinch.TraceClassBound P s c σ u :=
  (traceClassBound_iff P s c σ u).mpr (Or.inl h)

/-- **The dangerous shape is `Wb = ⊤`, `Wh = ⊥`.**  If the box region spans everything while the
halves span nothing, the residual fails — for *every* configuration of the trace. -/
theorem not_traceClassBound_of_box_top_halves_bot
    (hb : BoxSpan P s c σ = ⊤) (hh : HalvesSpan P s c σ u = ⊥) :
    ¬ Work.BoxShrink.Pinch.TraceClassBound P s c σ u := by
  rw [not_traceClassBound_iff P s c σ u]
  refine ⟨?_, ?_, ?_⟩
  · rw [hb, hh]
    intro h
    have h1 : ((1 : ℚ), (1 : ℚ)) ∈ (⊥ : Submodule ℚ (ℚ × ℚ)) := h Submodule.mem_top
    rw [Submodule.mem_bot] at h1
    exact one_ne_zero (Prod.ext_iff.mp h1).1
  · rw [hb]; exact le_top
  · rw [hh]; exact inf_bot_eq _

/-- **If the box region spans everything, the residual is exactly "the halves span everything, or a
trace class survives to the halves".** -/
theorem traceClassBound_iff_of_box_top (hb : BoxSpan P s c σ = ⊤) :
    Work.BoxShrink.Pinch.TraceClassBound P s c σ u ↔
      HalvesSpan P s c σ u = ⊤ ∨ PlaneSpan P c σ u ⊓ HalvesSpan P s c σ u ≠ ⊥ := by
  rw [traceClassBound_iff P s c σ u]
  constructor
  · rintro (hle | hnt | hinf)
    · exact Or.inl (top_le_iff.mp (hb ▸ hle))
    · rw [hb] at hnt
      exact absurd le_top hnt
    · exact Or.inr hinf
  · rintro (h | h)
    · exact Or.inl (h ▸ le_top)
    · exact Or.inr (Or.inr h)

/-- **If the trace spans everything**, the residual is the exclusion of the wall: unless the box
region spans everything, some trace class is not realised in it. -/
theorem traceClassBound_of_traceSpan_eq_top (ht : PlaneSpan P c σ u = ⊤)
    (h : ¬ (BoxSpan P s c σ = ⊤ ∧ HalvesSpan P s c σ u = ⊥)) :
    Work.BoxShrink.Pinch.TraceClassBound P s c σ u := by
  rw [traceClassBound_iff P s c σ u]
  by_cases hb : BoxSpan P s c σ = ⊤
  · refine Or.inr (Or.inr fun hbot => h ⟨hb, ?_⟩)
    rw [ht, top_inf_eq] at hbot
    exact hbot
  · exact Or.inr (Or.inl fun hle => hb (top_le_iff.mp (ht ▸ hle)))

/-- **The trace-inessential case**: when the trace's span vanishes, the residual is exactly the span
inclusion (`Work.BoxShrink.Pinch.traceClassBound_iff_box_le_halves_of_traceSpan_bot`, recovered). -/
theorem traceClassBound_iff_of_traceSpan_bot (ht : PlaneSpan P c σ u = ⊥) :
    Work.BoxShrink.Pinch.TraceClassBound P s c σ u ↔ BoxSpan P s c σ ≤ HalvesSpan P s c σ u := by
  rw [traceClassBound_iff P s c σ u]
  constructor
  · rintro (hle | hnt | hinf)
    · exact hle
    · rw [ht] at hnt
      exact absurd bot_le hnt
    · rw [ht] at hinf
      exact absurd (bot_inf_eq _) hinf
  · exact Or.inl

/-! ## The same analysis for the residual with the trace *line* (`TracePerpRealisable`) -/

/-- **`TracePerpRealisable`, in terms of the three spans and the trace lines.**  Since the kernel of
the crossing functional with `v` is the line `ℚv`, the second alternative holds for a class `v ≠ 0`
lying on *some* trace line exactly when `v` is not realised in the box region or is already realised
in the halves. -/
theorem tracePerpRealisable_iff :
    Work.BoxShrink.Pinch.TracePerpRealisable P s c σ u ↔
      BoxSpan P s c σ ≤ HalvesSpan P s c σ u ∨
        ∃ v : ℚ × ℚ, v ≠ 0 ∧
          (∃ L : Submodule ℚ (ℚ × ℚ), Work.BoxShrink.Pinch.TraceLine P c σ u L ∧ v ∈ L) ∧
          (v ∉ BoxSpan P s c σ ∨ v ∈ HalvesSpan P s c σ u) := by
  rw [Work.BoxShrink.Pinch.TracePerpRealisable]
  constructor
  · rintro (hle | ⟨v, hv0, hL, hperp⟩)
    · exact Or.inl hle
    · refine Or.inr ⟨v, hv0, hL, ?_⟩
      rw [ker_crossLin_eq_span hv0] at hperp
      exact (inf_span_singleton_le_iff (W := BoxSpan P s c σ)
        (Wh := HalvesSpan P s c σ u)).mp hperp
  · rintro (hle | ⟨v, hv0, hL, h | h⟩)
    · exact Or.inl hle
    · refine Or.inr ⟨v, hv0, hL, ?_⟩
      rw [ker_crossLin_eq_span hv0]
      exact (inf_span_singleton_le_iff (W := BoxSpan P s c σ)
        (Wh := HalvesSpan P s c σ u)).mpr (Or.inl h)
    · refine Or.inr ⟨v, hv0, hL, ?_⟩
      rw [ker_crossLin_eq_span hv0]
      exact (inf_span_singleton_le_iff (W := BoxSpan P s c σ)
        (Wh := HalvesSpan P s c σ u)).mpr (Or.inr h)

/-- **Without a nonzero trace period every line is a trace line**, so the second alternative may use
*any* class outside the box region: the residual is then exactly the exclusion of the wall. -/
theorem tracePerpRealisable_iff_of_noTracePeriod
    (hper : ∀ k l : ℤ, Work.BoxShrink.Pinch.TracePeriod P c σ u k l → (k, l) = 0) :
    Work.BoxShrink.Pinch.TracePerpRealisable P s c σ u ↔
      BoxSpan P s c σ ≠ ⊤ ∨ HalvesSpan P s c σ u ≠ ⊥ := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨hb, hh⟩ := hc
    rcases (tracePerpRealisable_iff P s c σ u).mp h with hle | ⟨v, hv0, hL, hmem⟩
    · have h1 : ((1 : ℚ), (1 : ℚ)) ∈ (⊥ : Submodule ℚ (ℚ × ℚ)) := by
        rw [← hh]
        exact hle (by rw [hb]; exact Submodule.mem_top)
      rw [Submodule.mem_bot] at h1
      exact one_ne_zero (Prod.ext_iff.mp h1).1
    · rcases hmem with h | h
      · exact h (by rw [hb]; exact Submodule.mem_top)
      · rw [hh] at h; exact hv0 h
  · rintro (h | h)
    · obtain ⟨v, -, hvW⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr h)
      have hv0 : v ≠ 0 := fun h0 => hvW (h0 ▸ Submodule.zero_mem _)
      have hTL : Work.BoxShrink.Pinch.TraceLine P c σ u (Submodule.span ℚ {v}) := by
        refine ⟨?_, ?_⟩
        · rw [finrank_span_singleton hv0]
        · intro k l hp
          obtain ⟨hk, hl⟩ : k = 0 ∧ l = 0 := Prod.ext_iff.mp (hper k l hp)
          rw [hk, hl]
          exact Submodule.zero_mem _
      exact (tracePerpRealisable_iff P s c σ u).mpr (Or.inr ⟨v, hv0,
        ⟨Submodule.span ℚ {v}, hTL, Submodule.mem_span_singleton_self v⟩, Or.inl hvW⟩)
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      have hTL : Work.BoxShrink.Pinch.TraceLine P c σ u (Submodule.span ℚ {v}) := by
        refine ⟨?_, ?_⟩
        · rw [finrank_span_singleton hv0]
        · intro k l hp
          obtain ⟨hk, hl⟩ : k = 0 ∧ l = 0 := Prod.ext_iff.mp (hper k l hp)
          rw [hk, hl]
          exact Submodule.zero_mem _
      exact (tracePerpRealisable_iff P s c σ u).mpr (Or.inr ⟨v, hv0,
        ⟨Submodule.span ℚ {v}, hTL, Submodule.mem_span_singleton_self v⟩, Or.inr hv⟩)

/-! ## The box-local residual of this chapter -/

/-- **The failure shape of any residual of this form.**  If a region's span is `⊤` and the halves'
span is `⊥`, then *no* choice of a trace subspace `Lt` makes the disjunction
`Wb ≤ Wh ∨ ¬ (Lt ≤ Wb) ∨ Lt ⊓ Wh ≠ ⊥` true: this is the shape
`not_traceClassBound_of_box_top_halves_bot` isolates, in the abstract form the chapter's
`TracePerpSliceBox` also has (with `Lt` the span of the classes of the trace curves meeting the
box). -/
theorem failure_shape {Wb Wh Lt : Submodule ℚ (ℚ × ℚ)} (hb : Wb = ⊤) (hh : Wh = ⊥) :
    ¬ (Wb ≤ Wh ∨ ¬ (Lt ≤ Wb) ∨ Lt ⊓ Wh ≠ ⊥) := by
  rintro (h | h | h)
  · have h1 : ((1 : ℚ), (1 : ℚ)) ∈ (⊥ : Submodule ℚ (ℚ × ℚ)) := by
      rw [← hh]
      exact h (by rw [hb]; exact Submodule.mem_top)
    rw [Submodule.mem_bot] at h1
    exact one_ne_zero (Prod.ext_iff.mp h1).1
  · exact h (by rw [hb]; exact le_top)
  · rw [hh] at h
    exact h (inf_bot_eq _)

/-! ## The form in which the residual should be *proved* -/

/-- **The per-class bound plus the inessential-trace dichotomy give the residual.**  This is the
"what to prove" form of `traceClassBound_iff`: if (i) every nonzero trace class carried by the box
region is carried by the halves, and (ii) when the trace's span vanishes the box region does not
drop, then the residual holds.  The two hypotheses are exactly the two named obligations of the
chapter (`TracePeriodBound`, `TraceInessentialHalfOrDrop`), read at the level of the spans rather
than at the level of the families of curves. -/
theorem traceClassBound_of_perClass
    (hdich : PlaneSpan P c σ u = ⊥ → BoxSpan P s c σ ≤ HalvesSpan P s c σ u)
    (hper : ∀ v : ℚ × ℚ, v ≠ 0 → v ∈ PlaneSpan P c σ u → v ∈ BoxSpan P s c σ →
      v ∈ HalvesSpan P s c σ u) :
    Work.BoxShrink.Pinch.TraceClassBound P s c σ u := by
  rw [traceClassBound_iff P s c σ u]
  by_cases ht : PlaneSpan P c σ u = ⊥
  · exact Or.inl (hdich ht)
  · by_cases hnt : PlaneSpan P c σ u ≤ BoxSpan P s c σ
    · refine Or.inr (Or.inr fun hbot => ?_)
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ht
      exact hv0 (by
        have : v ∈ PlaneSpan P c σ u ⊓ HalvesSpan P s c σ u := ⟨hv, hper v hv0 hv (hnt hv)⟩
        rw [hbot] at this
        exact this)
    · exact Or.inr (Or.inl hnt)

/-! ## A concrete instance: the tangent configuration refutes the residual -/

/-- **The residual `TraceClassBound` fails at the tangent configuration** (`KeyRefuted.lean`): the
box region spans everything while the halves span nothing, so §27's criterion
`not_traceClassBound_of_box_top_halves_bot` applies.  This is the machine-checked instance that
makes the criterion concrete; it is *not* affected by the correction of §28, because at the tangent
configuration the cutting plane is not transverse. -/
theorem not_traceClassBound_tangent :
    ¬ Work.BoxShrink.Pinch.TraceClassBound Work.CoreTopology.standard tangentRad tangentCtr
      tangentCyc3 0 :=
  not_traceClassBound_of_box_top_halves_bot _ _ _ _ _
    (by rw [BoxSpan, tangent_boxRegion_span_eq_top])
    (by rw [HalvesSpan]; exact tangent_halfRegions_span_eq_bot)

/-! ## The mechanism of the per-class bound

The evidence of `README.md` §30.3 is that the residual's failure condition cannot be realised
because of two facts about loops of the box region and the trace:

* a **trace** curve lying in the box region has trivial class — it is a loop of the slice, whose
  span is `⊥` by `hZ` (`zzClass_eq_zero_of_subset_slice`);
* a loop that avoids the cutting plane is already a loop of the halves (`mem_halvesSpan_of_avoid`).

The two together say: a loop of the box region whose class is "parallel to the trace" must either be
the trace itself (class `0`), or avoid the trace — which is the per-class bound in the form in which
it should be attacked. -/

/-- **A trace curve inside the box region has trivial class.**  Its image lies in the slice `Σ`
(`Σ = Ω ∩ {G = 0}`), and `hZ` (`W(Σ) = ⊥`) says that the slice realises no class: so
`zzClass γ = 0`.  In particular, under `hZ` every nonzero trace class carried by the box region is
carried by a trace curve that *leaves* the box. -/
theorem zzClass_eq_zero_of_subset_slice {γ : Work.CoreTopology.ClosedCurve P}
    (hmem : ∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.sliceRegion P s c σ u)
    (hZ : BoxSpan P s c σ = ⊥) : zzClass (P := P) γ = 0 := by
  have h : zzClass (P := P) γ ∈ BoxSpan P s c σ :=
    Submodule.subset_span ⟨γ, fun t => ⟨(hmem t).1.1, (hmem t).1.2⟩, rfl⟩
  rw [hZ] at h
  exact h

/-- **A loop of the box region that avoids the cutting plane is a loop of the halves.**  (`Ω₊ ∪ Ω₋`
is `Ω` minus the slice, so this is the definition of the halves read backwards.) -/
theorem mem_halvesSpan_of_avoid {γ : Work.CoreTopology.ClosedCurve P}
    (hmem : ∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.boxRegion P s c σ)
    (havoid : ∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.upperHalf c σ u ∨
      γ t ∈ Work.BoxShrink.Core.lowerHalf c σ u) :
    zzClass (P := P) γ ∈ HalvesSpan P s c σ u := by
  refine Submodule.subset_span ⟨γ, ?_, rfl⟩
  intro t
  rcases havoid t with h | h
  · exact Or.inl ⟨hmem t, h⟩
  · exact Or.inr ⟨hmem t, h⟩

end

end Work.BoxShrink.PinchOff
