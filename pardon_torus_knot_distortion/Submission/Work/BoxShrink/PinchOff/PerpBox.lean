import Submission.Work.BoxShrink.PinchOff.Perp
import Submission.Work.BoxShrink.PinchOff.windingSpan_sdiff_iUnion_range_eq_of_not_isEssential
import Submission.Work.BoxShrink.PinchOff.OpenArcs

/-!
# The residual in the box-local trace form, and its decomposition

`Perp.lean` states the residual of the pinch in the parent chapter's factored form
`Work.BoxShrink.Pinch.TracePerpRealisable`, whose second alternative is tied to the parent's
**global** trace line `TraceLine`: a statement about *all* periods of the trace of the cutting
plane, outside the box included.  The proof of that global form
(`Work.BoxShrink.Pinch.TraceSpanLeOneSmoothHolds`) carries the **global** transversality hypothesis
`TransverseTrace`, which is refuted for all configurations
(`Work.BoxShrink.PinchOff.not_forall_transverseTrace`); so the global line is not available
box-locally, and this module replaces it by the *box-local* line:

* the trace components that **meet the box** are pairwise disjoint, hence — by the disjointness form
  of (K0), `exists_collinear_windingOf_of_pairwise_disjoint` — their winding classes span a line of
  dimension at most one (`exists_traceLine_of_pairwise_disjoint`).  This needs neither
  transversality outside the box nor any Sard input.

The residual is then stated as `TracePerpSliceBox`: the same statement as `TracePerpSlice`, with the
second alternative tied to a *trace curve meeting the box* instead of to the global line.  It
implies the tamed dimension bound `KeyTame` (`keyTame_of_tracePerpSliceBox`) and hence, with the
general position of the box-sphere trace, the corrected residual `SmoothHalfSTame`
(`smoothHalfSTame_of_tracePerpSliceBox`), and through the parent chapter the abstract residual
`SmoothHalfS` (`smoothHalfS_of_tracePerpSliceBox`).

## The decomposition, and what is left

The module records the statements whose conjunction implies `TracePerpSliceBox`, i.e. the honest
decomposition of the remaining geometry:

* `TraceParallelSurvives` — **Claim R**: a class realised in the box region which is *parallel to the
  trace* (a rational multiple of the class of a trace curve meeting the box) is realised in the two
  half-regions.  By the linear algebra of the intersection form (`ker_crossLin_le_span`) this is
  exactly the second alternative for that trace curve, so it is the whole content of the residual in
  the case in which the trace meeting the box is **essential**
  (`tracePerpSliceBox_of_parallelSurvives`);
* the **inessential-trace** case, recorded as the hypothesis `hnoEss` of the same theorem: if every
  trace curve meeting the box is inessential then the box region does not drop to the halves.  The
  naive expectation that this case is "peeling" is **false**: removing the pieces of a *contractible*
  curve from a region can drop its winding span (an annulus cut along a chord, which is part of the
  boundary circle of a small disc, becomes a disc), so the box geometry is needed here too.  The
  *sound* partial case is `tracePerpSliceBox_of_peeling`, where the trace inside the box is covered
  by inessential simple closed curves *contained* in the box region: then the family peeling
  `windingSpan_sdiff_iUnion_range_eq_of_not_isEssential` applies verbatim and the box region does
  not drop.

**CORRECTION (`README.md` §28).**  The claim of an earlier stretch that the *residual itself* is
false at a transverse configuration does not stand: the "rotation witness" of §26 has an **essential**
trace (`Correction.lean`, `rotation_trace_essential`), and the residual's conclusion actually *holds*
there (`rotation_witness_not_refutation`).  `TraceParallelSurvives` and `hnoEss` are only
*sufficient* conditions for the residual (`tracePerpSliceBox_of_parallelSurvives`), so refuting one
of them does not refute it.  By `SpanSplit.lean` (`not_traceClassBound_iff`) the residual fails only
at the exact triple `¬ (W(Ω) ≤ W(halves)) ∧ Wt ≤ W(Ω) ∧ Wt ⊓ W(halves) = ⊥`, where `Wt` is the span
of the trace; no such configuration is known.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}

/-! ## Trace curves -/

/-- **The trace of the cutting plane on the surface**: the intersection of the surface with the flat
plane `{y (σ 2) = c (σ 2) + u}`.  Its connected components are the *trace curves*; the slice `Sigma`
is the part of the trace inside the box. -/
def PlaneTrace (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Set R3 :=
  (surface ψ).carrier ∩ Work.BoxShrink.Core.cutPlane c σ u

/-- **A trace curve**: a closed curve of the surface lying in the trace of the cutting plane. -/
def IsTraceCurve (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (γ : Work.CoreTopology.ClosedCurve (surface ψ)) : Prop :=
  ∀ t : ℝ, γ t ∈ PlaneTrace ψ c σ u

/-- The trace of the cutting plane is the zero set of the plane coordinate on the surface. -/
theorem mem_PlaneTrace_iff (x : R3) :
    x ∈ PlaneTrace ψ c σ u ↔ x ∈ (surface ψ).carrier ∧ x (σ 2) = c (σ 2) + u :=
  Iff.rfl

/-- A point of a trace curve lies on the surface. -/
theorem IsTraceCurve.mem_carrier {γ : Work.CoreTopology.ClosedCurve (surface ψ)}
    (h : IsTraceCurve ψ c σ u γ) (t : ℝ) :
    γ t ∈ (surface ψ).carrier :=
  (h t).1

/-- A point of a trace curve lies in the cutting plane. -/
theorem IsTraceCurve.mem_plane {γ : Work.CoreTopology.ClosedCurve (surface ψ)}
    (h : IsTraceCurve ψ c σ u γ) (t : ℝ) :
    γ t (σ 2) = c (σ 2) + u :=
  (h t).2

/-- **The slice is contained in the trace.** -/
theorem Sigma_subset_PlaneTrace :
    Sigma ψ s c σ u ⊆ PlaneTrace ψ c σ u := by
  intro x hx
  exact ⟨hx.1.1, hx.2⟩

/-- A closed curve of the slice is a trace curve. -/
theorem isTraceCurve_of_slice {γ : Work.CoreTopology.ClosedCurve (surface ψ)}
    (h : ∀ t : ℝ, γ t ∈ Sigma ψ s c σ u) : IsTraceCurve ψ c σ u γ :=
  fun t => Sigma_subset_PlaneTrace (h t)

/-! ## (K0) for the trace components meeting the box -/

/-- **(K0) box-locally**: the classes of pairwise disjoint trace curves span a line of dimension at
most one.  The trace components meeting the box are pairwise disjoint (they are distinct components
of a `1`-manifold), so their classes are collinear — this is Pardon's (K0) for the components that
matter, with no transversality outside the box. -/
theorem exists_traceLine_of_pairwise_disjoint {n : ℕ}
    (γ : Fin n → Work.CoreTopology.ClosedCurve (surface ψ))
    (hdisj : Pairwise fun i j => Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ)) :
    ∃ L : Submodule ℚ (ℚ × ℚ), Module.finrank ℚ ↥L ≤ 1 ∧
      ∀ i, zzClass (P := surface ψ) (γ i) ∈ L :=
  exists_collinear_windingOf_of_pairwise_disjoint (surface ψ) γ hdisj

/-- The class of an essential curve is nonzero. -/
theorem zzClass_ne_zero_of_isEssential {γ : Work.CoreTopology.ClosedCurve (surface ψ)}
    (h : Work.CoreTopology.IsEssential (surface ψ) γ) : zzClass (P := surface ψ) γ ≠ 0 := by
  intro hzero
  have hz : zzClass (P := surface ψ) γ =
      zzCast (Work.SurgeryInvariance.windingOf (surface ψ) γ) := rfl
  rw [hz] at hzero
  have hw : Work.SurgeryInvariance.windingOf (surface ψ) γ = 0 :=
    (Work.SurgeryInvariance.intPair_cast_eq_zero_iff _).mp hzero
  exact (Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero (surface ψ) γ).mp h hw

/-! ## The box region with the slice removed is the union of the two half-regions -/

/-- **`Ω` with the slice removed is the union of the two half-regions**: the box region is the union
of the two half-regions and the slice (`Work.BoxShrink.Core.boxRegion_eq_union`), and the slice is
disjoint from each half-region. -/
theorem Omega_sdiff_Sigma : Omega ψ s c σ \ Sigma ψ s c σ u = Halves ψ s c σ u := by
  ext y
  constructor
  · intro hy
    rw [Set.mem_sdiff] at hy
    obtain ⟨h1, h2⟩ := hy
    rw [show Omega ψ s c σ = Work.BoxShrink.Core.boxRegion (surface ψ) s c σ from rfl,
      Work.BoxShrink.Core.boxRegion_eq_union (surface ψ) s c σ u, Set.mem_union] at h1
    rw [show Sigma ψ s c σ u = Work.BoxShrink.Core.sliceRegion (surface ψ) s c σ u from rfl] at h2
    rw [show Halves ψ s c σ u = (Work.BoxShrink.Core.upperRegion (surface ψ) s c σ u ∪
        Work.BoxShrink.Core.lowerRegion (surface ψ) s c σ u) from rfl]
    rcases h1 with h | h
    · exact h
    · exact absurd h h2
  · intro hy
    rw [show Halves ψ s c σ u = (Work.BoxShrink.Core.upperRegion (surface ψ) s c σ u ∪
        Work.BoxShrink.Core.lowerRegion (surface ψ) s c σ u) from rfl, Set.mem_union] at hy
    rw [Set.mem_sdiff,
      show Omega ψ s c σ = Work.BoxShrink.Core.boxRegion (surface ψ) s c σ from rfl,
      Work.BoxShrink.Core.boxRegion_eq_union (surface ψ) s c σ u, Set.mem_union,
      show Sigma ψ s c σ u = Work.BoxShrink.Core.sliceRegion (surface ψ) s c σ u from rfl]
    rcases hy with h | h
    · exact ⟨Or.inl (Or.inl h), fun hz => absurd hz.2 (ne_of_gt h.2)⟩
    · exact ⟨Or.inl (Or.inr h), fun hz => absurd hz.2 (ne_of_lt h.2)⟩

/-! ## The residual in box-local trace form -/

/-- **The residual of the pinch in box-local trace form.**  For every smooth torus, every box and
every plane whose slice is transverse (`TransverseSlice`) and **honestly tame**
(`TameClosedSlice`, i.e. the pieces of the trace are arcs and circles covering the closure of the
slice — the ends of the arcs lie on the box sphere, so the slice need *not* be compact) and whose
slice carries no essential loop, either the box region does not drop to the two half-regions at all, or
there is a finite family of pairwise disjoint trace curves, each meeting the box, and a *nonzero*
class `v` in the span of their classes, every class of the box region perpendicular to `v` being
already realised in the two half-regions.

This is the parent's `TracePerpRealisable` with the global trace line replaced by the box-local one
and with the vacuous tameness `TameSlice` (which forces the slice to be compact, see `OpenArcs.lean`)
replaced by the honest `TameClosedSlice`; it is the interface the deliverable needs (through
`KeyTame`), it carries no false hypothesis, and it is *not* vacuous at the arcs configurations. -/
def TracePerpSliceBox : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
    TameClosedSlice ψ s c σ u →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ≤
        Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) ∨
      ∃ (v : ℚ × ℚ) (n : ℕ) (γ : Fin n → Work.CoreTopology.ClosedCurve (surface ψ)),
        v ≠ 0 ∧
        (∀ i, IsTraceCurve ψ c σ u (γ i)) ∧
        (∀ i, ∃ t : ℝ, γ i t ∈ Omega ψ s c σ) ∧
        (Pairwise fun i j => Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ)) ∧
        v ∈ Submodule.span ℚ (Set.range fun i => zzClass (P := surface ψ) (γ i)) ∧
        Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ⊓
            LinearMap.ker (Work.BoxShrink.Pinch.crossLin v) ≤
          Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)

/-- **The box-local residual gives the tamed dimension bound.**  In the first alternative the bound
is monotonicity of the dimension; in the second it is the linear algebra of the intersection form on
`ℚ² = H₁(T²;ℚ)`: the kernel of the nonzero functional `cross · v` is one-dimensional
(`Work.BoxShrink.Pinch.finrank_le_succ_of_inf_ker_le`). -/
theorem keyTame_of_tracePerpSliceBox
    (hhon : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TameSlice ψ s c σ u → TameClosedSlice ψ s c σ u)
    (h : TracePerpSliceBox) : KeyTame := by
  intro ψ s c σ u hT hTame hS hZ
  rcases h ψ s c σ u hT (hhon ψ s c σ u hTame) hZ with hle | ⟨v, n, γ, hv, _hγ, _hmeet, _hdisj, _hspan, hperp⟩
  · exact Nat.le_add_right_of_le (Submodule.finrank_mono hle)
  · exact Work.BoxShrink.Pinch.finrank_le_succ_of_inf_ker_le hv hperp

/-- **The box-local residual gives the corrected residual of the chapter** (`SmoothHalfSTame` = the
parent's `PushOffHalfTame`), given the general position of the box-sphere trace (`BoxSliceNice`). -/
theorem smoothHalfSTame_of_tracePerpSliceBox (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hhon : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TameSlice ψ s c σ u → TameClosedSlice ψ s c σ u)
    (h : TracePerpSliceBox) : SmoothHalfSTame :=
  smoothHalfSTame_of_keyTame hnice (keyTame_of_tracePerpSliceBox hhon h)

/-- The same, in the parent chapter's own name. -/
theorem pushOffHalfTame_of_tracePerpSliceBox (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hhon : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TameSlice ψ s c σ u → TameClosedSlice ψ s c σ u)
    (h : TracePerpSliceBox) : Work.BoxShrink.Pinch.PushOffHalfTame :=
  smoothHalfSTame_of_tracePerpSliceBox hnice hhon h

/-- **End to end**: the box-local residual, Pardon's equation (1) (discharged in `Dichotomy.lean`)
and the general position of the box-sphere trace give Pardon's Lemma 3 for the smooth tori of the
challenge under the two endpoint hypotheses. -/
theorem smoothHalfS_of_tracePerpSliceBox (hnice : Work.BoxShrink.Pinch.BoxSliceNice)
    (hhon : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TameSlice ψ s c σ u → TameClosedSlice ψ s c σ u)
    (h : TracePerpSliceBox)
    (htrans : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u)
    (htame : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TameSlice ψ s c σ u) :
    Work.BoxShrink.Pinch.SmoothHalfS :=
  Work.BoxShrink.Pinch.smoothHalfS_of_pushOffHalfTame
    (pushOffHalfTame_of_tracePerpSliceBox hnice hhon h) htrans htame

/-! ## Instances of the residual -/

/-- **The residual holds whenever the box region does not drop to the halves.** -/
theorem tracePerpSliceBox_of_span_le
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ≤
        Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)) : TracePerpSliceBox :=
  fun ψ s c σ u _ _ _ => Or.inl (h ψ s c σ u)

/-- **The peeling case**: if at every configuration the trace inside the box is covered by finitely
many pairwise disjoint simple *inessential* closed curves *contained in the box region*, then the box
region does not drop to the halves — the family peeling
`windingSpan_sdiff_iUnion_range_eq_of_not_isEssential` removes them without changing the winding
span.

This is the sound general form of the "the slice is a union of inessential circles lying in the
box" case (`Work.BoxShrink.PinchOff.Laminar`/`CirclesCase` and the disc-covering statements of
`Discs.lean` are instances): the curves need not be the trace curves themselves, only a covering of
the slice by inessential loops of the region. -/
theorem tracePerpSliceBox_of_peeling
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
      TameClosedSlice ψ s c σ u →
      ∃ (n : ℕ) (γ : Fin n → Work.CoreTopology.ClosedCurve (surface ψ)),
        (∀ i, Work.CoreTopology.IsSimple (surface ψ) (γ i)) ∧
        (∀ i, ¬ Work.CoreTopology.IsEssential (surface ψ) (γ i)) ∧
        (∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ)) ∧
        (∀ (i : Fin n) (t : ℝ), γ i t ∈ Omega ψ s c σ) ∧
        (Sigma ψ s c σ u ⊆ ⋃ i, Set.range (γ i).γ)) : TracePerpSliceBox := by
  intro ψ s c σ u hT hTame _
  obtain ⟨n, γ, hsimple, hiness, hdisj, hsub, hcov⟩ := h ψ s c σ u hT hTame
  refine Or.inl ?_
  have hpeel := windingSpan_sdiff_iUnion_range_eq_of_not_isEssential (P := surface ψ)
    (X := Omega ψ s c σ) (γ := γ)
    (Work.BoxShrink.Core.isOpenInCarrier_boxRegion (surface ψ) s c σ)
    hsimple hiness hdisj hsub
  rw [hpeel]
  refine Work.SurgeryInvariance.WindingSpan_mono (surface ψ) ?_
  refine fun x hx => ?_
  rw [← Omega_sdiff_Sigma (ψ := ψ) (s := s) (c := c) (σ := σ) (u := u)]
  exact ⟨hx.1, fun hxS => hx.2 (hcov hxS)⟩

/-! ## The decomposition of the residual -/

/-- **Claim R**: a class of the box region which is *parallel to the trace* survives to the two
half-regions.  Equivalently: a loop of the box region whose winding class is a rational multiple of
the class of a trace curve meeting the box is homotopic, inside the box, to a loop on one side of the
cutting plane.

This is the whole content of the residual in the case in which the trace meeting the box is
essential; it is *not* refuted, and by `ker_crossLin_le_span` it is exactly the second alternative
of `TracePerpRealisable` at such a curve. -/
def TraceParallelSurvives : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
    TameClosedSlice ψ s c σ u →
    ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
    ∀ γ : Work.CoreTopology.ClosedCurve (surface ψ),
      IsTraceCurve ψ c σ u γ → (∃ t : ℝ, γ t ∈ Omega ψ s c σ) →
      Work.CoreTopology.IsEssential (surface ψ) γ →
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ⊓
          Submodule.span ℚ {zzClass (P := surface ψ) γ} ≤
        Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)

/-- **The residual decomposes into Claim R and the inessential-trace case.**  Given

* `hR` — Claim R (`TraceParallelSurvives`);
* `htrace` — at every configuration, a finite pairwise disjoint family of trace curves, each meeting
  the box, which contains an essential member as soon as the trace meeting the box has one;
* `hnoEss` — the box region does not drop when every trace curve meeting the box is inessential;

the box-local residual holds. -/
theorem tracePerpSliceBox_of_parallelSurvives (hR : TraceParallelSurvives)
    (htrace : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
      TameClosedSlice ψ s c σ u →
      ∃ (n : ℕ) (γ : Fin n → Work.CoreTopology.ClosedCurve (surface ψ)),
        (∀ i, IsTraceCurve ψ c σ u (γ i)) ∧
        (∀ i, ∃ t : ℝ, γ i t ∈ Omega ψ s c σ) ∧
        (Pairwise fun i j => Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ)) ∧
        ((∃ γ' : Work.CoreTopology.ClosedCurve (surface ψ),
            IsTraceCurve ψ c σ u γ' ∧ (∃ t : ℝ, γ' t ∈ Omega ψ s c σ) ∧
            Work.CoreTopology.IsEssential (surface ψ) γ') →
          ∃ i, Work.CoreTopology.IsEssential (surface ψ) (γ i)))
    (hnoEss : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u →
      TameClosedSlice ψ s c σ u →
      ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
      (∀ γ : Work.CoreTopology.ClosedCurve (surface ψ), IsTraceCurve ψ c σ u γ →
        (∃ t : ℝ, γ t ∈ Omega ψ s c σ) → ¬ Work.CoreTopology.IsEssential (surface ψ) γ) →
      Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) ≤
        Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u)) :
    TracePerpSliceBox := by
  intro ψ s c σ u hT hTame hZ
  by_cases hE : ∃ γ' : Work.CoreTopology.ClosedCurve (surface ψ),
      IsTraceCurve ψ c σ u γ' ∧ (∃ t : ℝ, γ' t ∈ Omega ψ s c σ) ∧
      Work.CoreTopology.IsEssential (surface ψ) γ'
  · obtain ⟨n, γ, htr, hmeet, hdisj, hsome⟩ := htrace ψ s c σ u hT hTame
    obtain ⟨i₀, hi₀⟩ := hsome hE
    refine Or.inr ⟨zzClass (P := surface ψ) (γ i₀), n, γ, ?_, htr, hmeet, hdisj, ?_, ?_⟩
    · exact zzClass_ne_zero_of_isEssential hi₀
    · exact Submodule.subset_span ⟨i₀, rfl⟩
    · refine le_trans (inf_le_inf_left _
        (ker_crossLin_le_span (zzClass_ne_zero_of_isEssential hi₀))) ?_
      exact hR ψ s c σ u hT hTame hZ (γ i₀) (htr i₀) (hmeet i₀) hi₀
  · exact Or.inl (hnoEss ψ s c σ u hT hTame hZ
      (fun γ hγ hmeet hess => hE ⟨γ, hγ, hmeet, hess⟩))

end

end Work.BoxShrink.PinchOff
