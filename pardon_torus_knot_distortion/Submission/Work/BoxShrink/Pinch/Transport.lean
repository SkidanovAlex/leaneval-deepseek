import Submission.Work.BoxShrink.Pinch.PushOffNoJump
import Submission.Work.BoxShrink.Pinch.TraceClass
import Submission.Work.BoxShrink.Bubble.HalfDefs
import Submission.Work.BoxShrink.Pinch.HalfSplit
import Submission.Work.InnermostDisk.not_isEssential_of_const
import Submission.Work.BoxShrink.Bubble.Plane.FiniteSlice
import Submission.Work.BoxShrink.Bubble.Plane.CountableSlice
import Submission.Work.BoxShrink.Bubble.Instances.slicePushOff_of_empty_slice

/-!
# The push-off in loop-transport form, and the family it generates

This module states Pardon's push-off in the form in which his own proof produces it — as the
*transport of loops* from the region inside the box to the union of the two half-regions, with the
winding vector preserved — and proves that this form:

* gives the chapter's residual `Work.BoxShrink.Pinch.TraceClassBound` (the realised winding vectors
  of the two regions coincide, so in particular the span of the box region is contained in that of
  the halves);
* generates Pardon's pinching family `Work.BoxShrink.Bubble.PinchDatum`: the two-region family
  `{boxRegion, upperRegion ∪ lowerRegion}` is a `SweepLoopsSmall` whose exceptional parameter is the
  pinching parameter `1`, whose exceptional step *is* the transport, and whose dichotomy at every
  parameter before `1` is Pardon's equation (1) at the box sphere.  Consequently
  `Work.BoxShrink.Bubble.bubbleHalf_of_pinchDatum` applies, and the deliverable
  `Work.BoxShrink.Pinch.PushOffHalfTame` follows from the transport form together with the two
  classical inputs (`Equation1Input`, `BoxSliceNice`).

The point of the second item is that it identifies *exactly* what has to be proved: the whole
residual of the area is the single loop-transport statement `RegionTransport` below, and no
surgery/dichotomy/counting hypothesis is left over.  In particular the transport form is *not* a
`surgery step` of the library: at the pinching parameter the region loses the closed slice, which is
not the interior of a disc, so `SurgeryStepSmall` does not apply; the loop-level relation
`RegionEquivalent` does, and that is why this interface is the right one for Pardon's last step.

## A caveat on the *strength* of the transport form, and on the span-based residuals

The transport form is a per-loop statement: it asks that *every* loop of the box region be matched
by a loop of the halves with the same winding vector.  `regionTransport_iff_slicePushOff` shows that
this is exactly the parent chapter's `Work.BoxShrink.Bubble.SlicePushOff`; restricted to the case in
which the trace of the cutting plane is inessential it is the case in which Pardon's pinch is a
trivial `2`-surgery, and it is not refuted by any configuration of this chapter, but its *truth* is
not established here.

It is worth recording where the difficulty is sharpest, because it also bears on the span-based
residuals of `TraceClass.lean` (`TraceClassBoundSpanBot`, `PinchNoJump`).  In the parameter plane a
loop of the box region is a period of `Ω = {B < s}` and the halves are `Ω ∖ {G = 0}`.  For a slice
made of *compact* curves the period can be routed around them (each component is a compact obstacle
inside the open set `Ω`, so it has a neighbourhood in `Ω`), but for a slice made of **arcs** whose
endpoints lie on `∂Ω = {B = s}` the route has to go around an endpoint on the boundary of `Ω`, and
the plane-level model permits a "wall" of such arcs (each component compact, hence realising no
period, so `hZ` holds) which separates `Ω` into cells that realise none.  What rules this out in the
box/plane geometry is the convexity of Pardon's box: the trace `∂Ω` is cut out by a *convex* body,
and the caps it cuts off the surface lie on one side of the box.  Making that precise — or finding a
configuration in which it fails — is the sharpest form of what is still missing, and it decides
whether the span-based residuals are true as stated or have to be replaced by the weaker
`BubbleHalf` (which is all the challenge consumes).

## The three routes into `TraceClassBound`

The module records three sufficient conditions for the residual, in increasing order of weakness:

* `RegionTransport` — the loop-transport form (Pardon's push-off);
* the *homotopy* form (`traceClassBound_of_homotopic_transport`) — every loop of the box region is
  homotopic in the torus to a loop of the halves; this is what a flow/isotopy argument naturally
  produces, and it suffices by `Work.BoxShrink.Pinch.windingSpan_le_of_homotopic_split`;
* the degenerate instances (`traceClassBound_of_regionTransport`,
  `regionTransport_of_boxRegion_subset_disc`, `regionTransport_of_halves_eq_boxRegion`).

## Conventions

`Work.SurgeryInvariance.RegionEquivalent P X Y` is the loop-level relation: every closed curve of
`F` in `X` is matched by one in `Y` with the same winding vector, and conversely.  Note the order of
the arguments: `RegionTransport P s c σ u` is
`RegionEquivalent P (upperRegion ∪ lowerRegion) (boxRegion)`, whose *first* conjunct is the
interesting one (loops of the box region are transported to the halves) and whose second is the
trivial inclusion `upperRegion ∪ lowerRegion ⊆ boxRegion`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.Pinch

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## The transport form -/

/-- **The push-off in the loop-transport form.**  Every loop of the region inside the box is
transported to a loop of the union of the two half-regions with the same winding vector (and
conversely, the halves being a subset of the box region).  This is Pardon's push-off at the level of
`H₁`-information inside the regions; it is what his pinching family *would* produce.

**WARNING — the transport form is refuted, and so is the span inequality it implies.**  It is
exactly the parent chapter's `SlicePushOff` (`regionTransport_iff_slicePushOff`), and
`Work.BoxShrink.Pinch.not_windingSpan_le_halves_standard` (`RefuteSpan.lean`) proves unconditionally
that at the standard torus of revolution with `σ = swap 1 2`, `s = 9/5`, `u = 0` the region inside
the box realises `(1,0)` (the inner equator) while *every* winding vector realised in either
half-region has vanishing first coordinate (a point of a half-region has `y = (2+cos φ) sin θ ≠ 0`,
so the longitude parameter of the lift of one of its loops never leaves a window of length `π`).
Hence `¬ RegionTransport standard (9/5) 0 (swap 1 2) 0`
(`not_regionTransport_standard`), and the *span* inequality `W(boxRegion) ≤ W(halves)` — session 5's
`TraceClassBoundSpanBot` and the first alternative of `TraceClassBound` — is false in the
box/plane geometry.  The numerical study in `EXP/` shows the same failure also with the *plane*
trace inessential (a sheared torus with `s ≈ 1.6`), so the restriction `W(planeTrace) = ⊥` below is
not enough either; the residual has to be the weaker `+1` dimension bound
(`Work.BoxShrink.Pinch.PinchNoJump`) or the conclusion `BubbleHalf` itself, both of which hold in
every sampled configuration (and in the refuted ones: `2 ≤ 1 + 1`).  The definitions and the
conditional theorems below are kept because `pinchDatum_of_regionTransport` shows exactly *how* a
per-loop push-off would generate Pardon's pinching family, but the hypothesis has to be replaced by
something weaker. -/
def RegionTransport (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) : Prop :=
  Work.SurgeryInvariance.RegionEquivalent P
    (Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u)
    (Work.BoxShrink.Core.boxRegion P s c σ)

/-- **The transport form restricted to the configurations whose trace of the cutting plane is
inessential** — Pardon's trivially-pinching case (`W(planeTrace) = ⊥`).

The restriction is *essential*: by `regionTransport_iff_slicePushOff` below the transport form is
equivalent to `Work.BoxShrink.Bubble.SlicePushOff`, which is **false** for the unrestricted
configuration (the standard torus of revolution with `s = 5/2`, `u = 0` and `σ = swap 1 2`, where
both `hS` and `hZ` hold — `Work.BoxShrink.Bubble.standard_counterexample`).  There the trace of the
plane is `⊤`, so the restriction excludes exactly that counterexample; what `BubbleHalf` needs is
only that *some* essential loop survives, not that every winding vector of the box region is
realised in the halves, and the transport form asks the stronger (and, in that configuration,
false) per-loop statement.  In the case `W(planeTrace) = ⊥` the slice is contractible and the
per-loop matching is the correct strengthening of the span inequality, see
`traceClassBound_of_regionTransport`. -/
def RegionTransportSpanBotTame : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    TransverseSlice ψ s c σ u → TameSlice ψ s c σ u →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) →
    Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (planeTrace (Work.Smooth.Morse.torus ψ) c σ u) = ⊥ →
    RegionTransport (Work.Smooth.Morse.torus ψ) s c σ u

/-- The transport form for every parametrised torus, with the inessentiality of the slice and of
the trace of the cutting plane.  (The trace hypothesis is needed as in
`RegionTransportSpanBotTame`; see the warning there.) -/
def RegionTransportAll : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.SurgeryInvariance.WindingSpan P (planeTrace P c σ u) = ⊥ →
    RegionTransport P s c σ u

/-! ## The transport form gives the residual -/

/-- **The two regions have the same winding span.** -/
theorem windingSpan_eq_of_regionTransport {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : RegionTransport P s c σ u) :
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) =
      Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u) :=
  (Work.SurgeryInvariance.RegionEquivalent.windingSpan_eq h).symm

/-- **The transport form gives the residual.** -/
theorem traceClassBound_of_regionTransport {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : RegionTransport P s c σ u) : TraceClassBound P s c σ u :=
  Or.inl (le_of_eq (windingSpan_eq_of_regionTransport h))

/-- **The transport form for every configuration gives the hypothesis-free residual.** -/
theorem traceClassBound_of_regionTransportAll (h : RegionTransportAll) :
    ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      Work.SurgeryInvariance.WindingSpan P (planeTrace P c σ u) = ⊥ →
      TraceClassBound P s c σ u :=
  fun P s c σ u hbot => traceClassBound_of_regionTransport (h P s c σ u hbot)

/-- **A transported loop of the halves is essential whenever the box region is.**  In the transport
form the winding vectors of the two regions coincide, so the halves carry an essential loop as soon
as the box region does. -/
theorem containsEssentialLoop_halves_of_regionTransport {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (h : RegionTransport P s c σ u)
    (hbox : P.ContainsEssentialLoop (Work.BoxShrink.Core.boxRegion P s c σ)) :
    P.ContainsEssentialLoop
      (Work.BoxShrink.Core.upperRegion P s c σ u ∪
        Work.BoxShrink.Core.lowerRegion P s c σ u) := by
  have hne : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) ≠ ⊥ :=
    (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr hbox
  rw [windingSpan_eq_of_regionTransport h] at hne
  exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hne

/-- **The transport form gives Pardon's Lemma 3 conclusion**, given the dichotomy at the box
sphere: the halves are disjoint open pieces and one of them carries the loop. -/
theorem bubbleHalf_of_regionTransport {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : RegionTransport P s c σ u) : Work.BoxShrink.Bubble.BubbleHalf P s c σ u := by
  intro hbox
  have h1 := containsEssentialLoop_halves_of_regionTransport (P := P) h hbox
  have hsplit := Work.SurgeryInvariance.Span.union_eq_sup (P := P)
    (Work.BoxShrink.Core.isOpenInCarrier_upperRegion P s c σ u)
    (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion P s c σ u)
    (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion P s c σ u)
  have hne : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.upperRegion P s c σ u) ⊔
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.lowerRegion P s c σ u) ≠ ⊥ := by
    rw [← hsplit]
    exact (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr h1
  rcases not_and_or.mp (fun hh : Work.SurgeryInvariance.WindingSpan P
      (Work.BoxShrink.Core.upperRegion P s c σ u) = ⊥ ∧
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.lowerRegion P s c σ u) = ⊥ =>
      hne (by rw [hh.1, hh.2, sup_bot_eq])) with hup | hlo
  · exact Or.inl ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hup)
  · exact Or.inr ((Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mp hlo)

/-! ## The homotopy route -/

/-- **The homotopy form of the push-off gives the residual.**  If every loop of the region inside
the box is homotopic in the torus to a loop of the union of the halves, then the winding span of the
box region is contained in that of the halves: the winding vector is a homotopy invariant
(`Work.SurgeryInvariance.WindingOf.homotopic_eq`). -/
theorem traceClassBound_of_homotopic_transport {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : ∀ γ : Work.CoreTopology.ClosedCurve P,
      (∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.boxRegion P s c σ) →
      ∃ γ' : Work.CoreTopology.ClosedCurve P,
        (∀ t : ℝ, γ' t ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u) ∧ Work.CoreTopology.Homotopic P γ γ') :
    TraceClassBound P s c σ u := by
  refine Or.inl (windingSpan_le_of_homotopic_split (P := P)
    (A := Work.BoxShrink.Core.boxRegion P s c σ)
    (A' := Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u) (Z := ∅) ?_ ?_)
  · intro γ hγ
    exact Or.inl (h γ hγ)
  · rw [Work.SurgeryInvariance.WindingSpan, Work.SurgeryInvariance.windingVectors]
    simp

/-- **The homotopy form gives the transport form** (as soon as the halves are non-empty, so that a
transported loop can be produced when the given loop is constant).  This is the sense in which the
homotopy form is the stronger hypothesis; the transport form is what the family argument needs. -/
theorem regionTransport_of_homotopic_transport {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : ∀ γ : Work.CoreTopology.ClosedCurve P,
      (∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.boxRegion P s c σ) →
      ∃ γ' : Work.CoreTopology.ClosedCurve P,
        (∀ t : ℝ, γ' t ∈ Work.BoxShrink.Core.upperRegion P s c σ u ∪
          Work.BoxShrink.Core.lowerRegion P s c σ u) ∧ Work.CoreTopology.Homotopic P γ γ') :
    RegionTransport P s c σ u := by
  constructor
  · intro γ hγ
    refine ⟨γ, ?_, rfl⟩
    intro t
    exact Or.elim (hγ t)
      (fun hh => Work.BoxShrink.Core.upperRegion_subset P s c σ u hh)
      (fun hh => Work.BoxShrink.Core.lowerRegion_subset P s c σ u hh)
  · intro γ hγ
    obtain ⟨γ', hγ', hhom⟩ := h γ hγ
    exact ⟨γ', hγ', (Work.SurgeryInvariance.WindingOf.homotopic_eq hhom).symm⟩

/-! ## Degenerate instances of the transport form -/

/-- **If the plane misses the box region the two regions coincide** and the transport is the
identity relation. -/
theorem regionTransport_of_halves_eq_boxRegion {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u = Work.BoxShrink.Core.boxRegion P s c σ) :
    RegionTransport P s c σ u := by
  rw [RegionTransport, h]
  exact ⟨fun γ hγ => ⟨γ, hγ, rfl⟩, fun γ hγ => ⟨γ, hγ, rfl⟩⟩

/-- **If the empty slice makes the box region the union of the halves**, the transport form
holds. -/
theorem regionTransport_of_sliceRegion_eq_empty {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.BoxShrink.Core.sliceRegion P s c σ u = ∅) : RegionTransport P s c σ u := by
  refine regionTransport_of_halves_eq_boxRegion (P := P) ?_
  rw [Work.BoxShrink.Core.boxRegion_eq_union P s c σ u, h, union_empty]

/-- **If the box region is contained in an embedded disc of the surface then the transport form
holds**: every loop of the box region is inessential (the disc is contractible), so each is matched
by a constant loop of a half-region. -/
theorem regionTransport_of_boxRegion_subset_disc {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {u : ℝ} {D : Work.SurgeryInvariance.DiscRegion P}
    (hsub : Work.BoxShrink.Core.boxRegion P s c σ ⊆ D.carrier)
    (hne : (Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u).Nonempty) :
    RegionTransport P s c σ u := by
  obtain ⟨p, hp⟩ := hne
  have hpc : p ∈ P.carrier :=
    Or.elim hp
      (fun hh => (Work.BoxShrink.Core.mem_upperRegion.mp hh).1)
      (fun hh => (Work.BoxShrink.Core.mem_lowerRegion.mp hh).1)
  constructor
  · intro γ hγ
    refine ⟨γ, ?_, rfl⟩
    intro t
    exact Or.elim (hγ t)
      (fun hh => Work.BoxShrink.Core.upperRegion_subset P s c σ u hh)
      (fun hh => Work.BoxShrink.Core.lowerRegion_subset P s c σ u hh)
  · intro γ hγ
    have hw0 : Work.SurgeryInvariance.windingOf P γ = (0, 0) := by
      by_contra hw
      exact Work.SurgeryInvariance.DiscRegion.not_isEssential D γ
        (fun t => hsub (hγ t))
        ((Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P γ).mpr hw)
    have hw0' : Work.SurgeryInvariance.windingOf P
        (Work.InnermostDisk.constCurve P p hpc) = (0, 0) := by
      by_contra hw
      exact Work.InnermostDisk.not_isEssential_of_const P p hpc
        ((Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P _).mpr hw)
    exact ⟨Work.InnermostDisk.constCurve P p hpc, fun _ => hp, by rw [hw0', hw0]⟩

/-- **If the box region carries no essential loop then the transport form holds** (as soon as the
union of the halves is non-empty, so that a constant loop of a half-region can be produced): every
loop of the box region has vanishing winding, and is matched by a constant loop. -/
theorem regionTransport_of_windingSpan_bot {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hbot : Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.boxRegion P s c σ) = ⊥)
    (hne : (Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u).Nonempty) :
    RegionTransport P s c σ u := by
  obtain ⟨p, hp⟩ := hne
  have hpc : p ∈ P.carrier :=
    Or.elim hp
      (fun hh => (Work.BoxShrink.Core.mem_upperRegion.mp hh).1)
      (fun hh => (Work.BoxShrink.Core.mem_lowerRegion.mp hh).1)
  constructor
  · intro γ hγ
    refine ⟨γ, ?_, rfl⟩
    intro t
    exact Or.elim (hγ t)
      (fun hh => Work.BoxShrink.Core.upperRegion_subset P s c σ u hh)
      (fun hh => Work.BoxShrink.Core.lowerRegion_subset P s c σ u hh)
  · intro γ hγ
    have hw0 : Work.SurgeryInvariance.windingOf P γ = (0, 0) := by
      have : ((((Work.SurgeryInvariance.windingOf P γ).1 : ℤ) : ℚ),
          (((Work.SurgeryInvariance.windingOf P γ).2 : ℤ) : ℚ)) ∈
          (⊥ : Submodule ℚ (ℚ × ℚ)) := by
        rw [← hbot]
        exact Submodule.subset_span ⟨γ, hγ, rfl⟩
      rw [Submodule.mem_bot] at this
      have h1 : ((Work.SurgeryInvariance.windingOf P γ).1 : ℚ) = 0 := by
        simpa using congrArg Prod.fst this
      have h2 : ((Work.SurgeryInvariance.windingOf P γ).2 : ℚ) = 0 := by
        simpa using congrArg Prod.snd this
      exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)
    have hw0' : Work.SurgeryInvariance.windingOf P
        (Work.InnermostDisk.constCurve P p hpc) = (0, 0) := by
      by_contra hw
      exact Work.InnermostDisk.not_isEssential_of_const P p hpc
        ((Work.SurgeryInvariance.isEssential_iff_windingOf_ne_zero P _).mpr hw)
    exact ⟨Work.InnermostDisk.constCurve P p hpc, fun _ => hp, by rw [hw0', hw0]⟩

/-! ## The two-region family of the pinch -/

/-- **The two-region family of the pinch**: the region inside the box before the pinching parameter
`1`, and the union of the two half-regions at and after it.  This is Pardon's pinching family
collapsed to its two endpoints (the pinch is a single step at `t = 1`). -/
def transportRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (t : ℝ) : Set R3 :=
  if t < 1 then Work.BoxShrink.Core.boxRegion P s c σ
  else Work.BoxShrink.Core.upperRegion P s c σ u ∪ Work.BoxShrink.Core.lowerRegion P s c σ u

theorem transportRegion_of_lt {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u t : ℝ} (ht : t < 1) :
    transportRegion P s c σ u t = Work.BoxShrink.Core.boxRegion P s c σ := by
  simp only [transportRegion, if_pos ht]

theorem transportRegion_of_one_le {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u t : ℝ}
    (ht : 1 ≤ t) :
    transportRegion P s c σ u t = Work.BoxShrink.Core.upperRegion P s c σ u ∪
      Work.BoxShrink.Core.lowerRegion P s c σ u := by
  simp only [transportRegion, if_neg (not_lt.mpr ht)]

/-- **The transport form generates Pardon's pinching family**: the two-region family
`{boxRegion, upperRegion ∪ lowerRegion}` is a sweep with Pardon's local models, whose single
exceptional parameter is the pinching parameter `1`, whose exceptional step is the transport, and
whose dichotomy at every parameter before `1` is the dichotomy at the box sphere.

The point is that the pinch's last step — the region losing the *closed* slice — is not a
`SurgeryStepSmall` (the slice is not the interior of a disc), so it has to be carried by the
loop-level relation `RegionEquivalent`; this is exactly what the transport form provides. -/
def transportSweep (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (hdich : Work.BoxShrink.Bubble.PardonDichotomy P
      (Work.BoxShrink.Core.boxRegion P s c σ))
    (h : RegionTransport P s c σ u) : Work.BoxShrink.Bubble.SweepLoopsSmall P where
  region := transportRegion P s c σ u
  exc := ({1} : Finset ℝ)
  regular := by
    intro t ht
    have ht1 : t ≠ 1 := fun hh => ht (by rw [hh]; simp)
    rcases lt_or_gt_of_ne ht1 with hlt | hgt
    · refine ⟨(1 - t) / 2, by linarith, ?_, ?_⟩
      · intro s hs hs1
        rw [Finset.mem_singleton] at hs1
        rw [hs1] at hs
        rw [abs_of_pos (by linarith : (0 : ℝ) < 1 - t)] at hs
        linarith
      · intro s hs
        have hs1 : s < 1 := by
          rw [abs_lt] at hs
          linarith [hs.2]
        rw [transportRegion_of_lt hlt, transportRegion_of_lt hs1]
        exact ⟨fun γ hγ => ⟨γ, hγ, rfl⟩, fun γ hγ => ⟨γ, hγ, rfl⟩⟩
    · refine ⟨(t - 1) / 2, by linarith, ?_, ?_⟩
      · intro s hs hs1
        rw [Finset.mem_singleton] at hs1
        rw [hs1] at hs
        rw [abs_of_neg (by linarith : (1 : ℝ) - t < 0)] at hs
        linarith
      · intro s hs
        have hs1 : 1 ≤ s := by
          rw [abs_lt] at hs
          linarith [hs.1]
        rw [transportRegion_of_one_le (le_of_lt hgt), transportRegion_of_one_le hs1]
        exact ⟨fun γ hγ => ⟨γ, hγ, rfl⟩, fun γ hγ => ⟨γ, hγ, rfl⟩⟩
  surgery := by
    intro t ht
    have ht1 : t = 1 := Finset.mem_singleton.mp ht
    subst ht1
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro s _
    by_cases hs1 : s < 1
    · rw [transportRegion_of_one_le le_rfl, transportRegion_of_lt hs1]
      exact Or.inr h
    · rw [transportRegion_of_one_le le_rfl, transportRegion_of_one_le (le_of_not_gt hs1)]
      exact Or.inr ⟨fun γ hγ => ⟨γ, hγ, rfl⟩, fun γ hγ => ⟨γ, hγ, rfl⟩⟩
  dichotomy := by
    intro t ht
    rw [transportRegion_of_lt ht]
    exact hdich

/-- **The transport form gives Pardon's pinch datum.** -/
def pinchDatum_of_regionTransport {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hdich : Work.BoxShrink.Bubble.PardonDichotomy P
      (Work.BoxShrink.Core.boxRegion P s c σ))
    (h : RegionTransport P s c σ u) : Work.BoxShrink.Bubble.PinchDatum P s c σ u where
  sweep := transportSweep P s c σ u hdich h
  zero := transportRegion_of_lt (by norm_num : (0 : ℝ) < 1)
  one := transportRegion_of_one_le le_rfl
  pinch := by
    refine ⟨1 / 2, by norm_num, ?_⟩
    change P.ContainsEssentialLoop (transportRegion P s c σ u (1 / 2)) →
      P.ContainsEssentialLoop (transportRegion P s c σ u 1)
    rw [transportRegion_of_lt (by norm_num : (1 / 2 : ℝ) < 1), transportRegion_of_one_le le_rfl]
    exact containsEssentialLoop_halves_of_regionTransport h

/-- **The dictionary: the transport form *is* the parent chapter's `SlicePushOff`.**  The
interesting conjunct of `RegionEquivalent P (upperRegion ∪ lowerRegion) (boxRegion)` is "every loop
of the box region is matched by a loop of the halves with the same winding vector", which is exactly
the inclusion of the sets of realised winding vectors.  Consequently the transport form is *false*
for the unrestricted configuration (the standard torus with `s = 5/2`, where both inessentiality
hypotheses hold and `Work.BoxShrink.Bubble.standard_counterexample` refutes `SlicePushOff`), and the
hypothesis `W(planeTrace) = ⊥` of `RegionTransportSpanBotTame` / `RegionTransportAll` is essential:
what `BubbleHalf` needs is only that *some* essential loop survives the pinch. -/
theorem regionTransport_iff_slicePushOff {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    RegionTransport P s c σ u ↔ Work.BoxShrink.Bubble.SlicePushOff P s c σ u := by
  constructor
  · intro h
    rintro k ⟨γ, hγ, rfl⟩
    obtain ⟨γ', hγ', hw⟩ := h.2 γ hγ
    exact ⟨γ', hγ', hw⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro γ hγ
      refine ⟨γ, ?_, rfl⟩
      intro t
      exact Or.elim (hγ t)
        (fun hh => Work.BoxShrink.Core.upperRegion_subset P s c σ u hh)
        (fun hh => Work.BoxShrink.Core.lowerRegion_subset P s c σ u hh)
    · intro γ hγ
      obtain ⟨γ', hγ', hw⟩ := h ⟨γ, hγ, rfl⟩
      exact ⟨γ', hγ', hw⟩

/-- **The slice is contained in the trace of the plane**, so its inessentiality is a consequence of
the inessentiality of the trace.  (This is why the hypothesis `¬ ContainsEssentialLoop sliceRegion`
of `RegionTransportSpanBotTame` is redundant in the presence of `W(planeTrace) = ⊥`; it is kept
because it is one of the hypotheses of the deliverable.) -/
theorem sliceRegion_subset_planeTrace {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ} :
    Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ planeTrace P c σ u := by
  intro y hy
  rw [Work.BoxShrink.Core.mem_sliceRegion] at hy
  rw [mem_planeTrace]
  exact ⟨hy.1, hy.2.2⟩

/-- **`W(planeTrace) = ⊥` gives the inessentiality of the slice.** -/
theorem not_containsEssentialLoop_sliceRegion_of_planeTrace_bot {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hbot : Work.SurgeryInvariance.WindingSpan P (planeTrace P c σ u) = ⊥) :
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) := by
  rw [← Work.SurgeryInvariance.windingSpan_ne_bot_iff]
  refine fun hne => hne ?_
  refine le_bot_iff.mp ?_
  rw [← hbot]
  exact Work.SurgeryInvariance.WindingSpan_mono P sliceRegion_subset_planeTrace

/-! ## The transport form is inhabited in the degenerate cases the parent chapter covers -/

/-- **The transport form from the parent chapter's push-off.** -/
theorem regionTransport_of_slicePushOff {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.BoxShrink.Bubble.SlicePushOff P s c σ u) : RegionTransport P s c σ u :=
  (regionTransport_iff_slicePushOff (P := P) (s := s) (c := c) (σ := σ) (u := u)).mpr h

/-- **The transport form when the plane meets the region inside the box in finitely many
points.** -/
theorem regionTransport_of_finite_slice {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hfin : (Work.BoxShrink.Core.sliceRegion P s c σ u).Finite) : RegionTransport P s c σ u :=
  regionTransport_of_slicePushOff (Work.BoxShrink.Bubble.slicePushOff_of_finite_slice
    (P := P) (s := s) (c := c) (σ := σ) (u := u) hfin)

/-- **The transport form when the plane meets the region inside the box in countably many
points.** -/
theorem regionTransport_of_countable_slice {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hcount : (Work.BoxShrink.Core.sliceRegion P s c σ u).Countable) : RegionTransport P s c σ u :=
  regionTransport_of_slicePushOff (Work.BoxShrink.Bubble.slicePushOff_of_countable_slice
    (P := P) (s := s) (c := c) (σ := σ) (u := u) hcount)

/-- **The transport form when the plane misses the box region** (the two regions coincide). -/
theorem regionTransport_of_empty_slice {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : Work.BoxShrink.Core.sliceRegion P s c σ u = ∅) : RegionTransport P s c σ u :=
  regionTransport_of_slicePushOff (Work.BoxShrink.Bubble.Instances.slicePushOff_of_empty_slice
    (P := P) (s := s) (c := c) (σ := σ) (u := u) h)

/-! ## The transport form gives the residual in Pardon's trivial `2`-surgery case -/

/-- **The transport form restricted to the inessential-trace case gives the `⊥` half of the
residual.**  (The restriction is what makes the statement true; see
`regionTransport_iff_slicePushOff`.) -/
theorem traceClassBoundSpanBot_of_regionTransportSpanBotTame
    (h : RegionTransportSpanBotTame) : TraceClassBoundSpanBot :=
  fun ψ s c σ u hT htame hS hZ hbot =>
    (traceClassBound_iff_box_le_halves_of_traceSpan_bot
      (P := Work.Smooth.Morse.torus ψ) (s := s) (c := c) (σ := σ) (u := u) hbot).mp
      (traceClassBound_of_regionTransport (h ψ s c σ u hT htame hS hZ hbot))

/-- **The transport form for every parametrised torus gives the `⊥` half of the residual.** -/
theorem traceClassBoundSpanBot_of_regionTransportAll (h : RegionTransportAll) :
    TraceClassBoundSpanBot :=
  fun ψ s c σ u hT htame hS hZ hbot =>
    (traceClassBound_iff_box_le_halves_of_traceSpan_bot
      (P := Work.Smooth.Morse.torus ψ) (s := s) (c := c) (σ := σ) (u := u) hbot).mp
      (traceClassBound_of_regionTransport (h (Work.Smooth.Morse.torus ψ) s c σ u hbot))

/-! ## The two halves of the residual assembled -/

/-- **The chapter's residual in the tame form, from the transport form and the essential-trace
case.** -/
theorem traceClassBoundTame_of_spanNeBot_regionTransportSpanBotTame
    (hne : TraceClassBoundSpanNeBot) (h : RegionTransportSpanBotTame) : TraceClassBoundTame :=
  traceClassBoundTame_of_spanNeBot_spanBot hne
    (traceClassBoundSpanBot_of_regionTransportSpanBotTame h)

/-- **The deliverable `Work.BoxShrink.Pinch.PushOffHalfTame` from the transport form and the
essential-trace case**, with Pardon's equation (1) and the general position of the box-sphere trace:
this is what a proof of the pinch has to supply. -/
theorem pushOffHalfTame_of_spanNeBot_regionTransportSpanBotTame (h1 : Equation1Input)
    (hnice : BoxSliceNice) (hne : TraceClassBoundSpanNeBot) (h : RegionTransportSpanBotTame) :
    PushOffHalfTame :=
  pushOffHalfTame_of_traceClassBoundTame h1 hnice
    (traceClassBoundTame_of_spanNeBot_regionTransportSpanBotTame hne h)

/-- **The same assembly through Pardon's own pinch datum**: the transport form generates the
pinching family at every inessential-trace configuration, and one half carries an essential loop at
each of them. -/
theorem bubbleHalf_spanBot_of_regionTransportSpanBotTame (h1 : Equation1Input) (hnice : BoxSliceNice)
    (h : RegionTransportSpanBotTame) :
    ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
      TransverseSlice ψ s c σ u → TameSlice ψ s c σ u →
      ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
          (Work.BoxShrink.Core.sphereSet c σ s) →
      ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
          (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) →
      Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (planeTrace (Work.Smooth.Morse.torus ψ) c σ u) = ⊥ →
      Work.BoxShrink.Bubble.BubbleHalf (Work.Smooth.Morse.torus ψ) s c σ u :=
  fun ψ s c σ u hT htame hS hZ hbot =>
    Work.BoxShrink.Bubble.bubbleHalf_of_pinchDatum
      (pinchDatum_of_regionTransport
        (pardonDichotomy_boxRegion_of_equation1 h1 (hnice ψ s c σ) hS)
        (h ψ s c σ u hT htame hS hZ hbot))

end

end Work.BoxShrink.Pinch
