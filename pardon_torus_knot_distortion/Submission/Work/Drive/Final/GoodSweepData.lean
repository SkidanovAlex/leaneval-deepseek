import Mathlib
import Submission.Work.Drive.Mono.Residual

/-!
# `GoodSweepData`: the data of a *good* tilted sweep (field (L) of `TiltedSweepMono`)

This is the interface of the project lead's `01:50` directive: field **(L)** of
`Work.Drive.Final.TiltedSweepMono` — *no level of vanishing span is reached by a drop from `⊤` just
below* — is proved at data satisfying `GoodSweepData`, by

* **`eventGates`** (per event type, via the proved `Work.Drive.Mono.fibreRegion_pathConnected`),
* **`dent_regular`** (the dent `Ψ z = z ± a'·χ(‖z − p‖/r)·d` is regular),
* **`noJumpBelow_of_region`** (Span/Split's argument at the dented region), and then
* **`noJumpBelow_of_goodData`** by processing the events at one level **one at a time**.

The definition below is the **first draft** of the interface: it reuses
`Work.Drive.Mono.TiltData` (genericity of the sweep height — `Work.Drive.Final.TiltedGenericity`,
proved upstream by `Work.Drive.EpsForm.tiltedSweepGenericity_holds_sized` — together with the size
condition `‖v − e_{σ 2}‖·R < h` and the window conditions) and adds, concretely, the clauses of the
design that need no further vocabulary:

* **`above` / `below`** — the *thin cut*: the slab really cuts the box, on both sides of the wall
  (`∃ y ∈ PBox` with `⟪v,y⟫` above `⟪v,c⟫ + u + h`, respectively below `⟪v,c⟫ + u − h`);
* **`offK`** — every critical point of the sweep height inside the closed box and the closed slab is
  off the knot (so that the dents may be performed without meeting `K`);
* **`knotGP`** — the knot meets the two slab faces transversally (its `⟪v,·⟫`-coordinate has nonzero
  derivative there), which is the general position needed to bound the in-box crossing count.

## Still to be added (design §2 of `Submission/Work/Drive/Mono/NOTES_lead_pinch_design.md`)

These fields need their own small definitions first, and are *not* in this draft:

* **`capsFree`** — no active cap face in the slab (needs "active constraint" on the box ∩ slab);
* **`indep`** — at most two active constraints, with independent differentials;
* **`cornerGen`** — `dL ∉ ℝ·dG` at a two-constraint point;
* **`finite`** — the event set (`ℓ`-critical points of the sweep height on the box ∩ slab) is finite;
* **`morse2` / `morse1`** — the nondegeneracy of the events, interior and on one constraint (clause
  (iii) of `TiltedGenericity` already gives the interior part);
* **`inExc`** — `ℓ` of every event lies in `exc` (also already part of `TiltedGenericity` (iii));
* **`push`** — the existence of the sequence of dents of `noJumpBelow_of_goodData`.

The intended consumers are `Work.Drive.Final.eventGates`, `Work.Drive.Final.dent_regular`,
`Work.Drive.Final.noJumpBelow_of_region` and `Work.Drive.Final.noJumpBelow_of_goodData`, each taking
`GoodSweepData` as a hypothesis (as the per-clause `Prop`s of `Drive/Mono/Residual.lean` take
`TiltData`).
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Final

noncomputable section

/-- **The data of a good tilted sweep.**  `TiltData` (genericity, size and window conditions) plus
the thin-cut clauses (`above`, `below`), the `offK` clause (the critical points of the sweep height
in the box ∩ closed slab avoid the knot) and the knot general position `knotGP` with respect to the
two slab faces.  See the module docstring for the design clauses still to be added. -/
def GoodSweepData (ψ : Submission.Diffeo) (K : Knot) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ) : Prop :=
  Work.Drive.Mono.TiltData ψ s c σ u v h R ℓ exc lam0 lam1 ∧
  -- the thin cut: the slab is met strictly on both sides of the wall
  (∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y) ∧
  (∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h) ∧
  -- `offK`: no critical point of the sweep height in the box ∩ closed slab lies on the knot
  (∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ →
    Work.BoxShrink.Pinch.par ψ p ∈
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h →
    fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p = 0 →
    ∀ t : ℝ, K.curve t ≠ Work.BoxShrink.Pinch.par ψ p) ∧
  -- `knotGP`: the knot meets the two slab faces transversally
  (∀ t : ℝ, |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h →
    deriv (fun s : ℝ => inner ℝ v (K.curve s)) t ≠ 0)


/-! ## The event layer of the gate/dent vocabulary

The design's gates are attached to the **events**: the critical points of the sweep height on the box
∩ closed slab (`fderiv (sweepHeight ψ ℓ) = 0`).  By clause (iii) of
`Work.Drive.Final.TiltedGenericity` every such point is non-degenerate and its value lies in `exc`,
and by clause (iv) two events with the same value *coincide*; so the event values below are a subset
of `exc` and the events are isolated in the parameter plane.  The definitions below fix the notation
the consumer statements (`eventGates`, `dent_regular`, `noJumpBelow_of_goodData`) share. -/

/-- **An event** of the tilted sweep: a point of the parameter plane whose image lies in the box and
in the *closed* slab and at which the sweep height is critical.  (Clause (iii) of
`TiltedGenericity` makes each such point non-degenerate and puts its value in `exc`.) -/
def IsEvent (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3)
    (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) (p : ℝ × ℝ) : Prop :=
  Work.BoxShrink.Pinch.par ψ p ∈ Submission.PBox s c σ ∧
    Work.BoxShrink.Pinch.par ψ p ∈
      Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h ∧
    fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p = 0

/-- The **set of events**, as a subset of the parameter plane. -/
def eventSet (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3)
    (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) : Set (ℝ × ℝ) :=
  {p | IsEvent ψ s c σ u v h ℓ p}

/-- The **value** of an event: the level of the sweep at which it occurs. -/
def eventValue (ψ : Submission.Diffeo) (ℓ : R3 →L[ℝ] ℝ) (p : ℝ × ℝ) : ℝ :=
  ℓ (Work.BoxShrink.Pinch.par ψ p)

/-- The **levels of the events**, as a subset of the line.  By clause (iii) of `TiltedGenericity` it
is contained in `exc` (and finite). -/
def eventValues (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3)
    (h : ℝ) (ℓ : R3 →L[ℝ] ℝ) : Set ℝ :=
  eventValue ψ ℓ '' eventSet ψ s c σ u v h ℓ

/-- **The event values lie in `exc`** — immediate from clause (iii) of `TiltedGenericity` (the
consumer statements quote this as `hG.1.2.2.1`). -/
theorem eventValues_subset_exc {ψ : Submission.Diffeo} {K : Knot} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ} (hG : GoodSweepData ψ K s c σ u v h R ℓ exc lam0 lam1) :
    eventValues ψ s c σ u v h ℓ ⊆ (exc : Set ℝ) := by
  rintro t ⟨p, hp, rfl⟩
  exact (hG.1.1.2.2.1 p hp.1 hp.2.1 hp.2.2).2

end

end Work.Drive.Final
