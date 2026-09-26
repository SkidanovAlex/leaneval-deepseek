import Submission.Work.PinchLemma3.Residual

/-!
# The named targets of the chapter

The residual `SliceWall` is the dimension bound `dim W(Ω) ≤ dim W(Ω⁺ ∪ Ω⁻) + 1`.  It splits into
two cases, and each case has a *structural* sufficient condition.  This module names them, so that
they can be attacked by name, and proves that the three targets give the residual.

* `TrivialSurgeryTarget` — the case in which the whole trace `Γ = F ∩ P` of the cutting plane is
  contractible: then the pinch is a *trivial* `2`-surgery.  The natural-looking *span containment*
  `W(Ω) ≤ W(Ω⁺ ∪ Ω⁻)` in this case is **false** (it is the parent chapter's
  `TraceClassBoundSpanBot`; see `Residual.lean`'s module docstring and
  `Submission/Work/BoxShrink/Pinch/EXP`), so the target is stated as the *dimension* bound, which
  is the form that survives.
* `ArcDiscTarget` — the *arcs* of the slice close up inside the closed box: when the trace is
  essential (so the walls are genuine walls, cut out of an essential circle of the trace by the
  boundary of the box) the slice is contained in an embedded disc of the surface whose carrier
  lies in the *closed* box.  Both endpoint hypotheses are part of the hypothesis, and they are
  load-bearing: with an unbounded box radius the slice *is* the trace and the statement is false
  (the box swallows the torus; the reviewer's counterexample).
* `ClosedDiscBoundTarget` — the local model of the pinch for a disc that is allowed to *touch the
  boundary* of the box.  The sibling chapter proves the case in which the disc lies in the *open*
  box (`Work.BoxShrink.PinchOff.discRoute_holds`, `strong_of_slice_in_disc`); the arcs of the slice
  need the case in which the disc meets the boundary, because their endpoints lie on it and so no
  disc contained in the open box can contain them.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PinchLemma3

noncomputable section

/-- **The trivial-`2`-surgery case of the residual**: if the cutting plane meets the surface only in
contractible curves, the pinch loses at most one dimension (in fact the expectation — *not proved*,
and the naive stronger form is false — is that it loses nothing). -/
def TrivialSurgeryTarget : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) = ⊥ →
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.boxRegion P s c σ)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (halfRegions P s c σ u)) + 1

/-- **The arcs of the slice close up inside the closed box** — *one single disc*.

**This statement is FALSE**, and the module `Submission.Work.PinchLemma3.arcDiscRefuted` proves it
(`Work.PinchLemma3.not_arcDiscTarget`).  Counterexample: the standard torus of revolution with the
box centred at a point of its core circle, of size `2/3` and `σ = swap 1 2`, cut by the plane
`{y = 0}`; the box region is nonempty, the box sphere and the slice carry no essential loop, the
plane trace does — and the closed box region has four connected components while the slice meets
*two* of them, at `x = 13/5`, `z = ±4/5`, so that no connected disc inside the closed box can
contain the slice.  The statement is kept here because it is the natural first guess for the
*arcs* of the slice (their endpoints lie on the boundary of the box, so no disc of the open box can
contain them), and because its failure is exactly what rules that route out. -/
def ArcDiscTarget : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    (Work.BoxShrink.Core.boxRegion P s c σ).Nonempty →
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Pinch.planeTrace P c σ u) ≠ ⊥ →
    ∃ D : Work.SurgeryInvariance.DiscRegion P,
      D.carrier ⊆ closedBoxRegion P s c σ ∧
        Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior

/-- **The arcs of the slice are carried by finitely many discs of the closed box.**  The corrected
form of `ArcDiscTarget`: instead of one disc, a finite family, each disc contained in the closed box
region, covering the slice by their interiors.  This is the form the *arcs* actually have — in the
counterexample of `ArcDiscTarget` the slice meets two components of the closed box region — and it
is the closed-box analogue of the sibling chapter's `SliceDiscCovering`
(`Work.BoxShrink.PinchOff.SliceDiscCovering`), whose discs are required to lie in the *open* box. -/
def ClosedDiscsCoverTarget : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    (Work.BoxShrink.Core.boxRegion P s c σ).Nonempty →
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ P.ContainsEssentialLoop (Work.BoxShrink.Core.sliceRegion P s c σ u) →
    ∃ L : List (Work.SurgeryInvariance.DiscRegion P),
      (∀ D ∈ L, D.carrier ⊆ closedBoxRegion P s c σ) ∧
        (∀ x ∈ Work.BoxShrink.Core.sliceRegion P s c σ u, ∃ D ∈ L, x ∈ D.interior)

/-- **The local model of the pinch for a single disc that may touch the boundary of the box**:
a slice contained in the interior of one such disc costs at most one dimension.  This is the
single-disc case of `ClosedDiscsBoundTarget`; it is the statement a prover working on the closed-box
push-off should attack first, and it is what the parent chapter's `discRoute_holds` gives when the
disc is contained in the *open* box. -/
def ClosedDiscBoundTarget : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (D : Work.SurgeryInvariance.DiscRegion P),
    D.carrier ⊆ closedBoxRegion P s c σ →
    Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ D.interior →
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.boxRegion P s c σ)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (halfRegions P s c σ u)) + 1

/-- **The local model of the pinch for finitely many discs that may touch the boundary of the
box**: a slice covered by the interiors of finitely many embedded discs, each with carrier in the
*closed* box region, costs at most one dimension.  The sibling chapter proves the single-disc case
with the discs in the *open* box (`Work.BoxShrink.PinchOff.strong_of_slice_in_discs`); the arcs of
the slice need the closed-box case, because their endpoints lie on the boundary. -/
def ClosedDiscsBoundTarget : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (L : List (Work.SurgeryInvariance.DiscRegion P)),
    (∀ D ∈ L, D.carrier ⊆ closedBoxRegion P s c σ) →
    (∀ x ∈ Work.BoxShrink.Core.sliceRegion P s c σ u, ∃ D ∈ L, x ∈ D.interior) →
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P
        (Work.BoxShrink.Core.boxRegion P s c σ)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (halfRegions P s c σ u)) + 1

/-- **The closed half has the open half's span** when the slice is inessential in the surface.

**This statement is FALSE, and it is kept here as the record of a route that does not work.**
Witness: let `Ω` be an annular box region of the standard torus (a box thin in one coordinate
around a meridian), let the cutting plane meet `Ω` in a single radial *arc* (a crosscut), so that
`W(sliceRegion) = ⊥` holds because the slice is contractible; the upper half `upperRegion` is then a
*disc*, of vanishing span, while the closed upper half `closedUpper = upperRegion ∪ sliceRegion` is
the whole annulus, whose span is the line generated by the core.  The two spans therefore differ,
even though the slice is inessential.

This is the surface-theoretic content of the trap recorded in the parent chapter: the decomposition
of the region by the cutting plane cannot be pushed through the *closed* half, because the slice is
a closed subset of the box region whose complement is open, and a loop of the closed half may have
to run along the slice to stay closed (in the crosscut case the slice *closes up* an essential loop
of the closed half).  The arc inessentiality hypothesis `hZ` is not enough to make the closed half
deform to the open one. -/
def ClosedUpperEqTarget : Prop :=
  ∀ (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.sliceRegion P s c σ u) = ⊥ →
    Work.SurgeryInvariance.WindingSpan P (closedUpper P s c σ u) =
      Work.SurgeryInvariance.WindingSpan P (Work.BoxShrink.Core.upperRegion P s c σ u)

/-- **The essential-trace case of the residual.**  With both endpoint hypotheses and an *essential*
trace of the cutting plane (so the walls of the slice are genuine walls), the region inside the box
loses at most one dimension.  This is `SliceWall` with the trace-inessential case removed; by
`sliceWall_of_trivialSurgery_and_essential` it is, together with the trivial-surgery case
`TrivialSurgeryTarget`, exactly the residual.  Note that `TrivialSurgeryTarget` is *not* an
independent open problem: `Submission/Work/PinchLemma3/NoFullJumpAux.lean` proves
`trivialSurgery_of_noFullJump : NoFullJump → TrivialSurgeryTarget`, so the whole trivial-surgery
case rests on the single lemma `Work.PinchLemma3.NoFullJump`. -/
def EssentialTraceTarget : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) →
    Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Pinch.planeTrace (Work.Smooth.Morse.torus ψ) c σ u) ≠ ⊥ →
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)) ≤
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (halfRegions (Work.Smooth.Morse.torus ψ) s c σ u)) + 1

/-- **The residual is the conjunction of its two cases**: `TrivialSurgeryTarget` (trace
inessential) and `EssentialTraceTarget` (trace essential).  This is the strict split of the pinch,
and the reason the chapter's residual is one case smaller than the parent chapter's `PinchNoJump`:
the trivial-surgery case is reduced to the single lemma `Work.PinchLemma3.NoFullJump`
(`trivialSurgery_of_noFullJump`), so a prover only has to supply `NoFullJump` and the essential
case. -/
theorem sliceWall_of_trivialSurgery_and_essential (h0 : TrivialSurgeryTarget)
    (h1 : EssentialTraceTarget) : SliceWall := by
  intro ψ s c σ u hS hZ
  by_cases hT : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Pinch.planeTrace (Work.Smooth.Morse.torus ψ) c σ u) = ⊥
  · exact h0 (Work.Smooth.Morse.torus ψ) s c σ u hS hT
  · exact h1 ψ s c σ u hS hZ hT

/-- **The three targets give the residual `SliceWall`.**

* if the trace of the cutting plane is inessential, the pinch is a trivial `2`-surgery
  (`TrivialSurgeryTarget`);
* if the trace is essential, the slice is carried by finitely many discs of the closed box
  (`ClosedDiscsCoverTarget`), and the local model for discs that touch the boundary
  (`ClosedDiscsBoundTarget`) says that this costs nothing beyond one dimension.

Note that the *single*-disc version `ArcDiscTarget` of the second target is **false**
(`Work.PinchLemma3.not_arcDiscTarget`, `Submission/Work/PinchLemma3/arcDiscRefuted`), so the family
version is the one that has to be used; this is what makes the *arcs* of the slice (whose endpoints
lie on the boundary of the box and can therefore be spread over several components of the closed box
region) the exact content of the remaining difficulty. -/
theorem sliceWall_of_targets (h0 : TrivialSurgeryTarget) (h1 : ClosedDiscsCoverTarget)
    (h2 : ClosedDiscsBoundTarget) : SliceWall := by
  intro ψ s c σ u hS hZ
  by_cases hT : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Pinch.planeTrace (Work.Smooth.Morse.torus ψ) c σ u) = ⊥
  · exact h0 (Work.Smooth.Morse.torus ψ) s c σ u hS hT
  · by_cases hne : (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ).Nonempty
    · obtain ⟨L, hsub, hcov⟩ := h1 (Work.Smooth.Morse.torus ψ) s c σ u hne hS hZ
      exact h2 (Work.Smooth.Morse.torus ψ) s c σ u L hsub hcov
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      have hbot : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) = ⊥ := by
        rw [hne, Work.BoxShrink.Pinch.windingSpan_empty]
      rw [hbot, Submodule.finrank_eq_zero.mpr rfl]
      exact Nat.zero_le _

end

end Work.PinchLemma3
