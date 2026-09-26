import Submission.Work.Collar3D.Defs

/-!
# Pardon's single cut-and-paste step, in `ℝ³` alone

The ledger field `Work.BoxShrink.ClassicalInputs.pushThrough` is
`Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard`, whose content is
Pardon's cut-and-paste: *an embedded disc crossing a surface along finitely many pairwise disjoint
inessential Jordan curves can be modified, keeping its boundary and staying embedded, so as to
eliminate one of the crossing curves.*

This file records the **single classical proposition** from which that step follows, in the
vocabulary of `ℝ³` alone — no torus, no box, no `SliceData`:

`Work.Collar3D.PinchedSurgery` — *Pardon's (global) push-through*: an embedded disc `β` whose
interior misses a **locally flat** surface `F`, whose boundary curve `γ` lies on `F` and bounds a
disc `Σ ⊆ F` of the surface, can be pushed through `F` by an ambient homeomorphism which

* fixes the boundary curve `θ ↦ e (e^{iθ})` of a given larger embedded disc `e ⊇ β` pointwise,
* fixes a prescribed compact set `C` (disjoint from `β(𝔻)`) pointwise,
* moves the interior of `e` off the surface `F` except into `C`.

The classical content is **Alexander's theorem** for the embedded `2`-sphere `β ∪ Σ` (it bounds a
ball) together with the **isotopy extension theorem** (push the part of `e` inside that ball
through it, keeping everything outside a neighbourhood of `β(𝔻)` fixed).  Nothing else: no
regular-neighbourhood theorem, no planar Jordan–Schoenflies, no tameness of the *discs*, no annulus
theorem.

## Why `F` must be assumed locally flat — a counterexample

The sibling chapter `Submission/Work/Smooth/PushThrough3D` states the same proposition **without**
the hypothesis that `F` is locally flat (`Work.Smooth.PushThrough3D.PinchedSurgeryInput`), and that
statement is **FALSE**.  Counterexample (by the reviewer of this chapter; the argument is recorded
in full in `Submission/Work/Collar3D/README.md`, §5ter):

* `e` is the flat unit disc `z ↦ (Re z, Im z, 0)`, `β := e ∘ (·/2)` the disc of radius `1/2`, and
  `γ := β ∘ circlePoint` the circle of radius `1/2`;
* `F := Set.range γ ∪ (ℝ³ ∖ Set.range e)` — a wild set, not a surface: near a point of `γ` it
  contains two open half-balls;
* `Σ :=` the cone on `γ` from `(0,0,1)` has all of `Σ(𝔻) ⊆ F` (its interior points have positive
  third coordinate, hence lie outside `Set.range e`), and `C := ∅`;

every *hypothesis* of the unrestricted statement holds (`β(int 𝔻)` misses `F`, and an interior point
of `e` lies on `F` only if it lies on `γ`), but the *conclusion* cannot: it would force
`H (e(int 𝔻)) ⊆ ℝ³ ∖ F ∩ Set.range e`, a set with **two** connected components in the plane, while
`H (e(𝔻)) = H (e(int 𝔻)) ∪ e(∂𝔻)` is connected and `e(∂𝔻)` is the outer boundary; the inner
component is excluded by connectivity, and the outer one by the fact that the standard circle is not
null-homotopic in the punctured plane (it would be an embedded closed disc carrying the generator of
`π₁(S¹) = ℤ`).

The hypothesis `LocallyFlatSet F` is therefore **not** a convenience: it is exactly what rules this
configuration out, and it is the setting of Pardon's theorem (a locally flat surface).  The
*sibling's use* of its statement (`Work.Smooth.PushThrough3D.pinchedPushThrough_standard`) is at
`F = standardTorus.carrier`, which *is* locally flat (`Work.Smooth.PushThrough3D.torus_locallyFlat`),
so the instance used is sound even though the general statement is not; the reduction below avoids
the false statement altogether by using the corrected hypothesis.

## Non-vacuity

The hypothesis is satisfiable *with* the conclusion, in a configuration in which the disc genuinely
crosses the surface:

* `Work.Collar3D.pinchedSurgery_hypotheses_satisfiable` — a configuration (plane `nvPlane`,
  paraboloid `nvE`, sub-disc `nvBeta`, crossing circle `nvGamma`, `C = ∅`) satisfying **every**
  hypothesis, including `LocallyFlatSet nvPlane`;
* `Work.Collar3D.not_forall_interior_off_nvPlane` — there the identity homeomorphism does *not*
  realise the conclusion;
* **`Work.Collar3D.pinchedSurgery_realised`** — there the conclusion *is* realised by the explicit
  shear `nvShearHomeo`;
* `Work.Smooth.PushThrough3D.pinchedSurgery_instance` — another explicit configuration (the sibling
  chapter's);
* the fixed statement is used at `Work.CoreTopology.standard`, where local flatness is *proved*
  (`Work.Smooth.PushThrough3D.torus_locallyFlat`).

## Conventions

`Disc = 𝔻 = Metric.closedBall (0 : ℂ) 1` (the model disc `Work.Smooth.Jordan.Disc`), and
`circlePoint θ = e^{iθ}` is the boundary parametrisation `Work.Smooth.Jordan.circlePoint`.
-/

open Set

namespace Work.Collar3D

noncomputable section

/-- **Pardon's global push-through (the pinched surgery)**, in `ℝ³` alone, for a **locally flat**
surface.

Let `F ⊆ ℝ³` be a locally flat surface, `e : 𝔻 → ℝ³` an embedded disc and `β : 𝔻 → ℝ³` an embedded
sub-disc of its image whose boundary curve `γ` lies on `F`, whose interior misses `F`, and which
bounds a disc `Σ ⊆ F` of the surface (so `γ` is *inessential* in `F`).  Let `C ⊆ ℝ³` be compact and
disjoint from the closed sub-disc `β(𝔻)`, and assume the *innermost clause*: every interior point of
`e` which meets `F` already lies on `γ` or in `C`.

Then there is a homeomorphism `H` of `ℝ³` which fixes the boundary curve of `e` pointwise, fixes
`C` pointwise, and pushes the interior of `e` through `F`: `H (e z) ∈ F` for an interior `z` only
if `H (e z) ∈ C`.

The classical content is Alexander's theorem (the sphere `β ∪ Σ` bounds a ball) together with the
isotopy extension theorem.

The local-flatness hypothesis is **necessary**: without it the statement is refuted by the
counterexample recorded in `Submission/Work/Collar3D/README.md`, §5ter (and *is* the hypothesis that
the sibling's `Work.Smooth.PushThrough3D.PinchedSurgeryInput` omits). -/
def PinchedSurgery : Prop :=
  ∀ (F : Set R3), Work.Smooth.PushThrough3D.LocallyFlatSet F →
  ∀ (e β : C(Disc, R3)) (γ : ℝ → R3) (C : Set R3),
    Function.Injective e →
    Function.Injective β →
    Set.range (fun z : Disc => β z) ⊆ Set.range (fun z : Disc => e z) →
    (∀ θ : ℝ, β (Work.Smooth.Jordan.circlePoint θ) = γ θ) →
    (∀ z : Disc, ‖(z : ℂ)‖ < 1 → β z ∉ F) →
    (∃ Sig : C(Disc, R3),
      (∀ θ : ℝ, Sig (Work.Smooth.Jordan.circlePoint θ) = γ θ) ∧ ∀ z : Disc, Sig z ∈ F) →
    (∀ z : Disc, ‖(z : ℂ)‖ < 1 → e z ∈ F → e z ∈ C ∨ e z ∈ Set.range γ) →
    IsCompact C →
    Disjoint C (Set.range (fun z : Disc => β z)) →
    ∃ H : R3 ≃ₜ R3,
      (∀ θ : ℝ, H (e (Work.Smooth.Jordan.circlePoint θ))
        = e (Work.Smooth.Jordan.circlePoint θ)) ∧
      (∀ x ∈ C, H x = x) ∧
      (∀ z : Disc, ‖(z : ℂ)‖ < 1 → H (e z) ∈ F → H (e z) ∈ C)

end

end Work.Collar3D
