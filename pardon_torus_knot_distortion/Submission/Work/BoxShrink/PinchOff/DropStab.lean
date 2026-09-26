import Submission.Work.BoxShrink.PinchOff.Stabilizer
import Submission.Work.BoxShrink.PinchOff.Drop

/-!
# The residual `DropCase` in the vocabulary of the lifted components

`Stabilizer.lean` proves the dictionary

> `WindingSpan P X = span_ℚ { (a,b) : some connected component of `X̃` is invariant under
> `z ↦ z + periodPt a b` }`.

This module reads the chapter's residual `DropCase` (the last obligation of the area, isolated in
`Drop.lean`, `keyTameClosed_iff_dropCase`) in that vocabulary:

* `dropCase_iff_span_invariantDirections` — `DropCase` is *exactly* the statement that at every
  configuration of the area the invariance directions of the lifted box region `Ω̃ = {B < s}`
  span a space of dimension at most one (`Ω̃` is never invariant under two independent lattice
  translations);
* `dropCase_of_liftedComponents_bounded` — a new discharged family: if the lifted components of
  `Ω̃` are bounded (the box region does not "wrap around" in the parameter plane), then
  `WindingSpan (Ω) = ⊥`, hence `DropCase` holds at that configuration.

The second is the abstract form of the parent chapter's "bounded components" case
(`IB/Main.lean`, case 2 of `windingSpan_bot_or_top_aux`), now available for an arbitrary region and
with no hypothesis on the structure of the boundary.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **`DropCase` is the statement that the lifted box region has no `2`-dimensional wrapping.**

By the dictionary `windingSpan_eq_span_invariantDirections` the dimension bound
`finrank W(Ω) ≤ 1` is exactly: the lattice directions in which some connected component of the
lift `Ω̃ = Xtilde (surface ψ) (Omega ψ s c σ)` is invariant span a space of dimension `≤ 1`. -/
theorem dropCase_iff_span_invariantDirections :
    DropCase ↔
      ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
        Work.BoxShrink.Pinch.TransverseSlice ψ s c σ u → TameClosedSlice ψ s c σ u →
        ¬ (surface ψ).ContainsEssentialLoop (SphereTrace s c σ) →
        ¬ (surface ψ).ContainsEssentialLoop (Sigma ψ s c σ u) →
        Work.SurgeryInvariance.WindingSpan (surface ψ) (Halves ψ s c σ u) = ⊥ →
        Module.finrank ℚ
          ↥(Submodule.span ℚ {v : ℚ × ℚ |
            ∃ a b : ℤ, v = ((a : ℚ), (b : ℚ)) ∧
              ComponentInvariant (surface ψ) (Omega ψ s c σ) a b}) ≤ 1 := by
  have hopen : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Work.SurgeryInvariance.IsOpenInCarrier (surface ψ) (Omega ψ s c σ) :=
    fun ψ s c σ => Work.BoxShrink.Core.isOpenInCarrier_boxRegion (surface ψ) s c σ
  have hsub : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Omega ψ s c σ ⊆ (surface ψ).carrier := fun ψ s c σ _ hx => hx.1
  constructor
  · intro h ψ s c σ u hT hTa hS hZ hbot
    rw [← windingSpan_eq_span_invariantDirections (hsub ψ s c σ) (hopen ψ s c σ)]
    exact h ψ s c σ u hT hTa hS hZ hbot
  · intro h ψ s c σ u hT hTa hS hZ hbot
    rw [windingSpan_eq_span_invariantDirections (hsub ψ s c σ) (hopen ψ s c σ)]
    exact h ψ s c σ u hT hTa hS hZ hbot

/-- **A new discharged family of `DropCase`**: if the lifted components of the box region are
bounded — the box region is "small" in the parameter plane, i.e. it does not wrap around the
torus — then the box region carries no essential loop at all, so the dimension bound holds. -/
theorem dropCase_of_liftedComponents_bounded
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)),
      ∀ z : ℂ, Bornology.IsBounded
        (connectedComponentIn (Xtilde (surface ψ) (Omega ψ s c σ)) z)) : DropCase := by
  intro ψ s c σ u _hT _hTa _hS _hZ _hbot
  have hzero : Work.SurgeryInvariance.WindingSpan (surface ψ) (Omega ψ s c σ) = ⊥ :=
    windingSpan_eq_bot_of_components_bounded (P := surface ψ) (X := Omega ψ s c σ)
      (fun _ hx => hx.1) (Work.BoxShrink.Core.isOpenInCarrier_boxRegion (surface ψ) s c σ)
      (h ψ s c σ)
  rw [hzero, finrank_bot]
  omega

/-- **The same conclusion for the parent formulation**: a configuration whose lifted box-region
components are bounded satisfies the conclusion of Pardon's Lemma 3 automatically (the box region
is inessential, so one of the half-regions is not needed at all). -/
theorem keyTameClosed_of_liftedComponents_bounded
    (h : ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)),
      ∀ z : ℂ, Bornology.IsBounded
        (connectedComponentIn (Xtilde (surface ψ) (Omega ψ s c σ)) z)) : KeyTameClosed :=
  keyTameClosed_of_dropCase (dropCase_of_liftedComponents_bounded h)

end

end Work.BoxShrink.PinchOff
