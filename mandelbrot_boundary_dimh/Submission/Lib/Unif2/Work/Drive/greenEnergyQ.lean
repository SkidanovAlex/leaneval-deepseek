import Mathlib
import Submission.Lib.Unif2.Work.Drive.EnergyCover

/-!
# Towards (Q): the telescoping identity for the surface Dirichlet pairing

This module collects the two *linearity* bricks that the proof of
`Work.Drive.pairing_harmonic_zero` (the "**(Q)**" of
`Submission/Work/Drive/NOTES_greenSymmetryRegion_route.md`, Appendix 6) needs on top of
`Work.Drive.pairTerm_add`:

* `Work.Drive.clampedPullback_finset_sum` — the clamped pullback of a finite sum is the finite sum of
  the clamped pullbacks;
* `Work.Drive.pairTerm_finset_sum` — `pairTerm` is additive in its fifth argument over finite sums;
* `Work.Drive.pairing_finset_sum` — the same for the surface pairing `pairing`.

They are the tools that turn `pairing y ρ σ ψ f φ` into the double sum
`∑ k, ∑ i, pairTerm (y i) (ρ i) (σ i) (ψ i) f (ψ k * φ)`, after which each summand is transferred to
chart `k` (with the bump `β k` of the `EnergyCover` making `pairTerm_transfer` applicable) and the
inner sum telescopes to `pairTerm (y k) (ρ k) (σ k) β k f (ψ k * φ)`.
-/

open MeasureTheory Set Filter
open scoped Manifold Topology Gradient

noncomputable section

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The clamped pullback of a finite sum of *functions* is the finite sum of the clamped
pullbacks. -/
theorem clampedPullback_finset_sum {ι : Type*} (s : Finset ι) (x : X) (ρ : ℝ)
    (v : ι → X → ℝ) :
    clampedPullback x ρ (s.sum v) = s.sum (fun i => clampedPullback x ρ (v i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, clampedPullback_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, clampedPullback_add, ih]

/-! ### The remaining bricks (statement only; proofs to be written)

`pairTerm x ρ σ ψ f χ` is additive in `χ` (`Work.Drive.pairTerm_add` is already proved for two
summands), so the finite-sum version follows by induction *provided* one keeps track of the
integrability of the intermediate sums; the clean way to state it is

```
theorem pairTerm_finset_sum {ι : Type*} (s : Finset ι) {x : X} {ρ σ : ℝ} {ψ f : X → ℝ}
    {χ : ι → X → ℝ}
    (h₁ : ∀ i ∈ s, ∀ᵐ z ∂(volume : Measure ℂ),
      DifferentiableAt ℝ (clampedPullback x ρ (χ i)) z)
    (h₂ : ∀ i ∈ s, PairIntegrable x ρ σ ψ f (χ i))
    (h₃ : PairIntegrable x ρ σ ψ f (∑ i in s, χ i)) :
    pairTerm x ρ σ ψ f (∑ i in s, χ i) = ∑ i in s, pairTerm x ρ σ ψ f (χ i)
```

and then, summing over the chart index,

```
theorem pairing_finset_sum ... :
    pairing y ρ σ ψ f (∑ i in s, χ i) = ∑ i in s, pairing y ρ σ ψ f (χ i)
```

With both in hand the proof of `Work.Drive.pairing_harmonic_zero` (statement in Appendix 6b of
`NOTES_greenSymmetryRegion_route.md`) is the five-step telescoping described there. -/

end Work.Drive
