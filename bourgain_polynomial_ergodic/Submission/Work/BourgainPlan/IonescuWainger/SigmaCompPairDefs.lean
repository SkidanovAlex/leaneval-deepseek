import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ArcFinsetDefs
import Submission.Work.BourgainPlan.IonescuWainger.ArcDefs

/-!
# The index set of Tao's square function

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4,
Theorem `ortho-apply`(ii): the square function whose `ℓ^p` norm is bounded there is indexed by the
pairs `(A₀, α)` with `A₀ ∈ binom(S, ≤ k)` and `α ∈ Σ_{(A₀)}` (the *complementary* arc).  This file
records that index set as a `Finset` of pairs of the circle, together with its membership
characterisation. -/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- **The index set of Tao's square function at height `k`**: the pairs `(A₀, α)` with
`A₀ ⊆ S`, `A₀.card ≤ k` and `α ∈ Σ_{(A₀)} = ⋃_{A ⊆ S∖A₀, A.card ≤ k − A₀.card} Σ_A`
(the exact-denominator arcs). -/
noncomputable def sigmaCompPairSet (S : Finset ℕ) (k : ℕ) : Finset (Finset ℕ × Circle) :=
  (((S.powerset.filter (fun A => A.card ≤ k)).sigma fun A₀ =>
      ((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)).biUnion sigmaAFinset)).image
    (fun p => (p.1, p.2))

/-- Membership in `sigmaCompPairSet`. -/
theorem mem_sigmaCompPairSet {S : Finset ℕ} {k : ℕ} {A₀ : Finset ℕ} {α : Circle} :
    (A₀, α) ∈ sigmaCompPairSet S k ↔
      A₀ ⊆ S ∧ A₀.card ≤ k ∧
        α ∈ ((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)).biUnion sigmaAFinset := by
  classical
  simp only [sigmaCompPairSet, Finset.mem_image, Finset.mem_sigma, Finset.mem_filter,
    Finset.mem_powerset]
  constructor
  · rintro ⟨p, ⟨⟨h1, h2⟩, h3⟩, h4⟩
    simp only [Prod.mk.injEq] at h4
    obtain ⟨rfl, rfl⟩ := h4
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨A₀, α⟩, ⟨⟨h1, h2⟩, h3⟩, rfl⟩


/-- The pairs of `sigmaCompPairSet` that decompose a fixed point `β`: the pair `(A₀, α)` is counted
when `β - α ∈ Σ_{A₀}` (equivalently `β = α + α₀` with `α₀ ∈ Σ_{A₀}`).  This is the index set that
Tao's counting bound `2^k` bounds (arXiv:2008.05066, proof of Theorem `ortho-apply`(ii)). -/
noncomputable def sigmaCompPairSetFilter (S : Finset ℕ) (k : ℕ) (β : Circle) :
    Finset (Finset ℕ × Circle) := by
  classical
  exact (sigmaCompPairSet S k).filter (fun p => β - p.2 ∈ sigmaA p.1)

/-- Membership in `sigmaCompPairSetFilter`. -/
theorem mem_sigmaCompPairSetFilter {S : Finset ℕ} {k : ℕ} {β : Circle}
    {p : Finset ℕ × Circle} :
    p ∈ sigmaCompPairSetFilter S k β ↔ p ∈ sigmaCompPairSet S k ∧ β - p.2 ∈ sigmaA p.1 := by
  classical
  rw [sigmaCompPairSetFilter, Finset.mem_filter]

end Work.BourgainPlan.IonescuWainger
