import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.StrataFinsetDefs
import Submission.Work.BourgainPlan.IonescuWainger.indicator_sigmaStrataFinset_incl_excl

/-!
# The index set of Tao's square function in the *strata* convention

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4,
Theorem `ortho-apply`(ii) (the Rubio de Francia estimate).

Tao's square function is indexed by the pairs `(A₀, α)` with `A₀ ∈ binom(S, ≤ k)` and
`α ∈ Σ_{(A₀)} = ⋃_{A ∈ binom(S∖A₀, ≤ k−|A₀|)} Σ_A`, where

`Σ_A = Σ_{⊆ A} \ ⋃_{B ⊊ A} Σ_{⊆ B}`  (Tao's *strata*, `sigmaStrataFinset` in the corpus)

and the operator attached to the pair is the modulated multiplier `Op_{φ; α + Σ_{A₀}}`
(the symbol supported on the translate `α + Σ_{A₀} + [-ε,ε]`).

**Convention warning.**  `ArcFinsetDefs.sigmaAFinset A` is the set of points of *exact* denominator
`Q_A` (`gcd(a,Q_A) = 1`), which for composite elements of `S` is *strictly smaller* than Tao's
stratum `Σ_A` (e.g. `S = {4}` gives `1/2 ∈ Σ_{{4}}` but `1/2 ∉ sigmaAFinset {4}`).  The two agree
when every element of `S` is squarefree.  Tao's `ortho-apply`(ii) needs the strata; the
`p = 2` endpoint of `IonescuWainger/opArc_l2.lean` was stated with `sigmaAFinset`, so a
strata-convention version is required for the assembly (this file's companions).

This file only *defines* the index sets (for the circle): `strataCompFinset S k A₀` is
`Σ_{(A₀)}`, and `strataCompPairSet S k` is the set of pairs `(A₀, α)`, together with the
"What decomposes a fixed `β`" filter `strataCompPairSetFilter` whose cardinality Tao bounds by
`2 ^ k`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- **Tao's `Σ_{(A₀)} = ⋃_{A ∈ binom(S∖A₀, ≤ k−|A₀|)} Σ_A`** in the strata convention: the union of
the strata `sigmaStrataFinset A` over all subsets `A ⊆ S \ A₀` of cardinality at most `k - |A₀|`. -/
noncomputable def strataCompFinset (S : Finset ℕ) (k : ℕ) (A₀ : Finset ℕ) : Finset Circle :=
  ((S \ A₀).powerset.filter (fun A => A.card ≤ k - A₀.card)).biUnion
    (fun A => sigmaStrataFinset A)

/-- **The index set of Tao's square function at height `k`** in the strata convention: the pairs
`(A₀, α)` with `A₀ ⊆ S`, `A₀.card ≤ k` and `α ∈ Σ_{(A₀)} = strataCompFinset S k A₀`. -/
noncomputable def strataCompPairSet (S : Finset ℕ) (k : ℕ) : Finset (Finset ℕ × Circle) :=
  ((S.powerset.filter (fun A₀ => A₀.card ≤ k)).sigma
    (fun A₀ => strataCompFinset S k A₀)).image (fun p => (p.1, p.2))

/-- Membership in `Σ_{(A₀)}`. -/
theorem mem_strataCompFinset {S : Finset ℕ} {k : ℕ} {A₀ : Finset ℕ} {β : Circle} :
    β ∈ strataCompFinset S k A₀ ↔
      ∃ A ∈ (S \ A₀).powerset.filter (fun A => A.card ≤ k - A₀.card),
        β ∈ sigmaStrataFinset A := by
  classical
  rw [strataCompFinset, Finset.mem_biUnion]

/-- Membership in the index set of the square function. -/
theorem mem_strataCompPairSet {S : Finset ℕ} {k : ℕ} {A₀ : Finset ℕ} {α : Circle} :
    (A₀, α) ∈ strataCompPairSet S k ↔ A₀ ⊆ S ∧ A₀.card ≤ k ∧ α ∈ strataCompFinset S k A₀ := by
  classical
  rw [strataCompPairSet, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hpq⟩
    rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    obtain ⟨rfl, rfl⟩ : p.1 = A₀ ∧ p.2 = α := by
      simpa using Prod.ext_iff.mp hpq
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨A₀, α⟩, by
      rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨⟨h1, h2⟩, h3⟩, rfl⟩

/-- The pairs of the index set that **decompose a fixed point** `β`: the pair `(A₀, α)` is counted
when `β - α ∈ Σ_{A₀}`, i.e. `β = α + α₀` with `α₀ ∈ Σ_{A₀}`.  Tao's counting bound
(`ortho-apply`(ii), `p = 2` case) is that this set has at most `2 ^ k` elements. -/
noncomputable def strataCompPairSetFilter (S : Finset ℕ) (k : ℕ) (β : Circle) :
    Finset (Finset ℕ × Circle) :=
  (strataCompPairSet S k).filter (fun p => β - p.2 ∈ sigmaStrataFinset p.1)

/-- Membership in `strataCompPairSetFilter`. -/
theorem mem_strataCompPairSetFilter {S : Finset ℕ} {k : ℕ} {β : Circle}
    {p : Finset ℕ × Circle} :
    p ∈ strataCompPairSetFilter S k β ↔
      p ∈ strataCompPairSet S k ∧ β - p.2 ∈ sigmaStrataFinset p.1 := by
  classical
  rw [strataCompPairSetFilter, Finset.mem_filter]

/-- `Σ_{≤ k} = ⋃_{A ∈ binom(S,≤k)} Σ_{⊆ A}` as a `Finset` of the circle (strata convention: the
union of the torsion subgroups). -/
noncomputable def sigmaLeFinset (S : Finset ℕ) (k : ℕ) : Finset Circle :=
  (S.powerset.filter (fun A => A.card ≤ k)).biUnion (fun A => sigmaSubAFinset A)

end Work.BourgainPlan.IonescuWainger
