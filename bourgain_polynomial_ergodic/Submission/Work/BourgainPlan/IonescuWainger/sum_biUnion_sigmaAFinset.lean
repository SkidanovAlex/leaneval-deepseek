import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.coe_sigmaAFinset
import Submission.Work.BourgainPlan.IonescuWainger.ArcCRT

/-!
# Summing over the union of a family of exact-denominator arc sets

Tao's major arc system is `f_{Σ_A} = Σ_{α ∈ Σ_A} f_α`, a sum over the (finite) set of arc points of
*exact* denominator `Q_A`.  When a further sum is taken over a family `(A)_{A ∈ F}` of subsets of
`S`, the natural index set is `⋃_{A ∈ F} Σ_A = F.biUnion sigmaAFinset`, and one needs to know that
this sum splits as the iterated sum `Σ_{A ∈ F} Σ_{α ∈ Σ_A} f_α`.

That is exactly what this file records: for `S` a finite set of pairwise coprime integers `≥ 2`
(so that, by `ArcCRT.lean`, the `Σ_A = sigmaA A` are pairwise disjoint for distinct `A ⊆ S`), the
`Finset`-level sum over the `biUnion` of the `sigmaAFinset A` is the iterated sum.  The bridge from
the `Finset` version `sigmaAFinset A` to the `Set` version `sigmaA A` is `coe_sigmaAFinset`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- **The `Finset`s `sigmaAFinset A` and `sigmaAFinset B` are disjoint for distinct `A ≠ B`
(subsets of a pairwise coprime set `S` of integers `≥ 2`).** -/
lemma disjoint_sigmaAFinset {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A B : Finset ℕ} (hA : A ⊆ S) (hB : B ⊆ S) (hAB : A ≠ B) :
    Disjoint (sigmaAFinset A) (sigmaAFinset B) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  have hA0 : 0 ∉ A := fun h => by have := h2 0 (hA h); omega
  have hB0 : 0 ∉ B := fun h => by have := h2 0 (hB h); omega
  have hxA : x ∈ sigmaA A := by
    rw [← coe_sigmaAFinset hA0, Finset.mem_coe]; exact hx
  have hxB : x ∈ sigmaA B := by
    rw [← coe_sigmaAFinset hB0, Finset.mem_coe]; exact hy
  exact Set.disjoint_left.mp (sigmaA_disjoint h2 hS hA hB hAB) hxA hxB

/-- **Summing over a union of exact-denominator arc sets.**  For a family `(A)_{A ∈ F}` of subsets
of a pairwise coprime set `S` of integers `≥ 2`, the sum over the `biUnion` of the arc sets
`Σ_A = sigmaAFinset A` is the iterated sum over the members of `F`. -/
theorem sum_biUnion_sigmaAFinset {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) {F : Finset (Finset ℕ)}
    (hF : ∀ A ∈ F, A ⊆ S) (f : Circle → ℤ → ℂ) (m : ℤ) :
    (∑ α ∈ F.biUnion sigmaAFinset, f α m) = ∑ A ∈ F, ∑ α ∈ sigmaAFinset A, f α m := by
  classical
  refine Finset.sum_biUnion ?_
  intro A hAF B hBF hne
  show Disjoint (sigmaAFinset A) (sigmaAFinset B)
  exact disjoint_sigmaAFinset h2 hS (hF A hAF) (hF B hBF) hne

end Work.BourgainPlan.IonescuWainger
