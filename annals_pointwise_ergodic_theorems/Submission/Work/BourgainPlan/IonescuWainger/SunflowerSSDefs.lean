import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.TaoDefs

/-!
# The "strong sunflower" condition on tuples, and the counting vocabulary of Tao's §3

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066,
§3 (`sunflower-sec`), Corollary `sunsquare`.

Tao's sunflower bound compares the `r`-th power of the total mass of a weight `w` on `k`-element
sets with the sum of `∏_{i} w (A₀ ∪ A_i)` over tuples `(A₀, A_1, …, A_r)` whose members
`A₀ ∪ A_1, …, A₀ ∪ A_r` form a sunflower with core `A₀`.  The individual summands of that second
sum are exactly the `r`-tuples of `k`-sets `X_0, …, X_{r-1}` that possess a common core contained
in every member whose petals are pairwise disjoint — i.e. Tao's `nonceflower`(ii) sunflowers
(including degenerate ones such as the constant tuple).  This file fixes that notion and the
elementary facts about it used by the proof of `sunflower_square_function`.

All results are stated for a general finite `α`, a general `k` and a general `r`, so that they are
reusable harmonic-analysis bookkeeping rather than ad hoc.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- A tuple `X : Fin r → Finset α` is a **sunflower of `k`-sets**: every member has cardinality
`k` and there is a set `A₀` contained in every member such that all the pairwise intersections
`X i ∩ X j` (`i ≠ j`) are equal to `A₀`.

For tuples of pairwise *distinct* sets this is precisely Tao's notion `nonceflower`(ii) of a
sunflower with core `A₀` (the pairwise intersection of a sunflower is its core); the condition is
also well defined for tuples with repeated entries — e.g. the constant tuple `(X, …, X)` is an
`IsSS` sunflower with core `X`.  See `isSS_iff_isSunflower` for the equivalence with
`IsSunflower` (petals pairwise disjoint) when all members have cardinality `k`. -/
def IsSS {α : Type*} [DecidableEq α] (k : ℕ) {r : ℕ} (X : Fin r → Finset α) : Prop :=
  (∀ i, (X i).card = k) ∧
    ∃ A₀ : Finset α, (∀ i, A₀ ⊆ X i) ∧ ∀ i j : Fin r, i ≠ j → X i ∩ X j = A₀

/-- `IsSS` is decidable on a finite `α` (this is what makes the sums in
`sunflower_square_function` meaningful without a `classical` assumption in the statement). -/
instance instDecidableIsSS {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ) {r : ℕ}
    (X : Fin r → Finset α) : Decidable (IsSS k X) := by
  unfold IsSS
  infer_instance

/-- The core of an `IsSS` tuple is unique as soon as there are two distinct indices. -/
theorem IsSS.core_unique {α : Type*} [DecidableEq α] {r : ℕ} {X : Fin r → Finset α}
    {A₀ B₀ : Finset α} (hA : ∀ i j : Fin r, i ≠ j → X i ∩ X j = A₀)
    (hB : ∀ i j : Fin r, i ≠ j → X i ∩ X j = B₀) {i₀ i₁ : Fin r} (h01 : i₀ ≠ i₁) :
    A₀ = B₀ := by
  have h := hA i₀ i₁ h01
  rw [hB i₀ i₁ h01] at h
  exact h.symm

/-- A member of an `IsSS` tuple has cardinality `k`. -/
theorem IsSS.card_eq {α : Type*} [DecidableEq α] {k r : ℕ} {X : Fin r → Finset α}
    (h : IsSS k X) (i : Fin r) : (X i).card = k := h.1 i

/-- Permuting the petals of an `IsSS` sunflower leaves it an `IsSS` sunflower. -/
theorem IsSS.comp_perm {α : Type*} [DecidableEq α] {k r : ℕ} {X : Fin r → Finset α}
    (h : IsSS k X) (σ : Equiv.Perm (Fin r)) : IsSS k (X ∘ σ) := by
  obtain ⟨hcard, A₀, hsub, hint⟩ := h
  exact ⟨fun i => hcard (σ i), A₀, fun i => hsub (σ i),
    fun i j hij => hint (σ i) (σ j) (fun h => hij (σ.injective h))⟩

/-- Every `IsSS` tuple is a sunflower in Tao's sense `nonceflower`(ii). -/
theorem IsSS.isSunflower {α : Type*} [DecidableEq α] {k r : ℕ} {X : Fin r → Finset α}
    (h : IsSS k X) : IsSunflower X := by
  obtain ⟨-, A₀, hsub, hint⟩ := h
  refine ⟨A₀, hsub, fun i j hij => ?_⟩
  rw [Finset.disjoint_left]
  intro x hxi hxj
  obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hxi
  obtain ⟨h3, h4⟩ := Finset.mem_sdiff.mp hxj
  have hx : x ∈ X i ∩ X j := Finset.mem_inter.mpr ⟨h1, h3⟩
  rw [hint i j hij] at hx
  exact h4 hx

/-- Conversely, a sunflower (petals pairwise disjoint, common core contained in every member) all
of whose members have cardinality `k` is an `IsSS` tuple.  This is the passage from the
combinatorial hypothesis `hsun` of `sunflower_square_function` to `IsSS`. -/
theorem isSS_of_isSunflower {α : Type*} [DecidableEq α] {k r : ℕ} {X : Fin r → Finset α}
    (hcard : ∀ i, (X i).card = k) (h : IsSunflower X) : IsSS k X := by
  obtain ⟨A₀, hsub, hdisj⟩ := h
  refine ⟨hcard, A₀, hsub, fun i j hij => ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨hxi, hxj⟩ := Finset.mem_inter.mp hx
    by_contra hxA
    exact Finset.disjoint_left.mp (hdisj i j hij) (Finset.mem_sdiff.mpr ⟨hxi, hxA⟩)
      (Finset.mem_sdiff.mpr ⟨hxj, hxA⟩)
  · intro hx
    exact Finset.mem_inter.mpr ⟨hsub i hx, hsub j hx⟩

/-- The two notions coincide. -/
theorem isSS_iff_isSunflower {α : Type*} [DecidableEq α] {k r : ℕ} {X : Fin r → Finset α}
    (hcard : ∀ i, (X i).card = k) : IsSS k X ↔ IsSunflower X :=
  ⟨IsSS.isSunflower, isSS_of_isSunflower hcard⟩

end Work.BourgainPlan.IonescuWainger
