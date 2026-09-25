import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.SigmaCompPairDefs
import Submission.Work.BourgainPlan.IonescuWainger.sigmaComp_repr_count
import Submission.Work.BourgainPlan.IonescuWainger.sigmaA_exists_unique_add
import Submission.Work.BourgainPlan.IonescuWainger.ArcCRT

namespace Work.BourgainPlan.IonescuWainger

open Finset

/-! ## Three small bridges between the `Finset` and `Set` arc vocabulary -/

/-- Every point listed in the `Finset` `sigmaAFinset A` of points of *exact* denominator `Q_A`
lies in the `Set` `sigmaA A`.  (The converse needs `0 ∉ A`, see `coe_sigmaAFinset`.) -/
lemma sigmaAFinset_mem_sigmaA {A : Finset ℕ} {x : Circle} (hx : x ∈ sigmaAFinset A) :
    x ∈ sigmaA A := by
  rw [sigmaAFinset, Finset.mem_image] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨-, hcop⟩ := Finset.mem_filter.mp ha
  exact ⟨(a : ℤ), by simpa using hcop, rfl⟩

/-- **A point of the circle determines its exact denominator**: the sets `Σ_A` of points of exact
denominator `Q_A`, for `A` ranging over the subsets of a pairwise coprime set `S` of integers
`≥ 2`, are pairwise disjoint, so a point lying in `Σ_A` and in `Σ_B` has `A = B`. -/
lemma eq_of_mem_sigmaA {S A B : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA : A ⊆ S) (hB : B ⊆ S) {x : Circle} (hxA : x ∈ sigmaA A) (hxB : x ∈ sigmaA B) :
    A = B := by
  by_contra hne
  exact (Set.disjoint_left.mp (sigmaA_disjoint h2 hS hA hB hne) hxA) hxB

/-- **The exact denominator of a decomposition.**  If `β = (β - α) + α` with `β - α ∈ Σ_{A₀}` and
`α ∈ Σ_{A₁}`, where `A₀, A₁ ⊆ S` are disjoint, then `β ∈ Σ_{A₀ ∪ A₁}`. -/
lemma mem_sigmaA_union_of_compl {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A₀ A₁ : Finset ℕ} (hA₀ : A₀ ⊆ S) (hA₁S : A₁ ⊆ S) (hdisj : Disjoint A₀ A₁)
    {α β : Circle} (hα : α ∈ sigmaA A₁) (hβ : β - α ∈ sigmaA A₀) :
    β ∈ sigmaA (A₀ ∪ A₁) := by
  have h1 : (β - α) + α = β := sub_add_cancel β α
  rw [← h1]
  exact sigmaA_add_mem h2 hS hA₀ hA₁S hdisj hβ hα

/-! ## Tao's `2^k` counting bound for the pairs `(A₀, α)` -/

/-- **The exact denominator set of `β` is common to all the decompositions of `β` carried by pairs
of `sigmaCompPairSetFilter`.**  Concretely, if `sigmaCompPairSetFilter S k β` is nonempty then there
is a set `B ⊆ S` with `B.card ≤ k` such that every pair `(A₀, α)` of the filtered set has
`A₀ ⊆ B`: take `B = A₀ ∪ A₁` for one admissible pair, where `A₁` is the set with `α ∈ Σ_{A₁}`.

Indeed each admissible pair yields `β ∈ Σ_{A₀} + Σ_{A₁} ⊆ Σ_{A₀ ∪ A₁}`, so `β` has exact
denominator `Q_{A₀ ∪ A₁}` (in the sense that it lies in `Σ_{A₀ ∪ A₁}`), and the sets `Σ_C` of points
of exact denominator `Q_C` are pairwise disjoint (`sigmaA_disjoint`). -/
theorem exists_common_denomSet {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) (k : ℕ) (β : Circle) :
    ∃ B : Finset ℕ, B.card ≤ k ∧ ∀ p ∈ sigmaCompPairSetFilter S k β, p.1 ⊆ B := by
  classical
  by_cases hne : (sigmaCompPairSetFilter S k β).Nonempty
  · obtain ⟨p₀, hp₀⟩ := hne
    obtain ⟨A₀, α₀⟩ := p₀
    have hp₀pair : (A₀, α₀) ∈ sigmaCompPairSet S k := (mem_sigmaCompPairSetFilter.mp hp₀).1
    have hβ₀ : β - α₀ ∈ sigmaA A₀ := (mem_sigmaCompPairSetFilter.mp hp₀).2
    obtain ⟨hA₀sub, hA₀card, hα₀union⟩ := mem_sigmaCompPairSet.mp hp₀pair
    rw [Finset.mem_biUnion] at hα₀union
    obtain ⟨A₁, hA₁mem, hα₀A₁⟩ := hα₀union
    rw [Finset.mem_filter, Finset.mem_powerset] at hA₁mem
    obtain ⟨hA₁sub, hA₁card⟩ := hA₁mem
    have hA₁S : A₁ ⊆ S := hA₁sub.trans Finset.sdiff_subset
    have hdisj₀ : Disjoint A₀ A₁ :=
      Finset.disjoint_left.mpr fun q hq₀ hq₁ => (Finset.mem_sdiff.mp (hA₁sub hq₁)).2 hq₀
    have hα₀S : α₀ ∈ sigmaA A₁ := sigmaAFinset_mem_sigmaA hα₀A₁
    have hB₀ : β ∈ sigmaA (A₀ ∪ A₁) :=
      mem_sigmaA_union_of_compl h2 hS hA₀sub hA₁S hdisj₀ hα₀S hβ₀
    have hBcard : (A₀ ∪ A₁).card ≤ k := by
      rw [Finset.card_union_of_disjoint hdisj₀]
      omega
    refine ⟨A₀ ∪ A₁, hBcard, ?_⟩
    intro p hp
    obtain ⟨A, γ⟩ := p
    have hp_pair : (A, γ) ∈ sigmaCompPairSet S k := (mem_sigmaCompPairSetFilter.mp hp).1
    have hβ : β - γ ∈ sigmaA A := (mem_sigmaCompPairSetFilter.mp hp).2
    obtain ⟨hAsub, hAcard, hγunion⟩ := mem_sigmaCompPairSet.mp hp_pair
    rw [Finset.mem_biUnion] at hγunion
    obtain ⟨A₂, hA₂mem, hγA₂⟩ := hγunion
    rw [Finset.mem_filter, Finset.mem_powerset] at hA₂mem
    obtain ⟨hA₂sub, hA₂card⟩ := hA₂mem
    have hA₂S : A₂ ⊆ S := hA₂sub.trans Finset.sdiff_subset
    have hdisj : Disjoint A A₂ :=
      Finset.disjoint_left.mpr fun q hq hq₂ => (Finset.mem_sdiff.mp (hA₂sub hq₂)).2 hq
    have hγS : γ ∈ sigmaA A₂ := sigmaAFinset_mem_sigmaA hγA₂
    have hβA : β ∈ sigmaA (A ∪ A₂) :=
      mem_sigmaA_union_of_compl h2 hS hAsub hA₂S hdisj hγS hβ
    have heq : A ∪ A₂ = A₀ ∪ A₁ :=
      eq_of_mem_sigmaA h2 hS (Finset.union_subset hAsub hA₂S)
        (Finset.union_subset hA₀sub hA₁S) hβA hB₀
    intro q hq
    rw [← heq]
    exact Finset.mem_union_left _ hq
  · refine ⟨∅, by simp, ?_⟩
    intro p hp
    rw [Finset.not_nonempty_iff_eq_empty.mp hne] at hp
    exact absurd hp (Finset.notMem_empty p)

/-- **The first projection is injective on `sigmaCompPairSetFilter`.**  If two admissible pairs
`(A₀, α)` and `(A₀, α')` share their first component, they share their second one too: both
decompose `β` as `β = (β - α) + α` with `β - α ∈ Σ_{A₀}` and `α ∈ Σ_{A₁}` for the same `A₁`
(forced by the disjointness of the exact-denominator sets), and the decomposition of `β` into
`Σ_{A₀} + Σ_{A₁}` is unique (`sigmaA_exists_unique_add`). -/
theorem fst_injOn_filter {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) (k : ℕ) (β : Circle) :
    Set.InjOn Prod.fst (sigmaCompPairSetFilter S k β : Set (Finset ℕ × Circle)) := by
  classical
  intro p hp q hq hpq
  obtain ⟨A, α⟩ := p
  obtain ⟨B, γ⟩ := q
  have hAB : A = B := hpq
  subst hAB
  have hp_pair : (A, α) ∈ sigmaCompPairSet S k := (mem_sigmaCompPairSetFilter.mp hp).1
  have hβA : β - α ∈ sigmaA A := (mem_sigmaCompPairSetFilter.mp hp).2
  obtain ⟨hAsub, hAcard, hαunion⟩ := mem_sigmaCompPairSet.mp hp_pair
  rw [Finset.mem_biUnion] at hαunion
  obtain ⟨A₂, hA₂mem, hαA₂⟩ := hαunion
  rw [Finset.mem_filter, Finset.mem_powerset] at hA₂mem
  obtain ⟨hA₂sub, hA₂card⟩ := hA₂mem
  have hA₂S : A₂ ⊆ S := hA₂sub.trans Finset.sdiff_subset
  have hdisjA₂ : Disjoint A A₂ :=
    Finset.disjoint_left.mpr fun r hr hr₂ => (Finset.mem_sdiff.mp (hA₂sub hr₂)).2 hr
  have hαA₂S : α ∈ sigmaA A₂ := sigmaAFinset_mem_sigmaA hαA₂
  have hβu : β ∈ sigmaA (A ∪ A₂) :=
    mem_sigmaA_union_of_compl h2 hS hAsub hA₂S hdisjA₂ hαA₂S hβA
  have hq_pair : (A, γ) ∈ sigmaCompPairSet S k := (mem_sigmaCompPairSetFilter.mp hq).1
  have hβγ : β - γ ∈ sigmaA A := (mem_sigmaCompPairSetFilter.mp hq).2
  obtain ⟨hAsub', hAcard', hγunion⟩ := mem_sigmaCompPairSet.mp hq_pair
  rw [Finset.mem_biUnion] at hγunion
  obtain ⟨A₂', hA₂'mem, hγA₂'⟩ := hγunion
  rw [Finset.mem_filter, Finset.mem_powerset] at hA₂'mem
  obtain ⟨hA₂'sub, hA₂'card⟩ := hA₂'mem
  have hA₂'S : A₂' ⊆ S := hA₂'sub.trans Finset.sdiff_subset
  have hdisjA₂' : Disjoint A A₂' :=
    Finset.disjoint_left.mpr fun r hr hr₂ => (Finset.mem_sdiff.mp (hA₂'sub hr₂)).2 hr
  have hγA₂'S : γ ∈ sigmaA A₂' := sigmaAFinset_mem_sigmaA hγA₂'
  have hβu' : β ∈ sigmaA (A ∪ A₂') :=
    mem_sigmaA_union_of_compl h2 hS hAsub' hA₂'S hdisjA₂' hγA₂'S hβγ
  have heqU : A ∪ A₂ = A ∪ A₂' :=
    eq_of_mem_sigmaA h2 hS (Finset.union_subset hAsub hA₂S)
      (Finset.union_subset hAsub' hA₂'S) hβu hβu'
  have hA₂eq : A₂ = A₂' := by
    have e1 : A₂ = (A ∪ A₂) \ A := by
      ext r
      rw [Finset.mem_sdiff, Finset.mem_union]
      exact ⟨fun hr => ⟨Or.inr hr, fun hrA => Finset.disjoint_left.mp hdisjA₂ hrA hr⟩,
        fun h => h.1.elim (fun hrA => absurd hrA h.2) id⟩
    have e2 : A₂' = (A ∪ A₂') \ A := by
      ext r
      rw [Finset.mem_sdiff, Finset.mem_union]
      exact ⟨fun hr => ⟨Or.inr hr, fun hrA => Finset.disjoint_left.mp hdisjA₂' hrA hr⟩,
        fun h => h.1.elim (fun hrA => absurd hrA h.2) id⟩
    rw [e1, e2, heqU]
  have huniq := sigmaA_exists_unique_add h2 hS hAsub hA₂S hdisjA₂ hβu
  have hpair : (β - α, α) = (β - γ, γ) :=
    huniq.unique ⟨hβA, hαA₂S, sub_add_cancel β α⟩
      ⟨hβγ, by rw [hA₂eq]; exact hγA₂'S, sub_add_cancel β γ⟩
  have hαγ : α = γ := by
    have := congrArg Prod.snd hpair
    simpa using this
  exact Prod.ext rfl hαγ

/-- Tao's `2^k` counting bound for the pairs `(A₀, α)` of his square function (arXiv:2008.05066,
proof of Theorem `ortho-apply`(ii)): for a fixed point `β` of the circle, at most `2^k` pairs
`(A₀, α)` with `A₀ ⊆ S`, `A₀.card ≤ k`, `α ∈ Σ_{(A₀)}` satisfy `β - α ∈ Σ_{A₀}`
(equivalently `β = α + α₀` with `α₀ ∈ Σ_{A₀}`). -/
theorem sigmaCompPairSet_filter_card_le {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) (k : ℕ) (β : Circle) :
    (sigmaCompPairSetFilter S k β).card ≤ 2 ^ k := by
  classical
  obtain ⟨B, hBcard, hBsub⟩ := exists_common_denomSet h2 hS k β
  have hinj := fst_injOn_filter h2 hS k β
  have hmain : (sigmaCompPairSetFilter S k β).card ≤ B.powerset.card :=
    Finset.card_le_card_of_injOn Prod.fst
      (fun p hp => Finset.mem_powerset.mpr (hBsub p hp))
      (fun p hp q hq hpq => hinj hp hq hpq)
  calc (sigmaCompPairSetFilter S k β).card
      ≤ B.powerset.card := hmain
    _ = 2 ^ B.card := Finset.card_powerset B
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hBcard

end Work.BourgainPlan.IonescuWainger
