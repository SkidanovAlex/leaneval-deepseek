import Submission.Work.NielsenPeel
import Submission.Work.AggregateCoordinate

open FreeGroup
set_option autoImplicit false

/-!
# Reaching a signed permutation: entry to the `aut_nielsen` reduction

`aut_nielsen` (Work/Nielsen.lean) needs, for every automorphism `α`, a
`γ ∈ AutClosure n` with `α·γ` a signed permutation
(`AssemblyBridge.aut_nielsen_of_reachable_signed`).  The classical reduction
on the basis images `w_i := α(a_i)` is organised as follows (the
*reachability subgoals*, in dependency order):

1. **Base case** — if every image has reduced length ≤ 1 then `α` is a signed
   permutation (terminal state; `γ = 1`).
2. **Letter choice (THIS FILE)** — otherwise (`∃ i, 1 < |w_i|`) some standard
   generator `a_m` has an *aggregate* expression `a_m = Γ_m(w_1,…,w_n)` with
   **≥ 2 factors**.  The aggregate is built from the inverse automorphism:
   `es_m := imageAggregateList α (α⁻¹(a_m)).toWord`, whose length is
   `|(α⁻¹(a_m)).toWord|`.  This file proves the length fact:
   `exists_two_factor_letter`.
3. **Aggregate analysis** — from the aggregate `es` (`es.prod = a_m`, image
   factors, `SystemReduced`, `2 ≤ es.length`) obtain a *confined* factor
   (`AggregateProtocol.aggregate_confined_factor`), hence (word-level
   `T3Rebalance.t3_aggregate_step`, element-translated) either a *strict*
   junction (a combination of two factors shorter than a constituent) or the
   *balanced* state (`AggregateProtocol.aggregate_balanced_element`).
4. **Coordinate attachment** — the strict case, and the balanced case via
   `AggregateCoordinate.balanced_closure_move_*`, produce `γ ∈ AutClosure n`
   with `N (α·γ) < N α` (strict) resp. `N (α·γ) ≤ N α` with the balanced
   position advanced (rebalancing phase).
5. **Termination / classification** — the lexicographic descent
   (`NielsenEnergy`, `RebalanceProtocol`) reaches the base case 1, where
   `SignedClosure` closes the membership.

This file contributes subgoal 2 (plus the small single-letter vocabulary of
subgoal 1).  All lemmas kernel-checked; axioms
`[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- An automorphism preserves inversion (as a function). -/
lemma aut_map_inv {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (x : FreeGroup (Fin n)) :
    α (x⁻¹) = (α x)⁻¹ := by
  exact map_inv (α : FreeGroup (Fin n) →* FreeGroup (Fin n)) x

/-- An automorphism preserves the identity. -/
lemma aut_map_one {n : ℕ} (α : MulAut (FreeGroup (Fin n))) : α 1 = 1 := by
  exact map_one (α : FreeGroup (Fin n) →* FreeGroup (Fin n))

/-- The norm is invariant under inversion: `|x⁻¹| = |x|`. -/
lemma norm_inv_eq {n : ℕ} {x : FreeGroup (Fin n)} :
    FreeGroup.norm (x⁻¹) = FreeGroup.norm x := by
  calc
    FreeGroup.norm (x⁻¹) = (x⁻¹).toWord.length := rfl
    _ = (FreeGroup.invRev x.toWord).length := by rw [FreeGroup.toWord_inv]
    _ = x.toWord.length := by rw [FreeGroup.invRev_length]
    _ = FreeGroup.norm x := rfl

/-- Distinct generators are not inverses of each other. -/
lemma of_ne_inv_of {n : ℕ} (m m' : Fin n) : FreeGroup.of m ≠ (FreeGroup.of m')⁻¹ := by
  intro h
  have hw := congrArg FreeGroup.toWord h
  rw [FreeGroup.toWord_of, FreeGroup.toWord_inv, FreeGroup.toWord_of] at hw
  have hrev : FreeGroup.invRev [(m', true)] = [(m', false)] := by
    rfl
  rw [hrev] at hw
  simp at hw

/-- A non-trivial element of reduced length at most 1 is a single generator
or its inverse. -/
lemma word_single_letter_of_le_one {n : ℕ} {x : FreeGroup (Fin n)} (hx : x ≠ 1)
    (hlen : FreeGroup.norm x ≤ 1) :
    ∃ i : Fin n, x = FreeGroup.of i ∨ x = (FreeGroup.of i)⁻¹ := by
  have hnz : FreeGroup.norm x ≠ 0 := by
    intro hz
    exact hx (FreeGroup.norm_eq_zero.mp hz)
  have hone : FreeGroup.norm x = 1 := by omega
  rcases toWord_singleton_of_norm_eq_one hx hone with ⟨⟨i, b⟩, hl⟩
  cases b with
  | true =>
      refine ⟨i, Or.inl ?_⟩
      exact eq_of_of_singleton_true x hl
  | false =>
      refine ⟨i, Or.inr ?_⟩
      exact eq_inv_of_singleton_false x hl

/-- An injective map `Fin n → Fin n` is surjective (pigeonhole). -/
lemma fin_injective_surjective {n : ℕ} (σ : Fin n → Fin n)
    (hinj : Function.Injective σ) : Function.Surjective σ := by
  classical
  intro y
  have hcard : (Finset.univ.image σ).card = n := by
    rw [Finset.card_image_of_injective Finset.univ hinj]
    simp
  have hsub : (Finset.univ.image σ) ⊆ (Finset.univ : Finset (Fin n)) :=
    Finset.subset_univ _
  have heq : (Finset.univ.image σ) = (Finset.univ : Finset (Fin n)) := by
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; simp)
  have hy : y ∈ (Finset.univ.image σ) := by
    rw [heq]
    simp
  rcases (Finset.mem_image.mp hy) with ⟨m, hm, hσ⟩
  exact ⟨m, hσ⟩

/-- **Letter choice.**  If some basis image of `α` has reduced length ≥ 2,
then some standard generator `a_m` has an aggregate expression in the basis
images with at least two factors: `2 ≤ |(α⁻¹(a_m)).toWord|`.  (The aggregate
factors for `a_m` are obtained by mapping the letters of `α⁻¹(a_m)` through
`α`; its length is `|(α⁻¹(a_m)).toWord|`.) -/
theorem exists_two_factor_letter {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hlong : ∃ j : Fin n, 1 < FreeGroup.norm (α (FreeGroup.of j))) :
    ∃ m : Fin n, 2 ≤ ((α⁻¹) (FreeGroup.of m)).toWord.length := by
  classical
  by_contra h
  have hall : ∀ m : Fin n, FreeGroup.norm ((α⁻¹) (FreeGroup.of m)) ≤ 1 := by
    intro m
    by_contra hm
    have hle : 2 ≤ ((α⁻¹) (FreeGroup.of m)).toWord.length := by
      change 2 ≤ FreeGroup.norm ((α⁻¹) (FreeGroup.of m))
      omega
    exact h ⟨m, hle⟩
  have hne : ∀ m : Fin n, (α⁻¹) (FreeGroup.of m) ≠ 1 := by
    intro m hz
    have hα := congrArg (fun x : FreeGroup (Fin n) => α x) hz
    rw [MulAut.apply_inv_self (FreeGroup (Fin n)) α (FreeGroup.of m)] at hα
    rw [aut_map_one α] at hα
    exact (FreeGroup.of_ne_one m) hα
  let k : Fin n → Fin n := fun m =>
    Classical.choose (word_single_letter_of_le_one (hne m) (hall m))
  have hspec : ∀ m : Fin n,
      (α⁻¹) (FreeGroup.of m) = FreeGroup.of (k m) ∨
      (α⁻¹) (FreeGroup.of m) = (FreeGroup.of (k m))⁻¹ := by
    intro m
    have hs := Classical.choose_spec (word_single_letter_of_le_one (hne m) (hall m))
    simpa [k] using hs
  -- every `w_{k m}` is a single letter
  have hw1 : ∀ m : Fin n, FreeGroup.norm (α (FreeGroup.of (k m))) = 1 := by
    intro m
    rcases hspec m with h | h
    · have hα := congrArg (fun x : FreeGroup (Fin n) => α x) h
      rw [MulAut.apply_inv_self (FreeGroup (Fin n)) α (FreeGroup.of m)] at hα
      have hn := congrArg FreeGroup.norm hα
      rw [FreeGroup.norm_of] at hn
      exact hn.symm
    · have hα := congrArg (fun x : FreeGroup (Fin n) => α x) h
      rw [MulAut.apply_inv_self (FreeGroup (Fin n)) α (FreeGroup.of m)] at hα
      rw [aut_map_inv α (FreeGroup.of (k m))] at hα
      have hn := congrArg FreeGroup.norm hα
      rw [FreeGroup.norm_of] at hn
      rw [norm_inv_eq] at hn
      exact hn.symm
  -- `k` is injective
  have hk_inj : Function.Injective k := by
    intro m m' hk
    by_contra hmm
    rcases hspec m with spm | spm
    · rcases hspec m' with spm' | spm'
      · have heq : (α⁻¹) (FreeGroup.of m) = (α⁻¹) (FreeGroup.of m') := by
          rw [spm, spm', hk]
        have hα := congrArg (fun x : FreeGroup (Fin n) => α x) heq
        rw [MulAut.apply_inv_self (FreeGroup (Fin n)) α (FreeGroup.of m)] at hα
        rw [MulAut.apply_inv_self (FreeGroup (Fin n)) α (FreeGroup.of m')] at hα
        exact hmm (FreeGroup.of_injective hα)
      · have heq : (α⁻¹) (FreeGroup.of m') = ((α⁻¹) (FreeGroup.of m))⁻¹ := by
          rw [spm', ← hk, ← spm]
        have hα := congrArg (fun x : FreeGroup (Fin n) => α x) heq
        rw [MulAut.apply_inv_self (FreeGroup (Fin n)) α (FreeGroup.of m')] at hα
        rw [aut_map_inv α ((α⁻¹) (FreeGroup.of m))] at hα
        rw [MulAut.apply_inv_self (FreeGroup (Fin n)) α (FreeGroup.of m)] at hα
        exact (of_ne_inv_of m' m) hα
    · rcases hspec m' with spm' | spm'
      · have heq : (α⁻¹) (FreeGroup.of m) = ((α⁻¹) (FreeGroup.of m'))⁻¹ := by
          rw [spm, hk, ← spm']
        have hα := congrArg (fun x : FreeGroup (Fin n) => α x) heq
        rw [MulAut.apply_inv_self (FreeGroup (Fin n)) α (FreeGroup.of m)] at hα
        rw [aut_map_inv α ((α⁻¹) (FreeGroup.of m'))] at hα
        rw [MulAut.apply_inv_self (FreeGroup (Fin n)) α (FreeGroup.of m')] at hα
        exact (of_ne_inv_of m m') hα
      · have heq : (α⁻¹) (FreeGroup.of m) = (α⁻¹) (FreeGroup.of m') := by
          rw [spm, spm', hk]
        have hα := congrArg (fun x : FreeGroup (Fin n) => α x) heq
        rw [MulAut.apply_inv_self (FreeGroup (Fin n)) α (FreeGroup.of m)] at hα
        rw [MulAut.apply_inv_self (FreeGroup (Fin n)) α (FreeGroup.of m')] at hα
        exact hmm (FreeGroup.of_injective hα)
  have hsurj : Function.Surjective k := fin_injective_surjective k hk_inj
  rcases hlong with ⟨j0, hj0⟩
  rcases hsurj j0 with ⟨m, hm⟩
  have hw : FreeGroup.norm (α (FreeGroup.of j0)) = 1 := by
    rw [← hm]
    exact hw1 m
  omega

end Submission.Nielsen
