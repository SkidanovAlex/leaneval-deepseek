import Mathlib

/-!
# `Work.EKLC6Core.returnTimeDefs` — the first-hit (entrance) sets of a self-map

For a self-map `T` of a set `X` and a subset `Ω ⊆ X`, the `n`-th **first-hit set** is the set of
points whose first visit of `Ω` among the times `0, 1, ..., n` happens exactly at time `n`:

`firstHitSet T Ω n = {x | T^[n] x ∈ Ω ∧ ∀ j < n, T^[j] x ∉ Ω}`.

The family `firstHitSet T Ω ·` is the classical "entrance" tower of Kac's lemma: its members are
pairwise disjoint, and for the first-return partition `Q i = firstReturnSet t Ω i` of `Ω` (Pisa
7.49) one has the fundamental relation

`T ⁻¹' (firstHitSet T Ω n) = firstHitSet T Ω (n+1) ⊔ Q (n+1)`,

which telescopes into `μ (Q (n+1)) = μ (firstHitSet T Ω n) - μ (firstHitSet T Ω (n+1))` and hence
into Kac's inequality `∑ i · μ (Q i) ≤ 1`.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

/-- `T` applied after `j` iterates is `j + 1` iterates: `T^[j] (T x) = T^[j+1] x`. -/
theorem iterate_apply_self {X : Type*} (T : X → X) (j : ℕ) (x : X) :
    (T^[j]) (T x) = (T^[j + 1]) x :=
  (Function.iterate_succ_apply T j x).symm

/-- The `n`-th **first-hit set** of `Ω` under the self-map `T`: the points whose first visit of
`Ω` in the orbit `x, T x, T² x, …, Tⁿ x` takes place at time `n`.

For `n = 0` this is `Ω` itself; for `n ≥ 1` it is the set of points that are outside `Ω` up to
time `n - 1` and enter `Ω` at time `n`. -/
def firstHitSet {X : Type*} (T : X → X) (Ω : Set X) (n : ℕ) : Set X :=
  (T^[n]) ⁻¹' Ω ∩ ⋂ j ∈ Finset.range n, ((T^[j]) ⁻¹' Ω)ᶜ

@[simp] theorem firstHitSet_zero {X : Type*} (T : X → X) (Ω : Set X) :
    firstHitSet T Ω 0 = Ω := by
  simp [firstHitSet]

theorem mem_firstHitSet {X : Type*} {T : X → X} {Ω : Set X} {n : ℕ} {x : X} :
    x ∈ firstHitSet T Ω n ↔ (T^[n]) x ∈ Ω ∧ ∀ j < n, (T^[j]) x ∉ Ω := by
  simp [firstHitSet]

/-- The recursion behind the entrance tower: the first-hit set of level `n + 1` consists of the
points outside `Ω` whose image under `T` is a first-hit point of level `n`. -/
theorem firstHitSet_succ {X : Type*} (T : X → X) (Ω : Set X) (n : ℕ) :
    firstHitSet T Ω (n + 1) = Ωᶜ ∩ T ⁻¹' firstHitSet T Ω n := by
  ext x
  rw [mem_firstHitSet, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_preimage, mem_firstHitSet]
  constructor
  · rintro ⟨hx, hprev⟩
    refine ⟨hprev 0 (Nat.succ_pos n), ?_, fun j hj => ?_⟩
    · rw [Function.iterate_succ_apply] at hx; exact hx
    · rw [iterate_apply_self]; exact hprev (j + 1) (Nat.succ_lt_succ hj)
  · rintro ⟨h0, hx, hprev⟩
    refine ⟨?_, fun j hj => ?_⟩
    · rw [Function.iterate_succ_apply]; exact hx
    · rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · exact h0
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hjpos.ne'
        have h := hprev k (by omega)
        rwa [iterate_apply_self] at h

end Work.EKLC6Core
