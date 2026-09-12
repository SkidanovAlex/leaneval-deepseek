import Mathlib

/-!
# Finite-sum reindexing between `Fin` and integer intervals

Two small `AddCommMonoid`-generic identities used by the early-ints mean
argument (Gap B): reindexing a sum over `{2,…,N+1}` by `Fin N` via
`k ↦ k.val + 2`, and splitting the interval `{1,…,N+2}` into the interior
`{2,…,N+1}` plus the two endpoints.

Namespace `Submission.QuantileSums`.  Only Mathlib.
-/

open scoped BigOperators
open Finset

namespace Submission.QuantileSums

/-- `Σ_{i∈[2..N+1]} g i = Σ_{k : Fin N} g (k+2)`. -/
lemma sum_Icc_two_shift_fin {N : ℕ} {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    (∑ i ∈ Finset.Icc 2 (N + 1), g i) = (∑ k : Fin N, g (k.val + 2)) := by
  classical
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hstep : (∑ i ∈ Finset.Icc 2 (N + 2), g i) =
          (∑ i ∈ Finset.Icc 2 (N + 1), g i) + g (N + 2) := by
        simpa using (Finset.sum_Icc_succ_top (a := 2) (b := N + 1) (f := g) (by omega))
      have hfin : (∑ k : Fin (N + 1), g (k.val + 2)) =
          (∑ k : Fin N, g (k.val + 2)) + g (N + 2) := by
        rw [Fin.sum_univ_castSucc]
        rfl
      calc
        (∑ i ∈ Finset.Icc 2 ((N + 1) + 1), g i) = (∑ i ∈ Finset.Icc 2 (N + 2), g i) := by rfl
        _ = (∑ i ∈ Finset.Icc 2 (N + 1), g i) + g (N + 2) := hstep
        _ = (∑ k : Fin N, g (k.val + 2)) + g (N + 2) := by rw [ih]
        _ = (∑ k : Fin (N + 1), g (k.val + 2)) := hfin.symm

/-- `Σ_{i∈[1..N+2]} g i = g 1 + g (N+2) + Σ_{i∈[2..N+1]} g i`. -/
lemma sum_Icc_one_split {N : ℕ} {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    (∑ i ∈ Finset.Icc 1 (N + 2), g i) = g 1 + g (N + 2) + (∑ i ∈ Finset.Icc 2 (N + 1), g i) := by
  classical
  have htop : (∑ i ∈ Finset.Icc 2 (N + 2), g i) =
      (∑ i ∈ Finset.Icc 2 (N + 1), g i) + g (N + 2) := by
    simpa using (Finset.sum_Icc_succ_top (a := 2) (b := N + 1) (f := g) (by omega))
  have hcover : Finset.Icc 1 (N + 2) = ({1} : Finset ℕ) ∪ Finset.Icc 2 (N + 2) := by
    ext i
    rw [Finset.mem_union]
    constructor
    · intro hi
      have hge : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hle : i ≤ N + 2 := (Finset.mem_Icc.mp hi).2
      by_cases h1 : i = 1
      · left
        simpa [h1]
      · right
        rw [Finset.mem_Icc]
        constructor <;> omega
    · intro hi
      rcases hi with h1 | hi
      · rw [Finset.mem_singleton] at h1
        subst h1
        rw [Finset.mem_Icc]
        omega
      · rw [Finset.mem_Icc] at hi
        rw [Finset.mem_Icc]
        omega
  have hdisj : Disjoint ({1} : Finset ℕ) (Finset.Icc 2 (N + 2)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_singleton] at hx1
    have hge := (Finset.mem_Icc.mp hx2).1
    omega
  calc
    (∑ i ∈ Finset.Icc 1 (N + 2), g i) = (∑ i ∈ ({1} : Finset ℕ) ∪ Finset.Icc 2 (N + 2), g i) := by
      rw [hcover]
    _ = (∑ i ∈ ({1} : Finset ℕ), g i) + (∑ i ∈ Finset.Icc 2 (N + 2), g i) := by
      rw [Finset.sum_union hdisj]
    _ = g 1 + (∑ i ∈ Finset.Icc 2 (N + 2), g i) := by simp
    _ = g 1 + ((∑ i ∈ Finset.Icc 2 (N + 1), g i) + g (N + 2)) := by rw [htop]
    _ = g 1 + g (N + 2) + (∑ i ∈ Finset.Icc 2 (N + 1), g i) := by
      abel


/-- Reindexing a sum over `Fin n` onto `Fin N` (same cardinality) through the
canonical embedding `i ↦ ⟨i.val, _⟩`. -/
lemma sum_reindex_fin {n N : ℕ} (hsum : N = n) {M : Type*} [AddCommMonoid M]
    (g : Fin N → M) (α : Fin n → M) (hα : ∀ i : Fin n, α i = g ⟨i.val, by omega⟩) :
    (∑ i : Fin n, α i) = (∑ t : Fin N, g t) := by
  classical
  let emb : Fin n → Fin N := fun i => ⟨i.val, by omega⟩
  have hinj : Function.Injective emb := by
    intro a b hab
    apply Fin.ext
    simpa [emb] using congrArg Fin.val hab
  have hbij : Function.Bijective emb := by
    rw [Fintype.bijective_iff_injective_and_card]
    constructor
    · exact hinj
    · rw [Fintype.card_fin, Fintype.card_fin]
      exact hsum.symm
  let e : Fin n ≃ Fin N := Equiv.ofBijective emb hbij
  exact Fintype.sum_equiv e α g (by
    intro i
    dsimp [e, emb]
    exact hα i)

end Submission.QuantileSums
