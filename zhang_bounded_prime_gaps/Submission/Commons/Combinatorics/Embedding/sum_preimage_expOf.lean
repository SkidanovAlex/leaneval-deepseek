import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Submission.Commons.Combinatorics.Embedding.card_preimage_expOf

namespace Commons.Combinatorics.Embedding

open Finset
open scoped BigOperators

/-- **Regrouping a sum over injective placements by the induced profile.**

For a list `α` of nonzero natural numbers and any `G : (Fin k → ℕ) → ℕ`, the sum of `G` over the
injective placements `e : Fin α.length ↪ Fin k` (evaluated at the induced profile
`c ↦ Σ_i [e i = c] · α_i`) equals `∏ v ∈ α.toFinset, (α.count v)!` times the sum of `G` over the
profiles of `α` (the functions `f` with `f c ≤ α.sum`, every nonzero value in `α`, occurring with
the multiplicity with which it occurs in `α`); non-profile functions contribute `0`.

This is the `Finset.sum_fiberwise` consequence of `card_preimage_expOf`: when the profile
condition holds all values of `f` are `≤ α.sum` (their weighted sum is `α.sum`), so the
`Fintype.piFinset` range bound loses nothing. -/
theorem sum_preimage_expOf {k : ℕ} (α : List ℕ) (hα : 0 ∉ α) (G : (Fin k → ℕ) → ℕ) :
    (∑ e : Fin α.length ↪ Fin k,
        G (fun c => ∑ i : Fin α.length, if e i = c then α.get i else 0))
      = (∏ v ∈ α.toFinset, (α.count v).factorial) *
          ∑ f ∈ Fintype.piFinset (fun _ : Fin k => Finset.range (α.sum + 1)),
            if ((∀ v ∈ α.toFinset, (Finset.univ.filter (fun c : Fin k => f c = v)).card = α.count v)
                ∧ (∀ c : Fin k, f c = 0 ∨ f c ∈ α))
              then G f else 0 := by
  classical
  -- The finite set of candidate profiles.
  set S : Finset (Fin k → ℕ) := Fintype.piFinset (fun _ : Fin k => Finset.range (α.sum + 1)) with hS
  -- Every actual profile lies in `S`: its values are bounded by `α.sum`.
  have hmem : ∀ e : Fin α.length ↪ Fin k,
      (fun c => ∑ i : Fin α.length, if e i = c then α.get i else 0) ∈ S := by
    intro e
    rw [hS, Fintype.mem_piFinset]
    intro c
    rw [Finset.mem_range]
    have h1 : (∑ i : Fin α.length, if e i = c then α.get i else 0)
        ≤ ∑ i : Fin α.length, α.get i :=
      Finset.sum_le_sum (fun i _ => by split <;> simp)
    have h2 : (∑ i : Fin α.length, α.get i) = α.sum := by
      rw [← List.sum_ofFn (f := α.get), List.ofFn_get]
    omega
  -- Rewriting `φ e = f` as the pointwise condition used by `card_preimage_expOf`.
  have hfiber : ∀ f : Fin k → ℕ,
      (Finset.univ.filter (fun e : Fin α.length ↪ Fin k =>
        (fun c => ∑ i : Fin α.length, if e i = c then α.get i else 0) = f)).card
      = (Finset.univ.filter (fun e : Fin α.length ↪ Fin k =>
        ∀ c : Fin k, (∑ i : Fin α.length, if e i = c then α.get i else 0) = f c)).card := by
    intro f
    congr 1
    apply Finset.filter_congr
    intro e _
    exact funext_iff
  calc
    (∑ e : Fin α.length ↪ Fin k,
        G (fun c => ∑ i : Fin α.length, if e i = c then α.get i else 0))
        = ∑ e : Fin α.length ↪ Fin k,
            ∑ f ∈ S, (if (fun c => ∑ i : Fin α.length, if e i = c then α.get i else 0) = f
              then G f else 0) := by
          refine Finset.sum_congr rfl ?_
          intro e _
          rw [Finset.sum_ite_eq, if_pos (hmem e)]
      _ = ∑ f ∈ S, ∑ e : Fin α.length ↪ Fin k,
            (if (fun c => ∑ i : Fin α.length, if e i = c then α.get i else 0) = f
              then G f else 0) := by
          rw [Finset.sum_comm]
      _ = ∑ f ∈ S,
            (Finset.univ.filter (fun e : Fin α.length ↪ Fin k =>
              (fun c => ∑ i : Fin α.length, if e i = c then α.get i else 0) = f)).card * G f := by
          refine Finset.sum_congr rfl ?_
          intro f _
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      _ = ∑ f ∈ S,
            (if ((∀ v ∈ α.toFinset, (Finset.univ.filter (fun c : Fin k => f c = v)).card = α.count v)
                ∧ (∀ c : Fin k, f c = 0 ∨ f c ∈ α))
              then ∏ v ∈ α.toFinset, (α.count v).factorial else 0) * G f := by
          refine Finset.sum_congr rfl ?_
          intro f _
          rw [hfiber f, card_preimage_expOf α hα f]
      _ = (∏ v ∈ α.toFinset, (α.count v).factorial) *
            ∑ f ∈ S,
              if ((∀ v ∈ α.toFinset, (Finset.univ.filter (fun c : Fin k => f c = v)).card = α.count v)
                  ∧ (∀ c : Fin k, f c = 0 ∨ f c ∈ α))
                then G f else 0 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro f _
          by_cases h : ((∀ v ∈ α.toFinset, (Finset.univ.filter (fun c : Fin k => f c = v)).card = α.count v)
                ∧ (∀ c : Fin k, f c = 0 ∨ f c ∈ α)) <;> simp [h]

end Commons.Combinatorics.Embedding