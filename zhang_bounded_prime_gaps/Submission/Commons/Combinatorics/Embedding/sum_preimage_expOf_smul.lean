import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Submission.Commons.Combinatorics.Embedding.card_preimage_expOf
import Submission.Commons.Combinatorics.Embedding.sum_preimage_expOf

namespace Commons.Combinatorics.Embedding

open Finset
open scoped BigOperators

/-- **Regrouping a sum over injective placements by the induced profile, in an arbitrary additive
commutative monoid.**

This is `Combinatorics/Embedding/sum_preimage_expOf` with the coefficient monoid generalised from
`ℕ` to any `AddCommMonoid M` (the labelling factor `∏ v ∈ α.toFinset, (α.count v)!` is then a
natural-number scalar action `•`).  The `ℝ`-valued case `M = ℝ` is what the marginal (`J`-side)
development of the bounded-gaps certificate needs, where `G f = ∏ c, (t c) ^ (f c)` and the sum
over placements computes the *labelled* monomial `lmono`, while the right-hand side is
`theta α · m_α(t)` with `m_α` the monomial symmetric polynomial. -/
theorem sum_preimage_expOf_smul {k : ℕ} (α : List ℕ) (hα : 0 ∉ α) {M : Type*}
    [AddCommMonoid M] (G : (Fin k → ℕ) → M) :
    (∑ e : Fin α.length ↪ Fin k,
        G (fun c => ∑ i : Fin α.length, if e i = c then α.get i else 0))
      = (∏ v ∈ α.toFinset, (α.count v).factorial) •
          ∑ f ∈ Fintype.piFinset (fun _ : Fin k => Finset.range (α.sum + 1)),
            if ((∀ v ∈ α.toFinset, (Finset.univ.filter (fun c : Fin k => f c = v)).card = α.count v)
                ∧ (∀ c : Fin k, f c = 0 ∨ f c ∈ α))
              then G f else 0 := by
  classical
  set S : Finset (Fin k → ℕ) := Fintype.piFinset (fun _ : Fin k => Finset.range (α.sum + 1)) with hS
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
              (fun c => ∑ i : Fin α.length, if e i = c then α.get i else 0) = f)).card • G f := by
          refine Finset.sum_congr rfl ?_
          intro f _
          rw [← Finset.sum_filter, Finset.sum_const]
      _ = ∑ f ∈ S,
            (if ((∀ v ∈ α.toFinset, (Finset.univ.filter (fun c : Fin k => f c = v)).card = α.count v)
                ∧ (∀ c : Fin k, f c = 0 ∨ f c ∈ α))
              then ∏ v ∈ α.toFinset, (α.count v).factorial else 0) • G f := by
          refine Finset.sum_congr rfl ?_
          intro f _
          rw [hfiber f, card_preimage_expOf α hα f]
      _ = (∏ v ∈ α.toFinset, (α.count v).factorial) •
            ∑ f ∈ S,
              if ((∀ v ∈ α.toFinset, (Finset.univ.filter (fun c : Fin k => f c = v)).card = α.count v)
                  ∧ (∀ c : Fin k, f c = 0 ∨ f c ∈ α))
                then G f else 0 := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl ?_
          intro f _
          by_cases h : ((∀ v ∈ α.toFinset, (Finset.univ.filter (fun c : Fin k => f c = v)).card = α.count v)
                ∧ (∀ c : Fin k, f c = 0 ∨ f c ∈ α)) <;> simp [h]

end Commons.Combinatorics.Embedding