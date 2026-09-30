import Mathlib
import Submission.Work.BMF.kdr_defs
import Submission.Work.BMF.meanValueDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `J`-count as a sum of matching indicator terms

`Work.BMF.sum_ite_momMatch_eq_J` identifies the multiplicity-counting sum
`∑_{p} [ p.1 and p.2 have equal power sums of degrees 1,…,k ]`
over pairs of `s`-tuples in `[1,X]` with Vinogradov's mean-value count
`J_{s,k}(X) = #{(x,y) : ∀ j ≤ k, ∑ xᵢʲ = ∑ yᵢʲ}`.

Concretely, the summand is `1` exactly when the `Fin k`-indexed vector of
`ℤ`-valued differences of power sums of degrees `1,…,k` vanishes, which is
the same condition as equality of the power sums for all degrees `0 ≤ j ≤ k`
(degree `0` being `s = s`, automatically true).  The proof is therefore
bookkeeping: convert the `if`-sum into the cardinality of a filtered `Finset`,
identify the two filter predicates, and unfold `J`.
-/

namespace Work.BMF

open Finset
open scoped BigOperators

/-- The predicate on the left-hand side of `sum_ite_momMatch_eq_J`: the vector of `ℤ`-valued
differences of the power sums of degrees `1, …, k` of the two blocks vanishes. -/
private abbrev sumItePred (s k X : ℕ)
    (p : (Fin s → Finset.Icc 1 X) × (Fin s → Finset.Icc 1 X)) : Prop :=
  ((fun j : Fin k => (∑ i, (((p.1 i).1 : ℤ) ^ ((j : ℕ) + 1)))
        - (∑ i, (((p.2 i).1 : ℤ) ^ ((j : ℕ) + 1)))) = 0)

/-- The predicate used in the definition of `J`: equality of all power sums of degrees
`0 ≤ j ≤ k`. -/
private abbrev jPred (s k X : ℕ)
    (p : (Fin s → Finset.Icc 1 X) × (Fin s → Finset.Icc 1 X)) : Prop :=
  ∀ j, j ≤ k → (∑ i, ((p.1 i).1 : ℕ) ^ j) = (∑ i, ((p.2 i).1 : ℕ) ^ j)

/-- The two predicates agree: a vanishing vector of differences of the power sums of degrees
`1, …, k` is the same as equality of the power sums for all degrees `0 ≤ j ≤ k`, the degree
`0` case being automatic. -/
private lemma sumItePred_iff_jPred (s k X : ℕ)
    (p : (Fin s → Finset.Icc 1 X) × (Fin s → Finset.Icc 1 X)) :
    sumItePred s k X p ↔ jPred s k X p := by
  simp only [sumItePred, jPred, funext_iff, Pi.zero_apply, sub_eq_zero]
  constructor
  · intro h j hj
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; simp
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hmk : m < k := by omega
      have hh : (∑ i, (((p.1 i).1 : ℤ) ^ (m + 1)))
          = (∑ i, (((p.2 i).1 : ℤ) ^ (m + 1))) := by
        simpa using h ⟨m, hmk⟩
      rw [hm]
      apply Nat.cast_injective (R := ℤ)
      push_cast
      exact hh
  · intro h x
    have hx : (x : ℕ) + 1 ≤ k := by have hlt := x.isLt; omega
    exact_mod_cast h (x + 1) hx

/-- `J` unfolds to the cardinality of the filtered set given by `jPred`. -/
private lemma J_eq_filter (s k X : ℕ) :
    LeanEval.NumberTheory.VinogradovMeanValue.J s k X
      = (((Finset.univ.filter (jPred s k X)).card : ℕ) : ℝ) := rfl

theorem sum_ite_momMatch_eq_J (s k X : ℕ) :
    (∑ p : (Fin s → Finset.Icc 1 X) × (Fin s → Finset.Icc 1 X),
        if ((fun j : Fin k => (∑ i, (((p.1 i).1 : ℤ) ^ ((j:ℕ)+1)))
              - (∑ i, (((p.2 i).1 : ℤ) ^ ((j:ℕ)+1)))) = 0) then (1:ℂ) else 0)
      = ((LeanEval.NumberTheory.VinogradovMeanValue.J s k X : ℝ) : ℂ) := by
  classical
  have hL : (∑ p : (Fin s → Finset.Icc 1 X) × (Fin s → Finset.Icc 1 X),
        if ((fun j : Fin k => (∑ i, (((p.1 i).1 : ℤ) ^ ((j:ℕ)+1)))
              - (∑ i, (((p.2 i).1 : ℤ) ^ ((j:ℕ)+1)))) = 0) then (1:ℂ) else 0)
      = ((Finset.univ.filter (sumItePred s k X)).card : ℂ) :=
    Finset.sum_boole (sumItePred s k X) Finset.univ (R := ℂ)
  have hcard : (Finset.univ.filter (sumItePred s k X))
      = (Finset.univ.filter (jPred s k X)) := by
    apply Finset.filter_congr
    intro p _
    exact sumItePred_iff_jPred s k X p
  rw [hL, J_eq_filter, hcard]
  exact (Complex.ofReal_natCast _).symm

end Work.BMF
