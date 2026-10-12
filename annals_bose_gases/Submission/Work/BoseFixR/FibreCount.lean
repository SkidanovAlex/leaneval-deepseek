import Mathlib.Algebra.BigOperators.Fin
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.FibreCount` — fibre-counting helpers

**Helper module** for `Work.BoseFixR.labelling_count`: the multinomial count

`#{σ : Fin n → ι | ∀ i, #{d | σ d = i} = α i} = n! / ∏ i, (α i)!`  (`α.sum id = n`)

is proved there by induction on `n`, peeling off the last particle via `Fin.init` /
`Fin.snoc`.  The pieces of that argument are these *pure Mathlib* lemmas (a finite type
`ι`, a Finsupp `α : ι →₀ ℕ`), so that the companion modules `fibre_peel` (the peeling
bijection) and `fibre_arith` (the multinomial recursion for factorials) can state their
own results in the same vocabulary.

Nothing here mentions `modeMult`; the glue `modeMult_apply` lives in
`Submission.Work.BoseFixR.labelling_count`.
-/

open Finset

namespace Work.BoseFixR

/-- **The fibre cardinalities sum to the number of particles**: for any `σ : δ → ι` with
`δ` finite the sum of the cardinalities of its fibres is `Fintype.card δ`. -/
theorem sum_fibre_card {ι δ : Type*} [Fintype ι] [Fintype δ] [DecidableEq ι] (σ : δ → ι) :
    ∑ i : ι, (Finset.univ.filter fun d => σ d = i).card = Fintype.card δ := by
  rw [← Finset.card_univ (α := δ)]
  exact (Finset.card_eq_sum_card_fiberwise (f := σ) (s := (Finset.univ : Finset δ))
    (t := (Finset.univ : Finset ι)) (fun b _ => Finset.mem_univ _)).symm

/-- **Peeling the last particle** (`Fin.castSucc`): the fibre of `i` in
`σ : Fin (n+1) → ι` is the fibre of `i` in `σ ∘ Fin.castSucc`, plus the last particle
when it equals `i`. -/
theorem card_fibre_castSucc {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (σ : Fin (n+1) → ι) (i : ι) :
    (Finset.univ.filter fun d : Fin (n+1) => σ d = i).card
      = (Finset.univ.filter fun d : Fin n => σ d.castSucc = i).card
        + (if σ (Fin.last n) = i then 1 else 0) := by
  rw [Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_castSucc (f := fun d : Fin (n+1) => if σ d = i then (1:ℕ) else 0)]

/-- The same, for a labelling built by `Fin.snoc`. -/
theorem card_fibre_snoc {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (τ : Fin n → ι) (k i : ι) :
    (Finset.univ.filter fun d : Fin (n+1) => (Fin.snoc τ k : Fin (n+1) → ι) d = i).card
      = (Finset.univ.filter fun d : Fin n => τ d = i).card + (if k = i then 1 else 0) := by
  rw [card_fibre_castSucc (σ := Fin.snoc τ k)]
  simp

end Work.BoseFixR
