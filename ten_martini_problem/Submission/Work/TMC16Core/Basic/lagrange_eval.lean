import Mathlib

namespace Work.TMC16Core.Basic

open Polynomial

theorem lagrange_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Polynomial ℂ) (v : ι → ℂ) (w : ℂ)
    (hinj : Function.Injective v) (hdeg : Q.natDegree < Fintype.card ι) :
    Q.eval w = ∑ i : ι, (Q.eval (v i) / ∏ j ∈ Finset.univ.erase i, (v i - v j)) *
        ∏ j ∈ Finset.univ.erase i, (w - v j) := by
  classical
  have hvs : Set.InjOn v (Finset.univ : Finset ι) := fun i _ j _ h => hinj h
  have hdeg' : Q.degree < ((Finset.univ : Finset ι).card : WithBot ℕ) := by
    rw [Finset.card_univ]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hdeg)
  have hQ : Q = Lagrange.interpolate (Finset.univ : Finset ι) v (fun i => Q.eval (v i)) :=
    Lagrange.eq_interpolate hvs hdeg'
  conv_lhs => rw [hQ, Lagrange.interpolate_eq_sum]
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C, eval_prod]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  simp

end Work.TMC16Core.Basic
