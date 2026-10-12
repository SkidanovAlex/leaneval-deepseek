import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finsupp.Weight
import Submission.Work.BoseDict.Defs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDictC.modeProd_eq_zero_of_sum_ne`

The mode product `modeProd e n α` is a symmetric function on `Xn n = Fin n → Sp` built out of
the labellings `σ : Fin n → Fin m` whose occupation multi-index `modeMult σ` equals `α`.  Any
such labelling has total occupation `n`, so a multi-index `α` with `α.sum (fun _ k => k) ≠ n`
gives the zero function.

The only ingredient is `modeMult_sum`, the computation of the total occupation of
`modeMult σ` as the number `n` of labels.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseDictC

/-- The total occupation number of the multi-index of a labelling `σ : Fin n → Fin m` is `n`:
`(modeMult σ).degree = n`, i.e. the sum of the multiplicities of the modes is the number of
labels.  (`Finsupp.degree f = f.sum (fun _ k => k)` by definition.) -/
lemma modeMult_degree {m n : ℕ} (σ : Fin n → Fin m) : (Work.BoseDict.modeMult σ).degree = n := by
  simp only [Work.BoseDict.modeMult, map_sum, Finsupp.degree_single]
  rw [← Finset.card_eq_sum_card_fiberwise (f := σ) (s := Finset.univ) (t := Finset.univ)
    (fun a _ => Finset.mem_univ _)]
  simp

/-- The total occupation number of the multi-index of a labelling `σ : Fin n → Fin m`, in the
form in which the corpus writes it: `(modeMult σ).sum (fun _ k => k) = n`. -/
lemma modeMult_sum {m n : ℕ} (σ : Fin n → Fin m) :
    (Work.BoseDict.modeMult σ).sum (fun _ k => k) = n := by
  rw [show (Work.BoseDict.modeMult σ).sum (fun _ k => k) = (Work.BoseDict.modeMult σ).degree
      from rfl]
  exact modeMult_degree σ

theorem modeProd_eq_zero_of_sum_ne {m n : ℕ} {e : Fin m → Work.BoseDict.Sp → ℂ} (α : Fin m →₀ ℕ)
    (hα : α.sum (fun _ k => k) ≠ n) (x : Work.BoseDict.Xn n) :
    Work.BoseDict.modeProd e n α x = 0 := by
  classical
  simp only [Work.BoseDict.modeProd]
  refine Finset.sum_eq_zero fun σ _ => ?_
  have h : Work.BoseDict.modeMult σ ≠ α := by
    intro hh
    exact hα (by rw [← hh]; exact modeMult_sum σ)
  rw [if_neg h, zero_mul]

end Work.BoseDictC
