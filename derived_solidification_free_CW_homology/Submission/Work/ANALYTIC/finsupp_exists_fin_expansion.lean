import Mathlib

namespace Work.ANALYTIC

/-- Every finitely supported `ℤ`-valued function is the sum of its singleton terms:
`t = ∑_{a ∈ t.support} single a (t a)`. -/
lemma finsupp_eq_sum_support_single (α : Type) [DecidableEq α] (t : α →₀ ℤ) :
    t = ∑ a ∈ t.support, Finsupp.single a (t a) :=
  (Finsupp.sum_single t).symm

/-- Every finitely supported `ℤ`-valued function `t` on `α` is a finite linear combination of
the "atoms" `single (e j) 1`: there is a finite indexing `e : Fin k → α` and coefficients
`c : Fin k → ℤ` with `t = ∑ j, c j • single (e j) 1`.  (Take the support of `t` as the index
set.) -/
theorem finsupp_exists_fin_expansion (α : Type) [DecidableEq α] (t : α →₀ ℤ) :
    ∃ (k : ℕ) (e : Fin k → α) (c : Fin k → ℤ),
      t = ∑ j : Fin k, (c j) • Finsupp.single (e j) (1 : ℤ) := by
  classical
  set e : Fin t.support.card → α := fun j => ((Finset.equivFin t.support).symm j : α) with he
  refine ⟨t.support.card, e, fun j => t (e j), ?_⟩
  have h1 : t = ∑ a ∈ t.support, Finsupp.single a (t a) := finsupp_eq_sum_support_single α t
  have h2 : (∑ a ∈ t.support, Finsupp.single a (t a))
      = ∑ j : Fin t.support.card, Finsupp.single (e j) (t (e j)) := by
    rw [Finset.sum_subtype t.support (fun x => Iff.rfl) (fun a => Finsupp.single a (t a))]
    symm
    rw [← Equiv.sum_comp (Finset.equivFin t.support)
        (fun j : Fin t.support.card => Finsupp.single (e j) (t (e j)))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [he, Equiv.symm_apply_apply]
  exact h1.trans (h2.trans (Finset.sum_congr rfl (fun j _ => by
    rw [Finsupp.smul_single]
    simp)))

end Work.ANALYTIC
