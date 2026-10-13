import Mathlib
import Submission.Work.WilC4aP.Basic

namespace Work.WilC4aP

/-- A monic polynomial of degree `m` over `ℂ` with `m` prescribed distinct roots is the product
of the corresponding linear factors. -/
theorem prod_eq_of_distinct_roots {m : ℕ} {p : Polynomial ℂ} (hmon : p.Monic) (hdeg : p.natDegree = m)
    {r : Fin m → ℂ} (hinj : Function.Injective r) (hroot : ∀ j, p.eval (r j) = 0) :
    p = ∏ j, (Polynomial.X - Polynomial.C (r j)) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- the empty product: `p` is monic of degree `0`, hence `p = 1 = ∏ ∅`
    subst hm
    have hp1 : p = 1 := Polynomial.eq_one_of_monic_natDegree_zero hmon hdeg
    rw [hp1]
    simp
  · set q : Polynomial ℂ := ∏ j, (Polynomial.X - Polynomial.C (r j)) with hq
    have hqmon : q.Monic := by
      rw [hq]
      exact Polynomial.monic_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C (r j))
    have hqdeg : q.natDegree = m := by
      rw [hq]
      simp
    have hqeval : ∀ j, q.eval (r j) = 0 := by
      intro j
      rw [hq, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
    -- `p - q` is monic-cancelling, so has degree `< m`, yet vanishes at the `m` distinct points
    have hsub : p - q = 0 := by
      refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (p - q) hinj (fun j => ?_) ?_
      · simp [Polynomial.eval_sub, hroot j, hqeval j]
      · simpa using Polynomial.IsMonicOfDegree.natDegree_sub_lt hm.ne' ⟨hdeg, hmon⟩ ⟨hqdeg, hqmon⟩
    exact (sub_eq_zero.mp hsub).trans hq

end Work.WilC4aP
