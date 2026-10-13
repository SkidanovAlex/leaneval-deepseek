import Mathlib

namespace Work.WilC4aP

lemma eq_of_root_and_closest {m : ℕ} {p : Polynomial ℂ} {η : Fin m → ℂ} {k : Fin m} {Y : ℂ}
    (hfac : p = ∏ j : Fin m, (Polynomial.X - Polynomial.C (η j)))
    (hroot : p.eval Y = 0)
    (hclose : ∀ i, i ≠ k → ‖Y - η i‖ > ‖Y - η k‖) :
    Y = η k := by
  -- `Y` is a root of `p`, hence a root of one of the linear factors
  have hprod : ∏ j : Fin m, (Y - η j) = 0 := by
    rw [hfac, Polynomial.eval_prod] at hroot
    simpa using hroot
  have hex : ∃ j, Y - η j = 0 := by simpa [Finset.prod_eq_zero_iff] using hprod
  obtain ⟨j, hj⟩ := hex
  rw [sub_eq_zero] at hj
  by_cases hjk : j = k
  · rw [hj, hjk]
  · have hlt := hclose j hjk
    rw [hj, sub_self, norm_zero] at hlt
    exact absurd hlt (not_lt.mpr (norm_nonneg (η j - η k)))

end Work.WilC4aP
