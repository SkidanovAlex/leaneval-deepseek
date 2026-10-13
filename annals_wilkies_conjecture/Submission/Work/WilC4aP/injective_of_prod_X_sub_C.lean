import Mathlib

namespace Work.WilC4aP

lemma injective_of_prod_X_sub_C {m : ℕ} {p : Polynomial ℂ} (hmon : p.Monic) {a : Fin m → ℂ}
    (hfac : p = ∏ j : Fin m, (Polynomial.X - Polynomial.C (a j)))
    (hsep : ∀ w : ℂ, p.eval w = 0 → p.derivative.eval w ≠ 0) :
    Function.Injective a := by
  intro i j hij
  by_contra hne
  have hji : j ≠ i := fun h => hne h.symm
  set r : ℂ := a i with hr
  have haj : a j = r := by rw [hr]; exact hij.symm
  set q : Polynomial ℂ := ∏ l ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (a l)) with hq
  -- split off the factor `X - C (a i) = X - C r`
  have hp : p = (Polynomial.X - Polynomial.C r) * q := by
    rw [hfac, hq]
    rw [Fintype.prod_eq_mul_prod_compl i (fun l => Polynomial.X - Polynomial.C (a l))]
    rw [show ({i}ᶜ : Finset (Fin m)) = Finset.univ.erase i from by
      rw [Finset.compl_eq_univ_sdiff, Finset.sdiff_singleton_eq_erase]]
  -- `q` vanishes at `r`, because the index `j` contributes a zero factor
  have hqeval : q.eval r = 0 := by
    rw [hq, Polynomial.eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩) ?_
    simp [haj]
  -- hence the derivative of `p` vanishes at `r`
  have hderiv : p.derivative.eval r = 0 := by
    rw [hp, Polynomial.derivative_mul, Polynomial.derivative_X_sub_C]
    simp [hqeval]
  -- but `r` is a root of `p`
  have hroot : p.eval r = 0 := by
    rw [hp]
    simp
  exact hsep r hroot hderiv

end Work.WilC4aP
