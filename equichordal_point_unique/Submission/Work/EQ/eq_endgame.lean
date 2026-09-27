import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.eq_endgame_defs
import Submission.Work.EQ.eq_endgame_top
import Submission.Work.EQ.eval_of_natDegree_le_two

namespace Work.EQ

open Polynomial

theorem eq_endgame {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {c : ℂ} (hc : c ≠ 0) {D : Polynomial ℂ}
    (hD0 : Polynomial.eval 0 D ≠ 0)
    (hEND : ∀ u : ℂ,
      (Polynomial.eval (u / (Work.EQ.eqLam a : ℂ)) D - Polynomial.eval u D / (Work.EQ.eqLam a : ℂ)) ^ 2 *
        ((Work.EQ.eqLam a : ℂ) * Polynomial.eval u D - Polynomial.eval ((Work.EQ.eqLam a : ℂ) * u) D) ^ 2
      = ((a : ℂ)) ^ 2 * (c ^ 2 * u ^ 2 + Polynomial.eval u D ^ 2) *
        ((Work.EQ.eqLam a : ℂ) * Polynomial.eval (u / (Work.EQ.eqLam a : ℂ)) D -
          Polynomial.eval ((Work.EQ.eqLam a : ℂ) * u) D / (Work.EQ.eqLam a : ℂ)) ^ 2) : False := by
  set lam : ℂ := (eqLam a : ℂ) with hlam
  have hlam0 : lam ≠ 0 := by
    rw [hlam]; exact_mod_cast (ne_of_gt (endgame_lam_pos ha0 ha1))
  have hlam1 : lam ≠ 1 := by
    rw [hlam]; exact_mod_cast (ne_of_lt (endgame_lam_lt_one ha0 ha1))
  have ha_ne : (a : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ha0)
  have hlamsq : lam^2 ≠ 1 := by
    rw [hlam, ← Complex.ofReal_one, ← Complex.ofReal_pow, ne_eq, Complex.ofReal_inj]
    intro h
    have hlt := pow_lt_one₀ (le_of_lt (endgame_lam_pos ha0 ha1)) (endgame_lam_lt_one ha0 ha1)
      (by norm_num : (2:ℕ) ≠ 0)
    linarith
  have hlaminv : lam - 1/lam ≠ 0 := by
    intro h
    have h1 : lam = 1/lam := sub_eq_zero.mp h
    have h2 := congr_arg (fun z : ℂ => z * lam) h1
    rw [div_mul_cancel₀ (1:ℂ) hlam0, ← pow_two] at h2
    exact hlamsq h2
  by_cases hn : 3 ≤ D.natDegree
  · exact eq_endgame_top ha0 ha1 hEND hn
  · push_neg at hn
    have hD2 : D.natDegree ≤ 2 := by omega
    set d0 : ℂ := D.coeff 0 with hd0def
    set d1 : ℂ := D.coeff 1 with hd1def
    set d2 : ℂ := D.coeff 2 with hd2def
    have hd0 : d0 ≠ 0 := by
      rw [hd0def, Polynomial.coeff_zero_eq_eval_zero]; exact hD0
    have hDeval : ∀ u : ℂ, D.eval u = d0 + d1*u + d2*u^2 := by
      intro u
      rw [eval_of_natDegree_le_two hD2 u, ← hd0def, ← hd1def, ← hd2def]
    have h1m : (1:ℂ) - 1/lam ≠ 0 := by
      rw [sub_ne_zero, one_div]
      intro h
      exact hlam1 (inv_eq_one.mp h.symm)
    have hC1 : d0*(lam-1/lam) ≠ 0 := mul_ne_zero hd0 hlaminv
    have hCne : lam*d0 - d0/lam ≠ 0 := by
      have h : lam*d0 - d0/lam = d0*(lam-1/lam) := by ring
      rw [h]; exact hC1
    by_cases hd2 : d2 = 0
    · -- D has degree at most 1
      by_cases hd1 : d1 = 0
      · -- constant case
        have hDc : ∀ u : ℂ, D.eval u = d0 := by
          intro u; simp only [hDeval, hd1, hd2]; ring
        have key : ∀ u : ℂ,
            (d0-d0/lam)^2*(lam*d0-d0)^2
              = a^2*(c^2*u^2+d0^2)*(lam*d0-d0/lam)^2 := by
          intro u
          have h := hEND u
          simpa only [hDc] using h
        have hh : a^2*(c^2*1^2+d0^2)*(lam*d0-d0/lam)^2
            = a^2*(c^2*0^2+d0^2)*(lam*d0-d0/lam)^2 := by
          rw [← key 1, key 0]
        have hmain : a^2*c^2*(lam*d0-d0/lam)^2 = 0 := by
          have hh2 : a^2*(c^2+d0^2)*(lam*d0-d0/lam)^2
              = a^2*d0^2*(lam*d0-d0/lam)^2 := by
            have h := hh
            ring_nf at h ⊢
            exact h
          linear_combination hh2
        have hres : c = 0 := by
          rcases mul_eq_zero.mp hmain with h | h
          · rcases mul_eq_zero.mp h with h | h
            · exact absurd h (pow_ne_zero 2 ha_ne)
            · exact sq_eq_zero_iff.mp h
          · exact absurd h (pow_ne_zero 2 hCne)
        exact hc hres
      · -- linear case
        have hDl : ∀ u : ℂ, D.eval u = d0 + d1*u := by
          intro u; simp only [hDeval, hd2]; ring
        have hA : ∀ u : ℂ, D.eval (u/lam) - D.eval u/lam = d0*(1-1/lam) := by
          intro u; simp only [hDl]; ring
        have hB : ∀ u : ℂ, lam*D.eval u - D.eval (lam*u) = d0*(lam-1) := by
          intro u; simp only [hDl]; ring
        have hC : ∀ u : ℂ, lam*D.eval (u/lam) - D.eval (lam*u)/lam = d0*(lam-1/lam) := by
          intro u; simp only [hDl]; ring
        have key : ∀ u : ℂ,
            (d0*(1-1/lam))^2*(d0*(lam-1))^2
              = a^2*(c^2*u^2+(d0+d1*u)^2)*(d0*(lam-1/lam))^2 := by
          intro u
          have h := hEND u
          rw [hA u, hB u, hC u] at h
          simp only [hDl] at h
          exact h
        have hh : a^2*(c^2*1^2+(d0+d1*1)^2)*(d0*(lam-1/lam))^2
            = a^2*(c^2*(-1)^2+(d0+d1*(-1))^2)*(d0*(lam-1/lam))^2 :=
          (key 1).symm.trans (key (-1))
        have haC : a^2*(d0*(lam-1/lam))^2 ≠ 0 :=
          mul_ne_zero (pow_ne_zero 2 ha_ne) (pow_ne_zero 2 hC1)
        have hkey : (d0+d1)^2 = (d0-d1)^2 := by
          have hh' : a^2*(c^2+(d0+d1)^2)*(d0*(lam-1/lam))^2
              = a^2*(c^2+(d0-d1)^2)*(d0*(lam-1/lam))^2 := by
            have h := hh
            ring_nf at h ⊢
            exact h
          have h2 : (a^2*(d0*(lam-1/lam))^2) * (c^2+(d0+d1)^2)
              = (a^2*(d0*(lam-1/lam))^2) * (c^2+(d0-d1)^2) := by
            linear_combination hh'
          exact add_left_cancel (mul_left_cancel₀ haC h2)
        have hzero : d0*d1 = 0 := by
          linear_combination (1/4) * hkey
        rcases mul_eq_zero.mp hzero with h | h
        · exact hd0 h
        · exact hd1 h
    · -- quadratic case
      set u0 : ℂ := Complex.sqrt (d0/d2) with hu0def
      have hu0 : u0^2 = d0/d2 := by
        rw [hu0def, Complex.sqrt]
        exact Complex.cpow_nat_inv_pow (d0/d2) (by norm_num)
      have hu0sq : d2 * u0^2 = d0 := by
        rw [hu0]; field_simp
      have hA0 : D.eval (u0/lam) - D.eval u0/lam = d0*(1-1/lam)^2 := by
        simp only [hDeval, div_pow, mul_pow, hu0]
        field_simp
        ring
      have hB0 : lam*D.eval u0 - D.eval (lam*u0) = -(d0*(lam-1)^2) := by
        simp only [hDeval, div_pow, mul_pow, hu0]
        field_simp
        ring
      have hC0 : lam*D.eval (u0/lam) - D.eval (lam*u0)/lam = 0 := by
        simp only [hDeval, div_pow, mul_pow, hu0]
        field_simp
        ring
      have hm := hEND u0
      rw [hA0, hB0, hC0] at hm
      have hsq : (d0*(1-1/lam)^2)^2 * (-(d0*(lam-1)^2))^2 = 0 := by
        rw [hm]; ring
      have hne : (d0*(1-1/lam)^2)^2 * (-(d0*(lam-1)^2))^2 ≠ 0 := by
        refine mul_ne_zero (pow_ne_zero 2 ?_) (pow_ne_zero 2 ?_)
        · exact mul_ne_zero hd0 (pow_ne_zero 2 h1m)
        · exact neg_ne_zero.mpr (mul_ne_zero hd0 (pow_ne_zero 2 (sub_ne_zero.mpr hlam1)))
      exact hne hsq

end Work.EQ
