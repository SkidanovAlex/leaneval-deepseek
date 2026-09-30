import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- A polynomial over `ℚ` whose leading coefficient is negative is eventually
negative on the natural numbers. -/
lemma eventually_eval_neg_of_leadingCoeff_neg {f : Polynomial ℚ} (hf : f.leadingCoeff < 0) :
    ∀ᶠ n : ℕ in Filter.atTop, f.eval (n : ℚ) < 0 := by
  rcases lt_or_ge 0 f.degree with hdeg | hdeg
  · have htend : Filter.Tendsto (fun x : ℚ => f.eval x) Filter.atTop Filter.atBot :=
      Polynomial.tendsto_atBot_of_leadingCoeff_nonpos f hdeg (le_of_lt hf)
    exact (htend.comp tendsto_natCast_atTop_atTop).eventually (Filter.Iio_mem_atBot (0 : ℚ))
  · have hle : f.degree ≤ 0 := hdeg
    have hnat : f.natDegree = 0 := Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr hle
    have hC : f = Polynomial.C f.leadingCoeff := by
      conv_lhs => rw [Polynomial.eq_C_of_degree_le_zero hle]
      rw [← hnat, Polynomial.coeff_natDegree]
    refine Filter.Eventually.of_forall fun n => ?_
    rw [hC, Polynomial.eval_C]
    exact hf

theorem leadingCoeff_le_of_eventually_le {p q : Polynomial ℚ}
    (hd : p.natDegree = q.natDegree)
    (h : ∀ᶠ n : ℕ in Filter.atTop, p.eval (n : ℚ) ≤ q.eval (n : ℚ)) :
    p.leadingCoeff ≤ q.leadingCoeff := by
  by_contra hcon
  rw [not_le] at hcon
  -- hcon : q.leadingCoeff < p.leadingCoeff
  have hcoeff : (q - p).coeff p.natDegree = q.leadingCoeff - p.leadingCoeff := by
    rw [Polynomial.coeff_sub]
    rw [show q.coeff p.natDegree = q.leadingCoeff by rw [hd, Polynomial.coeff_natDegree]]
    rw [Polynomial.coeff_natDegree]
  have hcoeff_ne : (q - p).coeff p.natDegree ≠ 0 := by
    rw [hcoeff]
    exact sub_ne_zero.mpr (ne_of_gt hcon).symm
  have hnatdeg_le : (q - p).natDegree ≤ p.natDegree := by
    simpa [← hd, max_self] using Polynomial.natDegree_sub_le q p
  have hnatdeg_ge : p.natDegree ≤ (q - p).natDegree := by
    by_contra hc
    rw [not_le] at hc
    exact hcoeff_ne (Polynomial.coeff_eq_zero_of_natDegree_lt hc)
  have hnatdeg : (q - p).natDegree = p.natDegree := le_antisymm hnatdeg_le hnatdeg_ge
  have hflc : (q - p).leadingCoeff < 0 := by
    rw [← Polynomial.coeff_natDegree, hnatdeg, hcoeff]
    linarith
  have h_event : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ (q - p).eval (n : ℚ) := by
    filter_upwards [h] with n hn
    simp only [Polynomial.eval_sub]
    linarith
  have hkey := eventually_eval_neg_of_leadingCoeff_neg hflc
  have hcontra : ∀ᶠ n : ℕ in Filter.atTop, False := by
    filter_upwards [hkey, h_event] with n hn hn'
    exact absurd hn' (not_le.mpr hn)
  exact hcontra.exists.elim fun _ hf => hf

end Work.BW
