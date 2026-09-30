import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Filter

namespace Work.BW

/-- A polynomial over `ℚ` that is eventually positive and eventually bounded above by `C·t^n`
along the naturals has degree at most `n`. -/
theorem natDegree_le_of_eventually_le_pow {p : Polynomial ℚ} {n : ℕ} {C : ℚ}
    (hpos : ∀ᶠ t : ℕ in Filter.atTop, 0 < p.eval (t : ℚ))
    (hupper : ∀ᶠ t : ℕ in Filter.atTop, p.eval (t : ℚ) ≤ C * (t : ℚ) ^ n) :
    p.natDegree ≤ n := by
  by_contra hcon
  have hlt : n < p.natDegree := not_le.mp hcon
  have hp_ne : p ≠ 0 := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hpos
    intro h
    have := hN N le_rfl
    rw [h] at this
    simp at this
  have hdeg_pos : 0 < p.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp (by omega)
  -- The leading coefficient of `p` is positive, since `p` is eventually positive.
  have hlc_pos : 0 < p.leadingCoeff := by
    by_contra hle'
    have hle : p.leadingCoeff ≤ 0 := le_of_not_gt hle'
    have hb : Tendsto (fun x : ℚ => p.eval x) atTop atBot :=
      Polynomial.tendsto_atBot_of_leadingCoeff_nonpos p hdeg_pos hle
    have hb2 : ∀ᶠ t : ℕ in atTop, p.eval (t : ℚ) < 0 :=
      (hb.comp tendsto_natCast_atTop_atTop).eventually (Filter.eventually_lt_atBot (0 : ℚ))
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hb2
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hpos
    have h1 := hM (max N M) (le_max_right _ _)
    have h2 := hN (max N M) (le_max_left _ _)
    linarith
  -- Subtract `C * X ^ n`; the result has the same degree and leading coefficient as `p`.
  have hq_deg_le : (Polynomial.C C * Polynomial.X ^ n).natDegree < p.natDegree :=
    lt_of_le_of_lt (Polynomial.natDegree_C_mul_X_pow_le C n) hlt
  have hq_deg : (p - Polynomial.C C * Polynomial.X ^ n).natDegree = p.natDegree :=
    Polynomial.natDegree_sub_eq_left_of_natDegree_lt hq_deg_le
  have hdeg_lt : (Polynomial.C C * Polynomial.X ^ n).degree < p.degree :=
    lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le n C)
      (by rw [Polynomial.degree_eq_natDegree hp_ne]; exact WithBot.coe_lt_coe.mpr hlt)
  have hq_lc : (p - Polynomial.C C * Polynomial.X ^ n).leadingCoeff = p.leadingCoeff :=
    Polynomial.leadingCoeff_sub_of_degree_lt hdeg_lt
  have hq_deg_pos : 0 < (p - Polynomial.C C * Polynomial.X ^ n).degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp (by rw [hq_deg]; omega)
  have hq_tendsto :
      Tendsto (fun t : ℕ => (p - Polynomial.C C * Polynomial.X ^ n).eval (t : ℚ)) atTop atTop :=
    (Polynomial.tendsto_atTop_of_leadingCoeff_nonneg (p - Polynomial.C C * Polynomial.X ^ n)
      hq_deg_pos (by rw [hq_lc]; exact le_of_lt hlc_pos)).comp
        tendsto_natCast_atTop_atTop
  have hev_pos :
      ∀ᶠ t : ℕ in atTop, 0 < (p - Polynomial.C C * Polynomial.X ^ n).eval (t : ℚ) :=
    hq_tendsto.eventually (Filter.eventually_gt_atTop (0 : ℚ))
  have hev_nonpos :
      ∀ᶠ t : ℕ in atTop, (p - Polynomial.C C * Polynomial.X ^ n).eval (t : ℚ) ≤ 0 := by
    filter_upwards [hupper] with t ht
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    linarith
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hev_pos
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev_nonpos
  have h1 := hM (max N M) (le_max_right _ _)
  have h2 := hN (max N M) (le_max_left _ _)
  linarith

end Work.BW
