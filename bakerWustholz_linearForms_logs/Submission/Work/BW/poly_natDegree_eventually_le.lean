import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- A polynomial `Q` which is eventually nonnegative and eventually bounded above by a polynomial
`P` has `natDegree Q ≤ natDegree P`. (If `deg Q > deg P` then the leading coefficient of `Q` is
positive — otherwise `Q` would be negative for large `t` — so `Q - P → +∞`, contradicting
`Q ≤ P` eventually.) Used to compare the degrees of the ray Hilbert polynomials of `q` and of the
cut ideal `p + (Q)`, given only `dim (R/q)_{tD} ≤ dim (R/(p+(Q)))_{tD}` for large `t`. -/
theorem poly_natDegree_eventually_le {P Q : Polynomial ℚ}
    (h : ∀ᶠ t : ℕ in Filter.atTop, Q.eval (t : ℚ) ≤ P.eval (t : ℚ))
    (hQ : ∀ᶠ t : ℕ in Filter.atTop, 0 ≤ Q.eval (t : ℚ)) :
    Q.natDegree ≤ P.natDegree := by
  by_contra hcon
  rw [not_le] at hcon
  -- `Q` has degree at least `P.natDegree + 1 ≥ 1`, hence positive degree.
  have hdegQ : 0 < Q.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos]
    omega
  -- If the leading coefficient of `Q` were negative, `Q` would be negative for large `t`,
  -- contradicting eventual nonnegativity.
  have hlcQ : 0 ≤ Q.leadingCoeff := by
    by_contra hneg
    rw [not_le] at hneg
    have h_ev : ∀ᶠ x : ℚ in Filter.atTop, Q.eval x < 0 :=
      (Polynomial.tendsto_atBot_of_leadingCoeff_nonpos Q hdegQ hneg.le).eventually
        (Filter.eventually_lt_atBot 0)
    obtain ⟨t, ht1, ht2⟩ := (h_ev.natCast_atTop.and hQ).exists
    linarith
  have hdegP : P.degree < Q.degree := Polynomial.degree_lt_degree hcon
  -- `Q - P` has the same degree and leading coefficient as `Q`, so it tends to `+∞`.
  have hdegR : 0 < (Q - P).degree := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt hdegP]
    exact hdegQ
  have hlcR : 0 ≤ (Q - P).leadingCoeff := by
    rw [Polynomial.leadingCoeff_sub_of_degree_lt hdegP]
    exact hlcQ
  have h_ev : ∀ᶠ x : ℚ in Filter.atTop, 0 < (Q - P).eval x :=
    (Polynomial.tendsto_atTop_of_leadingCoeff_nonneg (Q - P) hdegR hlcR).eventually
      (Filter.eventually_gt_atTop 0)
  obtain ⟨t, ht1, ht2⟩ := (h_ev.natCast_atTop.and h).exists
  rw [Polynomial.eval_sub] at ht1
  linarith

end Work.BW
