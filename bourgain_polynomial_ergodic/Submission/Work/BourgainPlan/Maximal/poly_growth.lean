import Mathlib

namespace Work.BourgainPlan.Maximal

open Filter Asymptotics Polynomial

/-- If `f ~[atTop] g` and `g` is eventually positive, then `f` is eventually between
`g / 2` and `2 * g`.  (Direct from the definition of asymptotic equivalence:
`f - g =o[atTop] g`.) -/
lemma isEquivalent_eventually_bounds {f g : ℝ → ℝ} (h : f ~[atTop] g)
    (hg : ∀ᶠ x in atTop, 0 < g x) :
    (∀ᶠ x in atTop, g x / 2 ≤ f x) ∧ (∀ᶠ x in atTop, f x ≤ 2 * g x) := by
  have h1 : ∀ᶠ x in atTop, ‖f x - g x‖ ≤ (1 / 2) * ‖g x‖ := by
    simpa using h.isLittleO.def (c := 1 / 2) (by norm_num)
  have h2 : ∀ᶠ x in atTop, ‖g x‖ = g x := hg.mono fun x hx => Real.norm_of_nonneg hx.le
  have h1' : ∀ᶠ x in atTop, |f x - g x| ≤ (1 / 2) * g x := by
    filter_upwards [h1, h2] with x hx1 hx2
    rw [Real.norm_eq_abs, hx2] at hx1
    exact hx1
  constructor
  · filter_upwards [h1'] with x hx1
    have hle := neg_le_abs (f x - g x)
    linarith
  · filter_upwards [h1', hg] with x hx1 hx3
    have hle := le_abs_self (f x - g x)
    linarith

/-- Growth bounds for a real polynomial which is nonnegative on `[0,∞)`: its leading coefficient is positive, its derivative grows at least like `u^(d-1)` and it grows at most like `u^d` beyond some `U ≥ 1`.  HINT: nonnegativity forces `0 < q.leadingCoeff`; then compare the leading term with the sum of the lower-order terms. -/
theorem poly_growth {q : Polynomial ℝ} (hnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ q.eval x)
    (hdeg : 1 ≤ q.natDegree) :
    ∃ (U c C₀ : ℝ), 1 ≤ U ∧ 0 < c ∧ 0 < C₀ ∧ 0 < q.leadingCoeff ∧
      (∀ u : ℝ, U ≤ u → c * u ^ (q.natDegree - 1) ≤ q.derivative.eval u) ∧
      (∀ u : ℝ, U ≤ u → q.eval u ≤ C₀ * u ^ q.natDegree) := by
  have hdpos : 0 < q.natDegree := by omega
  have hdR : (0 : ℝ) < (q.natDegree : ℝ) := by exact_mod_cast hdpos
  have hdegpos : 0 < q.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos]; exact hdpos
  -- nonnegativity on `[0,∞)` forces a positive leading coefficient
  have ha : 0 < q.leadingCoeff := by
    by_contra hcon
    push Not at hcon
    have htend := Polynomial.tendsto_atBot_of_leadingCoeff_nonpos q hdegpos hcon
    have hev1 : ∀ᶠ x : ℝ in atTop, q.eval x < 0 := htend.eventually (eventually_lt_atBot 0)
    have hev2 : ∀ᶠ x : ℝ in atTop, 0 ≤ q.eval x :=
      (eventually_ge_atTop (0 : ℝ)).mono fun x hx => hnn x hx
    obtain ⟨x, hx1, hx2⟩ := (hev1.and hev2).exists
    linarith
  -- `q.eval x ~ leadingCoeff * x ^ natDegree`
  have hq : (fun x : ℝ => q.eval x) ~[atTop]
      (fun x : ℝ => q.leadingCoeff * x ^ q.natDegree) :=
    Polynomial.isEquivalent_atTop_lead q
  have hgnn : ∀ᶠ x : ℝ in atTop, 0 < q.leadingCoeff * x ^ q.natDegree := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_pos ha (pow_pos hx _)
  have hup0 : ∀ᶠ x : ℝ in atTop, q.eval x ≤ 2 * (q.leadingCoeff * x ^ q.natDegree) :=
    (isEquivalent_eventually_bounds hq hgnn).2
  have hup : ∀ᶠ x : ℝ in atTop, q.eval x ≤ (2 * q.leadingCoeff) * x ^ q.natDegree := by
    filter_upwards [hup0] with x hx
    linarith [show 2 * (q.leadingCoeff * x ^ q.natDegree)
      = (2 * q.leadingCoeff) * x ^ q.natDegree from by ring]
  -- the derivative grows like `natDegree * leadingCoeff * x ^ (natDegree - 1)`
  have hderiv : (fun x : ℝ => q.derivative.eval x) ~[atTop]
      (fun x : ℝ => q.derivative.leadingCoeff * x ^ q.derivative.natDegree) :=
    Polynomial.isEquivalent_atTop_lead q.derivative
  have hderiv' : (fun x : ℝ => q.derivative.eval x) ~[atTop]
      (fun x : ℝ => (q.leadingCoeff * (q.natDegree : ℝ)) * x ^ (q.natDegree - 1)) := by
    refine hderiv.congr_right ?_
    exact Eventually.of_forall fun x => by
      rw [Polynomial.leadingCoeff_derivative, Polynomial.natDegree_derivative]
  have hgnn' : ∀ᶠ x : ℝ in atTop,
      0 < (q.leadingCoeff * (q.natDegree : ℝ)) * x ^ (q.natDegree - 1) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_pos (mul_pos ha hdR) (pow_pos hx _)
  have hlow0 : ∀ᶠ x : ℝ in atTop,
      ((q.leadingCoeff * (q.natDegree : ℝ)) * x ^ (q.natDegree - 1)) / 2
        ≤ q.derivative.eval x :=
    (isEquivalent_eventually_bounds hderiv' hgnn').1
  have hlow : ∀ᶠ x : ℝ in atTop,
      (q.leadingCoeff * (q.natDegree : ℝ) / 2) * x ^ (q.natDegree - 1)
        ≤ q.derivative.eval x := by
    filter_upwards [hlow0] with x hx
    linarith [show ((q.leadingCoeff * (q.natDegree : ℝ)) * x ^ (q.natDegree - 1)) / 2
      = (q.leadingCoeff * (q.natDegree : ℝ) / 2) * x ^ (q.natDegree - 1) from by ring]
  obtain ⟨U₁, hU₁⟩ := eventually_atTop.1 hlow
  obtain ⟨U₂, hU₂⟩ := eventually_atTop.1 hup
  refine ⟨max U₁ (max U₂ 1), q.leadingCoeff * (q.natDegree : ℝ) / 2, 2 * q.leadingCoeff,
    ?_, ?_, ?_, ha, ?_, ?_⟩
  · exact le_trans (le_max_right U₂ 1) (le_max_right U₁ (max U₂ 1))
  · have h := mul_pos ha hdR; linarith
  · linarith
  · intro u hu
    exact hU₁ u (le_trans (le_max_left U₁ (max U₂ 1)) hu)
  · intro u hu
    exact hU₂ u (le_trans (le_trans (le_max_left U₂ 1) (le_max_right U₁ (max U₂ 1))) hu)

end Work.BourgainPlan.Maximal
