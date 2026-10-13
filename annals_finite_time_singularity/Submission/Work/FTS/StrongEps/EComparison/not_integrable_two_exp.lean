import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

/-!
# An integrable (square of a) two-exponential combination must be identically zero

We prove

`not_integrable_two_exp` : if `r2 < r1` and `t ↦ (c1 * exp (r1 * t) + c2 * exp (r2 * t)) ^ 2`
is integrable on `ℝ`, then `c1 = 0` and `c2 = 0`.

The mathematical content is purely growth: a nonzero exponential coefficient forces a bound
`≥ c > 0` of the integrand on a half-line, and an integrable function cannot dominate a
positive constant on a set of infinite measure.  The two halves of `ℝ` are handled by the two
elementary "tail" lemmas `not_eventually_ge_const` and `not_eventually_ge_const_atBot`; the
asymptotic lower bounds at `±∞` are extracted from `exp ((r2 - r1) * t) → 0` (respectively
`exp ((r1 - r2) * t) → 0` at `-∞`).
-/

/-- An integrable function cannot dominate a positive constant on a half-line `[T, ∞)`. -/
lemma not_eventually_ge_const {G : ℝ → ℝ} (hint : MeasureTheory.Integrable G) :
    ¬ (∃ c : ℝ, 0 < c ∧ ∃ T : ℝ, ∀ t : ℝ, T ≤ t → c ≤ G t) := by
  rintro ⟨c, hc, T, hT⟩
  have hG : MeasureTheory.Integrable G (MeasureTheory.volume.restrict (Set.Ioi T)) :=
    hint.integrableOn
  have hae : ∀ᵐ a ∂(MeasureTheory.volume.restrict (Set.Ioi T)), ‖(c : ℝ)‖ ≤ G a := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with a ha
    rw [Real.norm_eq_abs, abs_of_pos hc]
    exact hT a (le_of_lt ha)
  have hconst : MeasureTheory.Integrable (fun _ : ℝ => c)
      (MeasureTheory.volume.restrict (Set.Ioi T)) :=
    MeasureTheory.Integrable.mono' hG measurable_const.aestronglyMeasurable hae
  have hkey := (MeasureTheory.integrableOn_const_iff (C := c) (s := Set.Ioi T)
      (μ := MeasureTheory.volume)).mp hconst
  rcases hkey with h0 | hfin
  · exact hc.ne' (enorm_eq_zero.mp h0)
  · rw [Real.volume_Ioi] at hfin
    exact lt_irrefl _ hfin

/-- An integrable function cannot dominate a positive constant on a half-line `(-∞, S]`. -/
lemma not_eventually_ge_const_atBot {G : ℝ → ℝ} (hint : MeasureTheory.Integrable G) :
    ¬ (∃ c : ℝ, 0 < c ∧ ∃ S : ℝ, ∀ t : ℝ, t ≤ S → c ≤ G t) := by
  rintro ⟨c, hc, S, hS⟩
  have hG : MeasureTheory.Integrable G (MeasureTheory.volume.restrict (Set.Iic S)) :=
    hint.integrableOn
  have hae : ∀ᵐ a ∂(MeasureTheory.volume.restrict (Set.Iic S)), ‖(c : ℝ)‖ ≤ G a := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Iic]
    filter_upwards with a ha
    rw [Real.norm_eq_abs, abs_of_pos hc]
    exact hS a ha
  have hconst : MeasureTheory.Integrable (fun _ : ℝ => c)
      (MeasureTheory.volume.restrict (Set.Iic S)) :=
    MeasureTheory.Integrable.mono' hG measurable_const.aestronglyMeasurable hae
  have hkey := (MeasureTheory.integrableOn_const_iff (C := c) (s := Set.Iic S)
      (μ := MeasureTheory.volume)).mp hconst
  rcases hkey with h0 | hfin
  · exact hc.ne' (enorm_eq_zero.mp h0)
  · rw [Real.volume_Iic] at hfin
    exact lt_irrefl _ hfin

/-- The exact factorisation of the two-term exponential combination. -/
private lemma two_exp_sq_eq (r1 r2 c1 c2 t : ℝ) :
    (c1 * Real.exp (r1 * t) + c2 * Real.exp (r2 * t)) ^ 2
      = Real.exp (2 * r1 * t) * (c1 + c2 * Real.exp ((r2 - r1) * t)) ^ 2 := by
  have h1 : Real.exp ((r2 - r1) * t) * Real.exp (r1 * t) = Real.exp (r2 * t) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : c2 * Real.exp (r2 * t) = Real.exp (r1 * t) * (c2 * Real.exp ((r2 - r1) * t)) := by
    rw [← h1]; ring
  have h3 : Real.exp (2 * r1 * t) = Real.exp (r1 * t) ^ 2 := by
    rw [show (2 : ℝ) * r1 * t = r1 * t + r1 * t from by ring, Real.exp_add]; ring
  rw [h2, h3]; ring

/-- At `+∞` the top exponential of a two-term combination dominates: if its coefficient `c1`
is nonzero and its rate `r1` is nonnegative, the square is bounded below by a positive
constant on a half-line. -/
private lemma eventually_ge_of_exp_tendsto_zero {r1 r2 c1 c2 : ℝ} (h : r2 < r1)
    (hc1 : c1 ≠ 0) (hr1 : 0 ≤ r1) :
    ∃ c : ℝ, 0 < c ∧ ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      c ≤ (c1 * Real.exp (r1 * t) + c2 * Real.exp (r2 * t)) ^ 2 := by
  have hsub : r2 - r1 < 0 := by linarith
  have htend : Filter.Tendsto (fun t : ℝ => (r2 - r1) * t) Filter.atTop Filter.atBot :=
    (Filter.tendsto_const_mul_atBot_of_neg hsub).2 Filter.tendsto_id
  have hexp : Filter.Tendsto (fun t : ℝ => Real.exp ((r2 - r1) * t)) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp htend
  have hlin : Filter.Tendsto (fun t : ℝ => c1 + c2 * Real.exp ((r2 - r1) * t))
      Filter.atTop (nhds c1) := by
    have := (hexp.const_mul c2).const_add c1
    simpa using this
  have hsq : Filter.Tendsto (fun t : ℝ => (c1 + c2 * Real.exp ((r2 - r1) * t)) ^ 2)
      Filter.atTop (nhds (c1 ^ 2)) := hlin.pow 2
  have hc1sq : (0 : ℝ) < c1 ^ 2 := sq_pos_of_ne_zero hc1
  have hev1 : ∀ᶠ t : ℝ in Filter.atTop,
      c1 ^ 2 / 2 < (c1 + c2 * Real.exp ((r2 - r1) * t)) ^ 2 :=
    (tendsto_order.1 hsq).1 (c1 ^ 2 / 2) (by linarith)
  have hev2 : ∀ᶠ t : ℝ in Filter.atTop, (0 : ℝ) ≤ t := Filter.eventually_ge_atTop 0
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (hev1.and hev2)
  refine ⟨c1 ^ 2 / 2, by linarith, T, ?_⟩
  intro t ht
  obtain ⟨hb1, hb2⟩ := hT t ht
  have hge1 : (1 : ℝ) ≤ Real.exp (2 * r1 * t) := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith)
  rw [two_exp_sq_eq]
  have hsqnn : 0 ≤ (c1 + c2 * Real.exp ((r2 - r1) * t)) ^ 2 := sq_nonneg _
  have h2 : (c1 + c2 * Real.exp ((r2 - r1) * t)) ^ 2
      ≤ Real.exp (2 * r1 * t) * (c1 + c2 * Real.exp ((r2 - r1) * t)) ^ 2 := by
    calc (c1 + c2 * Real.exp ((r2 - r1) * t)) ^ 2
        = 1 * (c1 + c2 * Real.exp ((r2 - r1) * t)) ^ 2 := by ring
      _ ≤ Real.exp (2 * r1 * t) * (c1 + c2 * Real.exp ((r2 - r1) * t)) ^ 2 :=
          mul_le_mul_of_nonneg_right hge1 hsqnn
  linarith

/-- The `-∞` twin of `eventually_ge_of_exp_tendsto_zero`: if the *bottom* exponential
coefficient `c2` is nonzero and its rate `r2` is nonpositive, the square is bounded below by
a positive constant on a half-line at `-∞`. -/
private lemma eventually_ge_atBot_of_exp {r1 r2 c1 c2 : ℝ} (h : r2 < r1)
    (hc2 : c2 ≠ 0) (hr2 : r2 ≤ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ S : ℝ, ∀ t : ℝ, t ≤ S →
      c ≤ (c1 * Real.exp (r1 * t) + c2 * Real.exp (r2 * t)) ^ 2 := by
  obtain ⟨c, hc, T, hT⟩ := eventually_ge_of_exp_tendsto_zero (r1 := -r2) (r2 := -r1)
    (c1 := c2) (c2 := c1) (by linarith) hc2 (by linarith)
  refine ⟨c, hc, -T, ?_⟩
  intro t ht
  have ht' : T ≤ -t := by linarith
  have h := hT (-t) ht'
  have heq : (c2 * Real.exp ((-r2) * (-t)) + c1 * Real.exp ((-r1) * (-t))) ^ 2
      = (c1 * Real.exp (r1 * t) + c2 * Real.exp (r2 * t)) ^ 2 := by
    rw [neg_mul_neg, neg_mul_neg]; ring
  rw [heq] at h
  exact h

/-- A single nonzero exponential term has a non-integrable square over `ℝ`. -/
lemma single_exp_not_integrable {c r : ℝ} (hc : c ≠ 0) :
    ¬ MeasureTheory.Integrable (fun t : ℝ => (c * Real.exp (r * t)) ^ 2) := by
  intro hint
  have hc2 : (0 : ℝ) < c ^ 2 := sq_pos_of_ne_zero hc
  rcases le_or_gt 0 r with hr | hr
  · refine not_eventually_ge_const hint ⟨c ^ 2, hc2, 0, ?_⟩
    intro t ht
    have he : (1 : ℝ) ≤ Real.exp (r * t) := Real.one_le_exp (by nlinarith)
    have hs : (1 : ℝ) ≤ (Real.exp (r * t)) ^ 2 := one_le_pow₀ he
    calc c ^ 2 = c ^ 2 * 1 := by ring
      _ ≤ c ^ 2 * (Real.exp (r * t)) ^ 2 := mul_le_mul_of_nonneg_left hs (sq_nonneg c)
      _ = (c * Real.exp (r * t)) ^ 2 := by ring
  · refine not_eventually_ge_const_atBot hint ⟨c ^ 2, hc2, 0, ?_⟩
    intro t ht
    have he : (1 : ℝ) ≤ Real.exp (r * t) := Real.one_le_exp (by nlinarith)
    have hs : (1 : ℝ) ≤ (Real.exp (r * t)) ^ 2 := one_le_pow₀ he
    calc c ^ 2 = c ^ 2 * 1 := by ring
      _ ≤ c ^ 2 * (Real.exp (r * t)) ^ 2 := mul_le_mul_of_nonneg_left hs (sq_nonneg c)
      _ = (c * Real.exp (r * t)) ^ 2 := by ring

theorem not_integrable_two_exp {r1 r2 c1 c2 : ℝ} (h : r2 < r1)
    (hint : MeasureTheory.Integrable (fun t : ℝ => (c1 * Real.exp (r1 * t) + c2 * Real.exp (r2 * t)) ^ 2)) :
    c1 = 0 ∧ c2 = 0 := by
  by_cases hc1 : c1 = 0
  · -- a single (bottom) exponential remains
    have hc2 : c2 = 0 := by
      by_contra hc2ne
      exact single_exp_not_integrable hc2ne (by simpa [hc1] using hint)
    exact ⟨hc1, hc2⟩
  · exfalso
    -- `+∞` forces `r1 < 0`
    have hr1 : r1 < 0 := by
      by_contra hlt
      exact not_eventually_ge_const hint
        (eventually_ge_of_exp_tendsto_zero h hc1 (not_lt.mp hlt))
    -- then `c2 ≠ 0` would force `0 < r2`, contradicting `r2 < r1 < 0`
    have hc2 : c2 = 0 := by
      by_contra hc2ne
      have hpos : 0 < r2 := by
        by_contra hle
        exact not_eventually_ge_const_atBot hint
          (eventually_ge_atBot_of_exp h hc2ne (not_lt.mp hle))
      linarith
    exact single_exp_not_integrable hc1 (by simpa [hc2] using hint)

end Work.FTS.StrongEps.EComparison
