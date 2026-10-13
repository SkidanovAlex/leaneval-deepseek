/-
Copyright: work module for the Elgindi finite-time singularity project.

# `N6Trans/Hon/TraceOsc`: the elementary oscillation lemmas

If `u ≥ 0` is differentiable on `(0,1)`, `∫₀¹ |u'| < ∞` and `∫₀¹ u/z < ∞`, then `u → 0` at
`0⁺` (`tendsto_zero_of_integrableOn_deriv_left`), and the analogous statement at `+∞`
(`tendsto_zero_of_integrableOn_deriv_atTop`).

The argument: the total oscillation of `u` on `(0,δ)` is at most `∫₀^δ |u'| → 0`; and
`∫₀^δ u/z < ∞` forces the infimum of `u` on `(0,δ)` to be `0` (a positive infimum `m` would
give `u/z ≥ m/z`, whose integral over `(0,δ)` diverges).  Hence `sup_{z<δ} u ≤ ∫₀^δ |u'|`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.TraceAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

set_option autoImplicit false

/-- **The oscillation argument at `0⁺`.**  If `u ≥ 0` is differentiable on `(0,1)` with
`∫₀¹ |u'| < ∞` and `∫₀¹ u/z < ∞`, then `u → 0` at `0⁺`. -/
theorem tendsto_zero_of_integrableOn_deriv_left {u : ℝ → ℝ}
    (hu : ∀ z ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ u z)
    (hnn : ∀ z ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ u z)
    (hdiv : IntegrableOn (fun z => u z / z) (Set.Ioo (0 : ℝ) 1))
    (hder : IntegrableOn (deriv u) (Set.Ioo (0 : ℝ) 1)) :
    Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hosc : ∀ {a b δ : ℝ}, 0 < a → a ≤ b → b < δ → δ < 1 →
      |u b - u a| ≤ ∫ x in Set.Ioo (0 : ℝ) δ, |deriv u x| := by
    intro a b δ ha hab hb hδ
    have hsu : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) 1 := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 (lt_trans hb hδ)⟩
    have hInt : IntervalIntegrable (deriv u) volume a b :=
      IntegrableOn.intervalIntegrable (IntegrableOn.mono_set hder hsu)
    have hFTC : ∫ x in a..b, deriv u x = u b - u a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => (hu x (hsu hx)).hasDerivAt) hInt
    have h1 : |u b - u a| ≤ ∫ x in a..b, |deriv u x| := by
      rw [← hFTC]
      exact intervalIntegral.abs_integral_le_integral_abs hab
    have h2 : (∫ x in a..b, |deriv u x|) ≤ ∫ x in Set.Ioo (0 : ℝ) δ, |deriv u x| := by
      rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      refine MeasureTheory.setIntegral_mono_set
        (IntegrableOn.mono_set (Integrable.abs hder) (fun x hx => ⟨hx.1, lt_trans hx.2 hδ⟩))
        ?_ ?_
      · exact Filter.Eventually.of_forall (fun x => abs_nonneg (deriv u x))
      · exact Filter.Eventually.of_forall (fun x hx => ⟨lt_trans ha hx.1, lt_trans hx.2 hb⟩)
    linarith
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ0, hδ1, hδ⟩ := exists_setIntegral_Ioo_abs_le hder (show (0 : ℝ) < ε / 2 by linarith)
  set C : ℝ := ∫ x in Set.Ioo (0 : ℝ) 1, u x / x with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact div_nonneg (hnn x hx) (le_of_lt hx.1)
  have hkey : ∀ z ∈ Set.Ioo (0 : ℝ) δ, u z < ε := by
    intro z hz
    by_contra hcon
    push_neg at hcon
    have hA : ∀ z' ∈ Set.Ioo (0 : ℝ) δ, ε / 2 ≤ u z' := by
      intro z' hz'
      have h1 : |u z' - u z| ≤ ∫ x in Set.Ioo (0 : ℝ) δ, |deriv u x| := by
        rcases le_total z' z with h | h
        · rw [abs_sub_comm]
          exact hosc (a := z') (b := z) (δ := δ) hz'.1 h hz.2 hδ1
        · exact hosc (a := z) (b := z') (δ := δ) hz.1 h hz'.2 hδ1
      have h2 := (abs_le.mp h1).1
      have h3 : u z' ≥ u z - ε / 2 := by linarith [h2, hδ]
      linarith [hcon, h3]
    have hlog : ∀ M : ℝ, ∀ᶠ a in 𝓝[>] (0 : ℝ), M < Real.log (δ / a) := by
      intro M
      have h1 : ∀ᶠ a in 𝓝[>] (0 : ℝ), Real.log a < Real.log δ - M :=
        Real.tendsto_log_nhdsGT_zero.eventually (eventually_lt_atBot _)
      filter_upwards [h1, self_mem_nhdsWithin] with a ha ha0
      rw [Real.log_div (ne_of_gt hδ0) (ne_of_gt ha0)]
      linarith
    have hlt : ∀ᶠ a in 𝓝[>] (0 : ℝ), a < δ := nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hδ0)
    have hpos' : ∀ᶠ a in 𝓝[>] (0 : ℝ), (0 : ℝ) < a := self_mem_nhdsWithin
    have hev : ∀ᶠ a in 𝓝[>] (0 : ℝ), (2 * C / ε < Real.log (δ / a)) ∧ a < δ ∧ 0 < a :=
      (hlog (2 * C / ε)).and (hlt.and hpos')
    obtain ⟨a, hlog_a, haδ, ha0⟩ := hev.exists
    have hId' : (∫ x in a..δ, (ε / 2) / x) = (ε / 2) * Real.log (δ / a) := by
      have h1 : (fun x : ℝ => (ε / 2) / x) = fun x : ℝ => (ε / 2) * x⁻¹ := by
        funext x; rw [div_eq_mul_inv]
      rw [h1, intervalIntegral.integral_const_mul, integral_inv_of_pos ha0 hδ0]
    have hpt : ∀ x ∈ Set.Ioo a δ, (ε / 2) / x ≤ u x / x := by
      intro x hx
      have hx0 : 0 < x := lt_trans ha0 hx.1
      rw [div_le_div_iff_of_pos_right hx0]
      exact hA x ⟨hx0, hx.2⟩
    have hIntc : IntervalIntegrable (fun x : ℝ => (ε / 2) / x) volume a δ := by
      refine ContinuousOn.intervalIntegrable ?_
      refine continuousOn_const.div continuousOn_id (fun x hx => ?_)
      rw [Set.uIcc_of_le (le_of_lt haδ)] at hx
      exact ne_of_gt (lt_of_lt_of_le ha0 hx.1)
    have hIntu : IntervalIntegrable (fun x : ℝ => u x / x) volume a δ := by
      refine IntegrableOn.intervalIntegrable (IntegrableOn.mono_set hdiv ?_)
      intro x hx
      rw [Set.uIcc_of_le (le_of_lt haδ)] at hx
      exact ⟨lt_of_lt_of_le ha0 hx.1, lt_of_le_of_lt hx.2 hδ1⟩
    have hcmp : (∫ x in a..δ, (ε / 2) / x) ≤ ∫ x in a..δ, u x / x :=
      intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt haδ) hIntc hIntu hpt
    have hup : (∫ x in a..δ, u x / x) ≤ C := by
      rw [intervalIntegral.integral_of_le (le_of_lt haδ),
        MeasureTheory.integral_Ioc_eq_integral_Ioo, hCdef]
      refine MeasureTheory.setIntegral_mono_set hdiv ?_ ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        exact div_nonneg (hnn x hx) (le_of_lt hx.1)
      · exact Filter.Eventually.of_forall (fun x hx => ⟨lt_trans ha0 hx.1, lt_trans hx.2 hδ1⟩)
    have hε2 : 0 < ε / 2 := by linarith
    have hkey2 : C < (ε / 2) * Real.log (δ / a) := by
      have := mul_lt_mul_of_pos_left hlog_a hε2
      have heq : (ε / 2) * (2 * C / ε) = C := by
        field_simp
      rwa [heq] at this
    have h3 : (ε / 2) * Real.log (δ / a) ≤ C := by
      rw [← hId']
      exact le_trans hcmp hup
    linarith
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hδ0)] with z hz1 hz2
  have hz : z ∈ Set.Ioo (0 : ℝ) 1 := ⟨hz1, lt_trans hz2 hδ1⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnn z hz)]
  exact hkey z ⟨hz1, hz2⟩

/-- **The oscillation argument at `+∞`.**  If `u ≥ 0` is differentiable on `(1,∞)` with
`∫₁^∞ |u'| < ∞` and `∫₁^∞ u/z < ∞`, then `u → 0` at `+∞`. -/
theorem tendsto_zero_of_integrableOn_deriv_atTop {u : ℝ → ℝ}
    (hu : ∀ z ∈ Set.Ioi (1 : ℝ), DifferentiableAt ℝ u z)
    (hnn : ∀ z ∈ Set.Ioi (1 : ℝ), 0 ≤ u z)
    (hdiv : IntegrableOn (fun z => u z / z) (Set.Ioi (1 : ℝ)))
    (hder : IntegrableOn (deriv u) (Set.Ioi (1 : ℝ))) :
    Tendsto u atTop (𝓝 0) := by
  have hosc : ∀ {R a b : ℝ}, 1 < R → R < a → a ≤ b →
      |u b - u a| ≤ ∫ x in Set.Ioi R, |deriv u x| := by
    intro R a b hR1 hRa hab
    have hsub : Set.uIcc a b ⊆ Set.Ioi (1 : ℝ) := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      simp only [Set.mem_Ioi]
      exact lt_of_lt_of_le (lt_trans hR1 hRa) hx.1
    have hInt : IntervalIntegrable (deriv u) volume a b :=
      IntegrableOn.intervalIntegrable (IntegrableOn.mono_set hder hsub)
    have hFTC : ∫ x in a..b, deriv u x = u b - u a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => (hu x (hsub hx)).hasDerivAt) hInt
    have h1 : |u b - u a| ≤ ∫ x in a..b, |deriv u x| := by
      rw [← hFTC]
      exact intervalIntegral.abs_integral_le_integral_abs hab
    have h2 : (∫ x in a..b, |deriv u x|) ≤ ∫ x in Set.Ioi R, |deriv u x| := by
      rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      refine MeasureTheory.setIntegral_mono_set
        (IntegrableOn.mono_set (Integrable.abs hder) (fun x hx => lt_trans hR1 hx)) ?_ ?_
      · exact Filter.Eventually.of_forall (fun x => abs_nonneg (deriv u x))
      · exact Filter.Eventually.of_forall (fun x hx => lt_trans hRa hx.1)
    linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R, hR1, hR⟩ := exists_setIntegral_Ioi_abs_le hder (show (0 : ℝ) < ε / 2 by linarith)
  set C : ℝ := ∫ x in Set.Ioi (1 : ℝ), u x / x with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact div_nonneg (hnn x hx) (le_of_lt (lt_trans zero_lt_one hx))
  have hRpos : 0 < R := lt_trans zero_lt_one hR1
  have hkey : ∀ z ∈ Set.Ioi R, u z < ε := by
    intro z hz
    by_contra hcon
    push_neg at hcon
    have hA : ∀ z' ∈ Set.Ioi R, ε / 2 ≤ u z' := by
      intro z' hz'
      have h1 : |u z' - u z| ≤ ∫ x in Set.Ioi R, |deriv u x| := by
        rcases le_total z' z with h | h
        · rw [abs_sub_comm]
          exact hosc (R := R) (a := z') (b := z) hR1 hz' h
        · exact hosc (R := R) (a := z) (b := z') hR1 hz h
      have h2 := (abs_le.mp h1).1
      have h3 : u z' ≥ u z - ε / 2 := by linarith [h2, hR]
      linarith [hcon, h3]
    have hlog : ∀ M : ℝ, ∀ᶠ S in atTop, M < Real.log (S / R) ∧ R < S := by
      intro M
      have h1 : ∀ᶠ S in atTop, Real.log R + M < Real.log S :=
        Real.tendsto_log_atTop.eventually (eventually_gt_atTop _)
      filter_upwards [h1, Filter.Ioi_mem_atTop R] with S hS hRS
      have hSpos : 0 < S := lt_of_lt_of_le hRpos (le_of_lt hRS)
      refine ⟨?_, hRS⟩
      rw [Real.log_div (x := S) (y := R) (ne_of_gt hSpos) (ne_of_gt hRpos)]
      linarith
    obtain ⟨S, hlogS, hRS⟩ := (hlog (2 * C / ε)).exists
    have hSpos : 0 < S := lt_of_lt_of_le hRpos (le_of_lt hRS)
    have hId' : (∫ x in R..S, (ε / 2) / x) = (ε / 2) * Real.log (S / R) := by
      have h1 : (fun x : ℝ => (ε / 2) / x) = fun x : ℝ => (ε / 2) * x⁻¹ := by
        funext x; rw [div_eq_mul_inv]
      rw [h1, intervalIntegral.integral_const_mul, integral_inv_of_pos hRpos hSpos]
    have hpt : ∀ x ∈ Set.Ioo R S, (ε / 2) / x ≤ u x / x := by
      intro x hx
      have hx0 : 0 < x := lt_trans hRpos hx.1
      rw [div_le_div_iff_of_pos_right hx0]
      exact hA x hx.1
    have hIntc : IntervalIntegrable (fun x : ℝ => (ε / 2) / x) volume R S := by
      refine ContinuousOn.intervalIntegrable ?_
      refine continuousOn_const.div continuousOn_id (fun x hx => ?_)
      rw [Set.uIcc_of_le (le_of_lt hRS)] at hx
      exact ne_of_gt (lt_of_lt_of_le hRpos hx.1)
    have hIntu : IntervalIntegrable (fun x : ℝ => u x / x) volume R S := by
      refine IntegrableOn.intervalIntegrable (IntegrableOn.mono_set hdiv ?_)
      intro x hx
      rw [Set.uIcc_of_le (le_of_lt hRS)] at hx
      exact lt_of_lt_of_le hR1 hx.1
    have hcmp : (∫ x in R..S, (ε / 2) / x) ≤ ∫ x in R..S, u x / x :=
      intervalIntegral.integral_mono_on_of_le_Ioo (le_of_lt hRS) hIntc hIntu hpt
    have hup : (∫ x in R..S, u x / x) ≤ C := by
      rw [intervalIntegral.integral_of_le (le_of_lt hRS),
        MeasureTheory.integral_Ioc_eq_integral_Ioo, hCdef]
      refine MeasureTheory.setIntegral_mono_set hdiv ?_ ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact div_nonneg (hnn x hx) (le_of_lt (lt_trans zero_lt_one hx))
      · exact Filter.Eventually.of_forall (fun x hx => lt_trans hR1 hx.1)
    have hε2 : 0 < ε / 2 := by linarith
    have hkey2 : C < (ε / 2) * Real.log (S / R) := by
      have := mul_lt_mul_of_pos_left hlogS hε2
      have heq : (ε / 2) * (2 * C / ε) = C := by
        field_simp
      rwa [heq] at this
    have h3 : (ε / 2) * Real.log (S / R) ≤ C := by
      rw [← hId']
      exact le_trans hcmp hup
    linarith
  refine ⟨R + 1, fun n hn => ?_⟩
  have hnR : n ∈ Set.Ioi R := by simp only [Set.mem_Ioi]; linarith
  have hn1 : n ∈ Set.Ioi (1 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnn n hn1)]
  exact hkey n hnR

end Work.FTS.StrongPersist.N6Trans.Hon
