import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

/-- For a sequence `u : ℕ → ℝ` bounded below by `0`, and a real number `x` with
`x ≤ liminf u`, the `ℝ≥0∞`-valued `liminf` of the coerced sequence dominates `ENNReal.ofReal x`.
This is the pointwise (order-theoretic) ingredient of Fatou's lemma: it transfers a bound
against the real `liminf` into a bound against the `ℝ≥0∞` `liminf`. -/
lemma ofReal_le_liminf_ofReal {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) {x : ℝ}
    (hxu : x ≤ Filter.liminf u Filter.atTop) :
    ENNReal.ofReal x ≤ Filter.liminf (fun n => ENNReal.ofReal (u n)) Filter.atTop := by
  rw [Filter.liminf_eq_iSup_iInf_of_nat]
  have key : ∀ y < x, ENNReal.ofReal y ≤ ⨆ n, ⨅ i, ⨅ (_ : i ≥ n), ENNReal.ofReal (u i) := by
    intro y hy
    have hbdd : Filter.IsBoundedUnder (fun x1 x2 : ℝ => x2 ≤ x1) Filter.atTop u :=
      Filter.isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hu)
    have hyu : ∀ᶠ n in Filter.atTop, y < u n :=
      Filter.gt_mem_sets_of_limsInf_gt hbdd (hy.trans_le hxu)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hyu
    have h1 : ENNReal.ofReal y ≤ ⨅ k, ⨅ (_ : k ≥ N), ENNReal.ofReal (u k) :=
      le_iInf fun k => le_iInf fun hk => ENNReal.ofReal_le_ofReal (le_of_lt (hN k hk))
    have h2 : (⨅ k, ⨅ (_ : k ≥ N), ENNReal.ofReal (u k))
        ≤ ⨆ n, ⨅ i, ⨅ (_ : i ≥ n), ENNReal.ofReal (u i) :=
      le_iSup (fun n => ⨅ i, ⨅ (_ : i ≥ n), ENNReal.ofReal (u i)) N
    exact h1.trans h2
  by_cases hS : (⨆ n, ⨅ i, ⨅ (_ : i ≥ n), ENNReal.ofReal (u i)) = ⊤
  · simp [hS]
  · rw [ENNReal.ofReal_le_iff_le_toReal hS]
    refine le_of_forall_lt fun c hc => ?_
    obtain ⟨y, hcy, hyx⟩ := exists_between hc
    exact hcy.trans_le ((ENNReal.ofReal_le_iff_le_toReal hS).1 (key y hyx))

theorem integrable_and_integral_le_liminf {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {u : ℕ → α → ℝ} {h : α → ℝ} {D : ℝ}
    (hu : ∀ n, MeasureTheory.Integrable (u n) μ)
    (hu_nn : ∀ n, ∀ᵐ a ∂μ, 0 ≤ u n a)
    (hD : ∀ n, ∫ a, u n a ∂μ ≤ D) (hD0 : 0 ≤ D)
    (hh_meas : MeasureTheory.AEStronglyMeasurable h μ)
    (hh_nn : ∀ᵐ a ∂μ, 0 ≤ h a)
    (hle : ∀ᵐ a ∂μ, h a ≤ Filter.liminf (fun n => u n a) Filter.atTop) :
    MeasureTheory.Integrable h μ ∧
      ∫ a, h a ∂μ ≤ Filter.liminf (fun n => ∫ a, u n a ∂μ) Filter.atTop := by
  classical
  -- all the `u n` are nonnegative, simultaneously, almost everywhere
  have hu_nn_all : ∀ᵐ a ∂μ, ∀ n, 0 ≤ u n a := MeasureTheory.ae_all_iff.2 hu_nn
  -- pointwise comparison of `ofReal h` with the `ℝ≥0∞`-valued `liminf` of the `u n`
  have hVle : ∀ᵐ a ∂μ,
      ENNReal.ofReal (h a) ≤ Filter.liminf (fun n => ENNReal.ofReal (u n a)) Filter.atTop := by
    filter_upwards [hu_nn_all, hh_nn, hle] with a hn _ ha
    exact ofReal_le_liminf_ofReal hn ha
  -- Fatou's lemma for the `ℝ≥0∞`-valued functions `ofReal ∘ u n`
  have hFatou : ∫⁻ a, Filter.liminf (fun n => ENNReal.ofReal (u n a)) Filter.atTop ∂μ
      ≤ Filter.liminf (fun n => ∫⁻ a, ENNReal.ofReal (u n a) ∂μ) Filter.atTop :=
    MeasureTheory.lintegral_liminf_le' fun n => (hu n).1.aemeasurable.ennreal_ofReal
  have hrew : Filter.liminf (fun n => ∫⁻ a, ENNReal.ofReal (u n a) ∂μ) Filter.atTop
      = Filter.liminf (fun n => ENNReal.ofReal (∫ a, u n a ∂μ)) Filter.atTop :=
    Filter.liminf_congr (Filter.Eventually.of_forall fun n =>
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hu n) (hu_nn n)).symm)
  have hchain : ∫⁻ a, ENNReal.ofReal (h a) ∂μ
      ≤ Filter.liminf (fun n => ENNReal.ofReal (∫ a, u n a ∂μ)) Filter.atTop :=
    (MeasureTheory.lintegral_mono_ae hVle).trans (hFatou.trans_eq hrew)
  -- the `ℝ≥0∞`-valued `liminf` is bounded by `ofReal D`
  have hDle : Filter.liminf (fun n => ENNReal.ofReal (∫ a, u n a ∂μ)) Filter.atTop
      ≤ ENNReal.ofReal D := by
    rw [Filter.liminf_eq_iSup_iInf_of_nat]
    refine iSup_le fun n =>
      (iInf_le _ n).trans ((iInf_le _ le_rfl).trans (ENNReal.ofReal_le_ofReal (hD n)))
  have hfin : ∫⁻ a, ENNReal.ofReal (h a) ∂μ < ⊤ :=
    lt_of_le_of_lt (hchain.trans hDle) ENNReal.ofReal_lt_top
  -- hence `h` is integrable
  have henorm : ∫⁻ a, ‖h a‖ₑ ∂μ = ∫⁻ a, ENNReal.ofReal (h a) ∂μ := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [hh_nn] with a ha
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg ha]
  have hint : MeasureTheory.Integrable h μ := by
    refine ⟨hh_meas, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm, henorm]
    exact hfin
  refine ⟨hint, ?_⟩
  have hint_eq : ∫ a, h a ∂μ = (∫⁻ a, ENNReal.ofReal (h a) ∂μ).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae hh_nn hh_meas
  have htoReal : (Filter.liminf (fun n => ENNReal.ofReal (∫ a, u n a ∂μ)) Filter.atTop).toReal
      = Filter.liminf (fun n => ∫ a, u n a ∂μ) Filter.atTop := by
    have h1 := ENNReal.liminf_toReal_eq (f := Filter.atTop)
      (u := fun n => ENNReal.ofReal (∫ a, u n a ∂μ))
      (b := ENNReal.ofReal D) ENNReal.ofReal_ne_top
      (Filter.Eventually.of_forall fun n => ENNReal.ofReal_le_ofReal (hD n))
    have h2 : (fun n => (ENNReal.ofReal (∫ a, u n a ∂μ)).toReal)
        = fun n => ∫ a, u n a ∂μ :=
      funext fun n => ENNReal.toReal_ofReal (MeasureTheory.integral_nonneg_of_ae (hu_nn n))
    rw [h2] at h1
    exact h1.symm
  rw [hint_eq, ← htoReal]
  exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hDle) hchain

end Work.FTS.EllExist.Honesty
