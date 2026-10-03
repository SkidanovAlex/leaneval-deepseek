import Mathlib
import Submission.Work.FIArea2.SevenSix.quad_B_integrable
import Submission.Work.FIArea2.SevenSix.quad_pointwise_le

namespace Work.FIArea2.SevenSix

open MeasureTheory Set

-- Integrability of the joint (r,w)-integrand arising in the FI (7.6) computation, needed for Fubini.
-- `0 ≤ f` continuous, vanishing on `(-∞,0]`, compactly supported, and `γ² < 1`.
-- Route: with `Q(w) = w²-2γw+1 ≥ 1-γ² =: c > 0`, a support bound `R ≥ 1` of `f` and `M ≥ f`,
-- one has, for `r, w > 0`,
--   `f(r²Q(w))/√w ≤ 1_{r<√(R/c)} · (M R^{3/8} r^{-3/4}) · (Q(w)^{-3/8} w^{-1/2})`,
-- and the right-hand side is a product of an `L¹` function of `r` (supported in `(0,√(R/c))`,
-- with `r^{-3/4} ∈ L¹` near `0`) and an `L¹` function of `w` (`Q(w)^{-3/8} w^{-1/2}` decays like
-- `w^{-5/4}` at infinity and like `w^{-1/2}` near `0`).  `Integrable.mul_prod` + `Integrable.mono'`
-- on `(volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))` — which is `volume` restricted to
-- the quadrant by `Measure.prod_restrict` — give the claim.
set_option linter.unusedVariables false in
theorem quad_integrable (f : ℝ → ℝ) (γ : ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfc : Continuous f)
    (hfsupp : ∀ x, x ≤ 0 → f x = 0) (hcc : HasCompactSupport f) (hγ : γ ^ 2 < 1) :
    MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => f (p.1 ^ 2 * (p.2 ^ 2 - 2 * γ * p.2 + 1)) / Real.sqrt p.2)
      (Set.Ioi 0 ×ˢ Set.Ioi 0) := by
  classical
  have hc : 0 < 1 - γ ^ 2 := by nlinarith
  -- a support bound `R ≥ 1`: `f` vanishes on `[R, ∞)`
  obtain ⟨C, hC⟩ := hcc.isCompact.isBounded.exists_norm_le
  obtain ⟨R, hR1, hR⟩ : ∃ R : ℝ, 1 ≤ R ∧ ∀ x, R ≤ x → f x = 0 := by
    refine ⟨max C 1 + 1, by linarith [le_max_right C 1], ?_⟩
    intro x hx
    by_contra hne
    have hxt : x ∈ tsupport f := subset_tsupport f (Function.mem_support.mpr hne)
    have hle := hC x hxt
    have hx0 : 0 ≤ x := by linarith [le_max_left C 1, le_max_right C 1]
    rw [Real.norm_eq_abs, abs_of_nonneg hx0] at hle
    linarith [le_max_left C 1]
  -- an upper bound `M ≥ f`
  obtain ⟨C', hC'⟩ := (hcc.isCompact.image hfc).isBounded.exists_norm_le
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, f x ≤ M := by
    refine ⟨max C' 0, le_max_right _ _, ?_⟩
    intro x
    by_cases hx : x ∈ Function.support f
    · have hxt : x ∈ tsupport f := subset_tsupport f hx
      have hle := hC' (f x) ⟨x, hxt, rfl⟩
      rw [Real.norm_eq_abs] at hle
      exact le_trans (abs_le.mp hle).2 (le_max_left _ _)
    · rw [Function.mem_support, not_not] at hx
      rw [hx]; exact le_max_right _ _
  set L : ℝ := Real.sqrt (R / (1 - γ ^ 2)) with hLdef
  have hRpos : 0 < R := by linarith
  have hLpos : 0 < L := by
    rw [hLdef]; exact Real.sqrt_pos_of_pos (div_pos hRpos hc)
  set g1 : ℝ → ℝ := fun r => M * R ^ ((3 : ℝ) / 8) * r ^ (-(3 : ℝ) / 4) with hg1def
  set A : ℝ → ℝ := Set.indicator (Iio L) g1 with hAdef
  set B : ℝ → ℝ :=
    fun w => (w ^ 2 - 2 * γ * w + 1) ^ (-(3 : ℝ) / 8) * w ^ (-(1 : ℝ) / 2) with hBdef
  -- `A` is integrable on `(0,∞)`
  have hg1int : IntegrableOn g1 (Ioo 0 L) := by
    have hbase : IntegrableOn (fun r : ℝ => r ^ (-(3 : ℝ) / 4)) (Ioo 0 L) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff (s := -(3 : ℝ) / 4) hLpos).mpr (by norm_num)
    rw [hg1def]
    rw [IntegrableOn] at hbase ⊢
    simpa only [mul_assoc] using hbase.const_mul (M * R ^ ((3 : ℝ) / 8))
  have hAint : IntegrableOn A (Ioi 0) := by
    rw [hAdef]
    exact (integrableOn_indicator_iff measurableSet_Iio).mpr (by
      rw [Set.Iio_inter_Ioi]; exact hg1int)
  -- `B` is integrable on `(0,∞)`
  have hBint : IntegrableOn B (Ioi 0) := by
    rw [hBdef]; exact quad_B_integrable γ hγ
  -- reduce to the product measure
  rw [MeasureTheory.IntegrableOn, MeasureTheory.Measure.volume_eq_prod,
    ← MeasureTheory.Measure.prod_restrict]
  refine (MeasureTheory.Integrable.mul_prod hAint hBint).mono' ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    have h1 : Measurable (fun p : ℝ × ℝ => f (p.1 ^ 2 * (p.2 ^ 2 - 2 * γ * p.2 + 1))) :=
      hfc.measurable.comp (by fun_prop)
    have h2 : Measurable (fun p : ℝ × ℝ => Real.sqrt p.2) :=
      Real.continuous_sqrt.measurable.comp measurable_snd
    exact h1.div h2
  · rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)]
    exact Filter.Eventually.of_forall (fun p hp => by
      have := quad_pointwise_le f γ M R hf0 hM hR1 hR hγ p.1 hp.1 p.2 hp.2
      simpa only [hAdef, hBdef, hg1def, hLdef] using this)

end Work.FIArea2.SevenSix
