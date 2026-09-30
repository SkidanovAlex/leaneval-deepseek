import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MeasureTheory
open scoped ENNReal

/-- The layer cake formula for a *measurable* `ℝ≥0∞`-valued function: the integral of `F`
equals the integral over the positive halfline of the measures of the superlevel sets
`{x | ENNReal.ofReal t ≤ F x}`.

This is the core of `layerCakeENNRealLe`, stated for a genuinely measurable function. -/
private theorem layerCake_of_measurable {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : α → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂μ = ∫⁻ t in Set.Ioi 0, μ {x | ENNReal.ofReal t ≤ F x} := by
  set R : α → ℝ := fun x => (F x).toReal with hRdef
  set A : Set α := {x | F x = ⊤} with hAdef
  have hA_meas : MeasurableSet A := by
    rw [hAdef]; exact hF (measurableSet_singleton ⊤)
  have hR_meas : Measurable R := by
    rw [hRdef]; exact hF.ennreal_toReal
  -- pointwise decomposition of `F` into its real part and its `⊤`-part
  have hpoint : ∀ x, F x = ENNReal.ofReal (R x) + ⊤ * (A.indicator (1 : α → ℝ≥0∞) x) := by
    intro x
    by_cases hx : F x = ⊤
    · have hxA : x ∈ A := by rw [hAdef]; exact hx
      rw [Set.indicator_of_mem hxA]
      simp [hRdef, hx]
    · have hxA : x ∉ A := by rw [hAdef]; exact hx
      rw [Set.indicator_of_notMem hxA]
      simp only [mul_zero, add_zero]
      rw [hRdef]
      exact (ENNReal.ofReal_toReal hx).symm
  have hL : ∫⁻ x, F x ∂μ = ∫⁻ x, ENNReal.ofReal (R x) ∂μ + ⊤ * μ A := by
    rw [show (fun x => F x)
        = (fun x => ENNReal.ofReal (R x) + ⊤ * (A.indicator (1 : α → ℝ≥0∞) x)) from
      funext hpoint]
    rw [lintegral_add_left hR_meas.ennreal_ofReal]
    rw [lintegral_const_mul (f := A.indicator (1 : α → ℝ≥0∞)) ⊤
        ((measurable_const : Measurable (1 : α → ℝ≥0∞)).indicator hA_meas)]
    rw [lintegral_indicator_one hA_meas]
  -- the level sets decompose as the good part together with the `⊤`-part
  have hmeasure : ∀ t, 0 < t → μ {x | ENNReal.ofReal t ≤ F x} = μ {a | t ≤ R a} + μ A := by
    intro t ht
    have hset : {x | ENNReal.ofReal t ≤ F x} = A ∪ {a | t ≤ R a} := by
      ext x
      by_cases hx : F x = ⊤
      · have hxA : x ∈ A := by rw [hAdef]; exact hx
        simp only [Set.mem_ofPred_eq, Set.mem_union, hxA, true_or, iff_true]
        rw [hx]; exact le_top
      · have hxA : x ∉ A := by rw [hAdef]; exact hx
        simp only [Set.mem_ofPred_eq, Set.mem_union, hxA, false_or]
        rw [← ENNReal.ofReal_toReal hx, ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg,
          hRdef]
    have hdisj : Disjoint A {a | t ≤ R a} := by
      rw [Set.disjoint_left]
      intro x hxA hxr
      have hFtop : F x = ⊤ := hxA
      have hR0 : R x = 0 := by rw [hRdef]; simp [hFtop]
      simp only [Set.mem_ofPred_eq] at hxr
      rw [hR0] at hxr
      linarith
    rw [hset, measure_union hdisj (hR_meas measurableSet_Ici), add_comm]
  have hRnn : 0 ≤ᵐ[μ] R := ae_of_all μ (fun x => by rw [hRdef]; exact ENNReal.toReal_nonneg)
  have hRlin : ∫⁻ x, ENNReal.ofReal (R x) ∂μ = ∫⁻ t in Set.Ioi 0, μ {a | t ≤ R a} :=
    lintegral_eq_lintegral_meas_le μ hRnn hR_meas.aemeasurable
  have hRHS : ∫⁻ t in Set.Ioi 0, μ {x | ENNReal.ofReal t ≤ F x}
      = (∫⁻ t in Set.Ioi 0, μ {a | t ≤ R a}) + ⊤ * μ A := by
    have hcongr : ∫⁻ t in Set.Ioi 0, μ {x | ENNReal.ofReal t ≤ F x}
        = ∫⁻ t in Set.Ioi 0, (μ {a | t ≤ R a} + μ A) :=
      setLIntegral_congr_fun measurableSet_Ioi (fun t ht => hmeasure t ht)
    rw [hcongr, lintegral_add_right (fun t => μ {a | t ≤ R a}) measurable_const,
      setLIntegral_const, Real.volume_Ioi, mul_comm]
  calc ∫⁻ x, F x ∂μ
      = ∫⁻ x, ENNReal.ofReal (R x) ∂μ + ⊤ * μ A := hL
    _ = (∫⁻ t in Set.Ioi 0, μ {a | t ≤ R a}) + ⊤ * μ A := by rw [hRlin]
    _ = ∫⁻ t in Set.Ioi 0, μ {x | ENNReal.ofReal t ≤ F x} := hRHS.symm

theorem layerCakeENNRealLe {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SFinite μ] (F : α → ℝ≥0∞) (hF : AEMeasurable F μ) :
    ∫⁻ x, F x ∂μ = ∫⁻ t in Set.Ioi 0, μ {x | ENNReal.ofReal t ≤ F x} := by
  obtain ⟨F', hF'_meas, hF'_eq⟩ : ∃ F' : α → ℝ≥0∞, Measurable F' ∧ F =ᵐ[μ] F' :=
    ⟨hF.mk F, hF.measurable_mk, hF.ae_eq_mk⟩
  have h1 : ∫⁻ x, F x ∂μ = ∫⁻ x, F' x ∂μ := lintegral_congr_ae hF'_eq
  have h2 : ∫⁻ t in Set.Ioi 0, μ {x | ENNReal.ofReal t ≤ F x}
      = ∫⁻ t in Set.Ioi 0, μ {x | ENNReal.ofReal t ≤ F' x} := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    apply measure_congr
    filter_upwards [hF'_eq] with x hx
    rw [hx]
  rw [h1, h2, layerCake_of_measurable μ F' hF'_meas]

end Work.BW
