import Mathlib.MeasureTheory.Function.L2Space
import Submission.Commons.Analysis.Measure.lintegral_lintegral_sub_mul
import Submission.Commons.Analysis.Measure.aemeasurable_sub_mul_prod

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}
local notation "𝔽" => EuclideanSpace ℝ (Fin d)

/-- Change of variables `x ↦ g - x` in a set-Lebesgue-integral.  (The map `x ↦ g - x` is a
measure-preserving bijection of an additive Haar measure, being the composition of a translation
with the negation.) -/
lemma lintegral_sub_indicator {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd G] [MeasurableNeg G] {μ : Measure G} [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
    (g : G) (s : Set G) (F : G → ENNReal) (hs : MeasurableSet s) :
    ∫⁻ x in s, F (g - x) ∂μ = ∫⁻ y in {y : G | g - y ∈ s}, F y ∂μ := by
  classical
  have hs' : MeasurableSet {y : G | g - y ∈ s} := hs.preimage (by measurability)
  have key : ∫⁻ x, s.indicator (fun x => F (g - x)) x ∂μ
      = ∫⁻ x, ({y : G | g - y ∈ s}).indicator F (g - x) ∂μ := by
    apply lintegral_congr
    intro x
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hx : x ∈ s
    · rw [if_pos hx, if_pos (show g - x ∈ {y : G | g - y ∈ s} from by
        rw [Set.mem_ofPred_eq, show g - (g - x) = x by abel]; exact hx)]
    · rw [if_neg hx, if_neg (show g - x ∉ {y : G | g - y ∈ s} from by
        rw [Set.mem_ofPred_eq, show g - (g - x) = x by abel]; exact hx)]
  rw [← lintegral_indicator hs (fun x => F (g - x)), key,
      lintegral_sub_left_eq_self (f := ({y : G | g - y ∈ s}).indicator F) g,
      lintegral_indicator hs' F]

/-- **Modulation average via a `L²` lower bound.**  If `Ψ` has `L²`-mass at least `c₂²` on the
unit cube `[-1,1]^d`, then the double average of `|F(ξ - η)|²|Ψ(ξ)|²` over `η ∈ [-2,2]^d`,
`ξ ∈ ℝ^d` dominates `c₂²` times the `L²`-mass of `F` on the unit cube. -/
theorem modulation_average_lintegral {d : ℕ} {c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    {F Ψ : EuclideanSpace ℝ (Fin d) → ℂ}
    (hF : MeasureTheory.MemLp F 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hΨ : MeasureTheory.MemLp Ψ 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hΨnorm : c₂ ^ 2 ≤ ∫ ξ in {x : EuclideanSpace ℝ (Fin d) | ∀ i, x i ∈ Set.Icc (-1:ℝ) 1}, ‖Ψ ξ‖ ^ 2) :
    ENNReal.ofReal (c₂ ^ 2) *
        ∫⁻ θ in {x : EuclideanSpace ℝ (Fin d) | ∀ i, x i ∈ Set.Icc (-1:ℝ) 1}, ENNReal.ofReal (‖F θ‖ ^ 2)
      ≤ ∫⁻ η in {x : EuclideanSpace ℝ (Fin d) | ∀ i, x i ∈ Set.Icc (-2:ℝ) 2},
          ∫⁻ ξ, ENNReal.ofReal (‖F (ξ - η)‖ ^ 2 * ‖Ψ ξ‖ ^ 2) := by
  classical
  set S1 : Set (EuclideanSpace ℝ (Fin d)) :=
    {x : EuclideanSpace ℝ (Fin d) | ∀ i, x i ∈ Set.Icc (-1:ℝ) 1} with hS1def
  set S2 : Set (EuclideanSpace ℝ (Fin d)) :=
    {x : EuclideanSpace ℝ (Fin d) | ∀ i, x i ∈ Set.Icc (-2:ℝ) 2} with hS2def
  set G : EuclideanSpace ℝ (Fin d) → ENNReal := fun θ => ENNReal.ofReal (‖F θ‖ ^ 2) with hGdef
  set H : EuclideanSpace ℝ (Fin d) → ENNReal := fun ξ => ENNReal.ofReal (‖Ψ ξ‖ ^ 2) with hHdef
  have hS1 : MeasurableSet S1 := by rw [hS1def]; measurability
  have hS2 : MeasurableSet S2 := by rw [hS2def]; measurability
  have hGa : AEMeasurable G (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    rw [hGdef]
    exact Measurable.comp_aemeasurable (g := fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2))
      (by measurability) hF.aemeasurable
  have hHa : AEMeasurable H (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    rw [hHdef]
    exact Measurable.comp_aemeasurable (g := fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2))
      (by measurability) hΨ.aemeasurable
  have hHfin : ∀ ξ, H ξ ≠ ∞ := by intro ξ; rw [hHdef]; exact ENNReal.ofReal_ne_top
  have hHrestrict : AEMeasurable H ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S1) :=
    hHa.mono_measure Measure.restrict_le_self
  have hsub : ∀ ξ ∈ S1, S1 ⊆ {u : EuclideanSpace ℝ (Fin d) | ξ - u ∈ S2} := by
    intro ξ hξ u hu
    rw [hS1def] at hξ hu
    rw [hS2def]
    intro i
    have h1 := hξ i
    have h2 := hu i
    rw [Set.mem_Icc] at h1 h2
    have h3 : (ξ - u) i = ξ i - u i := by simp
    rw [h3, Set.mem_Icc]
    exact ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
  have hd : ∀ ξ ∈ S1, ∫⁻ θ in S1, G θ ≤ ∫⁻ η in S2, G (ξ - η) := by
    intro ξ hξ
    rw [lintegral_sub_indicator ξ S2 G hS2]
    exact lintegral_mono_set (hsub ξ hξ)
  have hcoef : ENNReal.ofReal (c₂ ^ 2) ≤ ∫⁻ ξ in S1, H ξ := by
    have hint_vol : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => ‖Ψ ξ‖ ^ 2)
        (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
      (memLp_two_iff_integrable_sq_norm hΨ.aestronglyMeasurable).mp hΨ
    have hint : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => ‖Ψ ξ‖ ^ 2)
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S1) :=
      hint_vol.mono_measure Measure.restrict_le_self
    have hnn : 0 ≤ᵐ[((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S1)]
        (fun ξ : EuclideanSpace ℝ (Fin d) => ‖Ψ ξ‖ ^ 2) :=
      Filter.Eventually.of_forall (fun ξ => sq_nonneg _)
    rw [hHdef, ← ofReal_integral_eq_lintegral_ofReal hint hnn]
    exact ENNReal.ofReal_le_ofReal hΨnorm
  have hgoal : ENNReal.ofReal (c₂ ^ 2) * (∫⁻ θ in S1, G θ)
      ≤ ∫⁻ η in S2, ∫⁻ ξ, G (ξ - η) * H ξ := by
    rw [Commons.Analysis.Measure.lintegral_lintegral_sub_mul S2 hS2 hGa hHa]
    calc ENNReal.ofReal (c₂ ^ 2) * (∫⁻ θ in S1, G θ)
        ≤ (∫⁻ ξ in S1, H ξ) * (∫⁻ θ in S1, G θ) := mul_le_mul' hcoef le_rfl
      _ = ∫⁻ ξ in S1, H ξ * (∫⁻ θ in S1, G θ) :=
            (lintegral_mul_const'' (∫⁻ θ in S1, G θ) hHrestrict).symm
      _ ≤ ∫⁻ ξ in S1, H ξ * ∫⁻ η in S2, G (ξ - η) := by
          apply lintegral_mono_ae
          rw [ae_restrict_iff' hS1]
          filter_upwards with ξ hξ
          exact mul_le_mul' le_rfl (hd ξ hξ)
      _ ≤ ∫⁻ ξ, H ξ * ∫⁻ η in S2, G (ξ - η) := by
          have hmono := lintegral_mono_set (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
            (s := S1) (t := Set.univ) (f := fun ξ => H ξ * ∫⁻ η in S2, G (ξ - η))
            (Set.subset_univ S1)
          simpa only [Measure.restrict_univ] using hmono
  have hconv : (∫⁻ η in S2, ∫⁻ ξ, ENNReal.ofReal (‖F (ξ - η)‖ ^ 2 * ‖Ψ ξ‖ ^ 2))
      = ∫⁻ η in S2, ∫⁻ ξ, G (ξ - η) * H ξ := by
    apply lintegral_congr; intro η
    apply lintegral_congr; intro ξ
    rw [hGdef, hHdef, ENNReal.ofReal_mul (by positivity)]
  rw [hconv]
  exact hgoal

end Commons.Analysis.Fourier