import Mathlib
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.WinMass_basic
import Submission.Work.GM.Affine.Hfun_sq_integral_le
import Submission.Work.GM.Affine.integrable_Fhat_sq

/-!
# The elementary window bound for `WinMass`

`WinMass` is the `M₃`-multiple of the sum of the local `L²`-masses of `Bsum f M₂ = Fhat (Hprof)`
over the windows `Iwin M₃ ℓ = [ℓ - 2/M₃, ℓ + 2/M₃]`.  Each real `x` lies in at most `1 + 4/M₃` of
those windows (`tsum_indicator_Iwin_le`), so

`WinMass f M₂ M₃ ≤ (M₃ + 4) ∫ u, (Hprof f M₂ u)²`.

This is the crude half of the local/sampling input to `WinMass_core`; it is what covers the case
`M₃ ≲ M₂` once combined with the band-limited sampling bound (which covers `M₃ ≫ M₂`).
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

theorem WinMass_window_le {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {M₂ M₃ : ℝ} (hM₂ : 0 < M₂)
    (hM₃ : 0 < M₃) {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f)
    (hsup : SuppHyp C₀ f) :
    WinMass f M₂ M₃ ≤ (M₃ + 4) * ∫ u, (Hprof f M₂ u) ^ 2 := by
  set g : ℝ → ℝ := fun x => ‖Bsum f M₂ x‖ ^ 2 with hgdef
  have hHcont : Continuous (Hprof f M₂) := Hprof_continuous hf M₂
  have hHcs : HasCompactSupport (Hprof f M₂) := Hprof_hasCompactSupport hsup hC₀ hM₂.le
  have hcsC : HasCompactSupport (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) :=
    hHcs.comp_left (g := fun z : ℝ => (z : ℂ)) (by simp)
  have hcontC : Continuous (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hHcont
  have hgint : Integrable g := by
    have h := integrable_fourier_sq_of_continuous_hasCompactSupport hcontC hcsC
    refine h.congr ?_
    filter_upwards with x
    show ‖FourierTransform.fourier (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) x‖ ^ 2 = g x
    have h1 : FourierTransform.fourier (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ))
        = fun x => Fhat (Hprof f M₂) x := rfl
    rw [h1]
    show ‖Fhat (Hprof f M₂) x‖ ^ 2 = ‖Bsum f M₂ x‖ ^ 2
    rw [Bsum_eq_Fhat_Hprof hf hsup hC₀ hM₂ x]
  have hFc : Continuous (Fhat f) := continuous_fhat hf hcs
  have hBcont : Continuous (Bsum f M₂) := by
    unfold Bsum
    refine continuous_finsetSum _ (fun m₂ _ => ?_)
    exact (continuous_const.mul (hFc.comp (continuous_const.mul continuous_id)))
  have hgc : Continuous g := by rw [hgdef]; exact (hBcont.norm.pow 2)
  have hterm : ∀ ℓ : ℤ, (∫ τ in Set.Icc (-2 : ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2)
      = M₃ * ∫ x in Iwin M₃ ℓ, g x := by
    intro ℓ
    have hc : (0:ℝ) < 1/M₃ := by positivity
    have h := window_mul_Icc g (c := 1/M₃) (d := (ℓ:ℝ)) hc
    have hL : (∫ τ in Set.Icc (-2 : ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2)
        = ∫ τ in Set.Icc (-2 : ℝ) 2, g ((ℓ:ℝ) + (1/M₃) * τ) := by
      refine setIntegral_congr_fun measurableSet_Icc (fun τ _ => ?_)
      show ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 = g ((ℓ:ℝ) + (1/M₃) * τ)
      rw [hgdef]
      have harg : (ℓ:ℝ) + (1/M₃) * τ = (ℓ:ℝ) + τ/M₃ := by ring
      rw [harg]
      rfl
    have hI : Iwin M₃ ℓ = Set.Icc ((ℓ:ℝ) - 2 * (1/M₃)) ((ℓ:ℝ) + 2 * (1/M₃)) := by
      rw [Iwin]; congr 1 <;> ring
    have hIf : (∫ x in Iwin M₃ ℓ, g x)
        = ∫ x in Set.Icc ((ℓ:ℝ) - 2 * (1/M₃)) ((ℓ:ℝ) + 2 * (1/M₃)), g x := by rw [hI]
    rw [hL, hIf, ← h,
      show M₃ * ((1/M₃) * ∫ τ in Set.Icc (-2 : ℝ) 2, g ((ℓ:ℝ) + (1/M₃) * τ))
        = (M₃ * (1/M₃)) * ∫ τ in Set.Icc (-2 : ℝ) 2, g ((ℓ:ℝ) + (1/M₃) * τ) from by ring]
    rw [mul_one_div, div_self (ne_of_gt hM₃), one_mul]
  have hWM : WinMass f M₂ M₃ = M₃ * ∑' ℓ : ℤ, ∫ x in Iwin M₃ ℓ, g x := by
    rw [WinMass, tsum_congr hterm, tsum_mul_left]
  -- the finite-window sums are bounded by the total mass with multiplicity `1 + 4/M₃`
  have hfin : ∀ s : Finset ℤ, (∑ ℓ ∈ s, ∫ x in Iwin M₃ ℓ, g x) ≤ (1 + 4/M₃) * ∫ x, g x := by
    intro s
    have h1 : (∑ ℓ ∈ s, ∫ x in Iwin M₃ ℓ, g x)
        = ∫ x, g x * (∑ ℓ ∈ s, (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x) := by
      have hpt : ∀ ℓ ∈ s, (∫ x in Iwin M₃ ℓ, g x)
          = ∫ x, g x * (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x := by
        intro ℓ _
        rw [(MeasureTheory.integral_indicator (μ := (volume : Measure ℝ)) (f := g)
          (s := Iwin M₃ ℓ) measurableSet_Icc).symm]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        by_cases hx : x ∈ Iwin M₃ ℓ
        · simp only [Set.indicator_of_mem hx, mul_one]
        · simp only [Set.indicator_of_notMem hx, mul_zero]
      rw [Finset.sum_congr rfl hpt]
      rw [← MeasureTheory.integral_finsetSum]
      · refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        show (∑ i ∈ s, g x * (Iwin M₃ i).indicator (fun _ => (1:ℝ)) x)
            = g x * (∑ ℓ ∈ s, (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x)
        rw [Finset.mul_sum]
      · intro ℓ _
        refine (hgint.indicator (Iwin_measurable M₃ ℓ)).congr ?_
        filter_upwards with x
        by_cases hx : x ∈ Iwin M₃ ℓ
        · simp only [Set.indicator_of_mem hx, mul_one]
        · simp only [Set.indicator_of_notMem hx, mul_zero]
    have h2 : (∫ x, g x * (∑ ℓ ∈ s, (Iwin M₃ ℓ).indicator (fun _ => (1:ℝ)) x))
        ≤ ∫ x, g x * (1 + 4/M₃) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => ?_))
        (hgint.mul_const _) (Filter.Eventually.of_forall (fun x => ?_))
      · exact mul_nonneg (sq_nonneg _)
          (Finset.sum_nonneg (fun ℓ _ => (Set.indicator_nonneg (fun _ _ => zero_le_one)) x))
      · exact mul_le_mul_of_nonneg_left (finset_sum_indicator_Iwin_le hM₃ x s)
          (show (0:ℝ) ≤ g x from by rw [hgdef]; exact sq_nonneg _)
    have h3 : (∫ x, g x * (1 + 4/M₃)) = (1 + 4/M₃) * ∫ x, g x := by
      rw [MeasureTheory.integral_mul_const, mul_comm]
    rw [h1]
    exact h2.trans (le_of_eq h3)
  have hsummable : Summable (fun ℓ : ℤ => ∫ x in Iwin M₃ ℓ, g x) :=
    summable_of_sum_le (fun ℓ => integral_nonneg (fun x => sq_nonneg _)) hfin
  have hS : (∑' ℓ : ℤ, ∫ x in Iwin M₃ ℓ, g x) ≤ (1 + 4/M₃) * ∫ x, g x :=
    le_of_tendsto hsummable.hasSum (Filter.Eventually.of_forall hfin)
  have hfinal : M₃ * (∑' ℓ : ℤ, ∫ x in Iwin M₃ ℓ, g x) ≤ (M₃ + 4) * ∫ x, g x := by
    have h4 : M₃ * ((1 + 4/M₃) * ∫ x, g x) = (M₃ + 4) * ∫ x, g x := by
      field_simp
    rw [← h4]
    exact mul_le_mul_of_nonneg_left hS hM₃.le
  rw [hWM, show ∫ u, (Hprof f M₂ u) ^ 2 = ∫ x, g x from ?_]
  · exact hfinal
  · rw [hgdef]
    exact (integral_normSq_Bsum_eq_integral_Hprof_sq hf hsup hC₀ hM₂).symm

end

end Work.GM.Affine
