import Mathlib
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.WinMass_basic

/-!
# The window-mass identity for `WinMass`

`WinMass f M₂ M₃ = ∑'_ℓ ∫_{[-2,2]} ‖H_ℓ(τ)‖² dτ` with `H_ℓ(τ) = Bsum f M₂ (ℓ + τ/M₃)`.
Substituting `τ = M₃ t` in each window and exchanging the sum with the integral (Tonelli, the
series being summable because the windows `Iwin M₃ ℓ` have bounded multiplicity), we obtain

`WinMass f M₂ M₃ = M₃ ∫_{[-2/M₃, 2/M₃]} Σ'_ℓ ‖Bsum f M₂ (ℓ + t)‖² dt`,

which is the form in which the local `L²`-mass of `Bsum` over the integer lattice is sampled.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- Translation change of variables for set integrals over a symmetric window:
`∫_{[-c,c]} G (d + t) dt = ∫_{[d-c,d+c]} G x dx` for `c ≥ 0`. -/
lemma win_mass_Icc_comp_add_left (G : ℝ → ℝ) {c d : ℝ} (hc : 0 ≤ c) :
    (∫ t in Set.Icc (-c) c, G (d + t)) = ∫ x in Set.Icc (d - c) (d + c), G x := by
  have h1 : (∫ t in Set.Icc (-c) c, G (d + t)) = ∫ t in (-c)..c, G (d + t) := by
    rw [intervalIntegral.integral_of_le (by linarith : -c ≤ c),
      MeasureTheory.setIntegral_congr_set MeasureTheory.Ioc_ae_eq_Icc]
  have h2 : (∫ x in (d - c)..(d + c), G x) = ∫ x in Set.Icc (d - c) (d + c), G x := by
    rw [intervalIntegral.integral_of_le (by linarith : d - c ≤ d + c),
      MeasureTheory.setIntegral_congr_set MeasureTheory.Ioc_ae_eq_Icc]
  rw [h1, intervalIntegral.integral_comp_add_left G d]
  rw [show d + -c = d - c from by ring]
  rw [h2]

/-- Scaling change of variables `t = τ/M₃` on the window `[-2,2]`:
`∫_{[-2,2]} G (a + τ/M₃) dτ = M₃ ∫_{[-2/M₃, 2/M₃]} G (a + t) dt` for `M₃ > 0`. -/
lemma win_mass_window_div (G : ℝ → ℝ) {M₃ a : ℝ} (hM₃ : 0 < M₃) :
    (∫ τ in Set.Icc (-2 : ℝ) 2, G (a + τ / M₃))
      = M₃ * ∫ t in Set.Icc (-(2 / M₃)) (2 / M₃), G (a + t) := by
  have hc : (0:ℝ) < 1 / M₃ := by positivity
  have h2c : (0:ℝ) < 2 / M₃ := by positivity
  have hpt : (∫ τ in Set.Icc (-2 : ℝ) 2, G (a + τ / M₃))
      = ∫ τ in Set.Icc (-2 : ℝ) 2, G (a + (1 / M₃) * τ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun τ _ => ?_)
    rw [show τ / M₃ = (1 / M₃) * τ from by ring]
  have hIcc : (∫ τ in Set.Icc (-2 : ℝ) 2, G (a + (1 / M₃) * τ))
      = ∫ τ in (-2 : ℝ)..2, G (a + (1 / M₃) * τ) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-2:ℝ) ≤ 2),
      MeasureTheory.setIntegral_congr_set MeasureTheory.Ioc_ae_eq_Icc]
  have hcomp : (∫ τ in (-2 : ℝ)..2, G (a + (1 / M₃) * τ))
      = M₃ * ∫ x in (a - 2 / M₃)..(a + 2 / M₃), G x := by
    have h := intervalIntegral.integral_comp_add_mul (a := (-2 : ℝ)) (b := (2 : ℝ))
      (c := 1 / M₃) G (ne_of_gt hc) a
    have hb1 : a + (1 / M₃) * (-2) = a - 2 / M₃ := by ring
    have hb2 : a + (1 / M₃) * 2 = a + 2 / M₃ := by ring
    rw [hb1, hb2] at h
    rw [h, smul_eq_mul, show (1 / M₃)⁻¹ = M₃ from by rw [one_div, inv_inv]]
  have hIcc' : (∫ x in (a - 2 / M₃)..(a + 2 / M₃), G x)
      = ∫ x in Set.Icc (a - 2 / M₃) (a + 2 / M₃), G x := by
    rw [intervalIntegral.integral_of_le (by linarith : a - 2 / M₃ ≤ a + 2 / M₃),
      MeasureTheory.setIntegral_congr_set MeasureTheory.Ioc_ae_eq_Icc]
  rw [hpt, hIcc, hcomp, win_mass_Icc_comp_add_left G (c := 2 / M₃) (d := a) h2c.le, hIcc']

theorem win_mass_eq {C₀ M₂ M₃ : ℝ} (hC₀ : 1 ≤ C₀) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {f : ℝ → ℝ} (hf : Continuous f) (hsup : SuppHyp C₀ f) :
    WinMass f M₂ M₃
      = M₃ * ∫ t in Set.Icc (-(2 / M₃)) (2 / M₃),
          (∑' ℓ : ℤ, ‖Bsum f M₂ ((ℓ : ℝ) + t)‖ ^ 2) := by
  set g : ℝ → ℝ := fun x => ‖Bsum f M₂ x‖ ^ 2 with hgdef
  have hgnn : ∀ x : ℝ, 0 ≤ g x := fun x => by rw [hgdef]; exact sq_nonneg _
  have hgint : Integrable g := by
    have hHcont : Continuous (Hprof f M₂) := Hprof_continuous hf M₂
    have hHcs : HasCompactSupport (Hprof f M₂) := Hprof_hasCompactSupport hsup hC₀ hM₂.le
    have hcontC : Continuous (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp hHcont
    have hcsC : HasCompactSupport (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) :=
      hHcs.comp_left (g := fun z : ℝ => (z : ℂ)) (by simp)
    have h := integrable_fourier_sq_of_continuous_hasCompactSupport hcontC hcsC
    refine h.congr ?_
    filter_upwards with x
    show ‖FourierTransform.fourier (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ)) x‖ ^ 2 = g x
    rw [show FourierTransform.fourier (fun u : ℝ => ((Hprof f M₂ u : ℝ) : ℂ))
        = fun x => Fhat (Hprof f M₂) x from rfl]
    show ‖Fhat (Hprof f M₂) x‖ ^ 2 = ‖Bsum f M₂ x‖ ^ 2
    rw [Bsum_eq_Fhat_Hprof hf hsup hC₀ hM₂ x]
  have hterm : ∀ ℓ : ℤ, (∫ τ in Set.Icc (-2 : ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2)
      = M₃ * ∫ t in Set.Icc (-(2 / M₃)) (2 / M₃), g ((ℓ : ℝ) + t) := by
    intro ℓ
    have hcongr : (∫ τ in Set.Icc (-2 : ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2)
        = ∫ τ in Set.Icc (-2 : ℝ) 2, g ((ℓ : ℝ) + τ / M₃) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun τ _ => ?_)
      show ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 = g ((ℓ : ℝ) + τ / M₃)
      rw [Hfun_eq_Bsum, hgdef]
    rw [hcongr, win_mass_window_div g hM₃ (a := (ℓ : ℝ))]
  have hIwinJ : ∀ ℓ : ℤ, (∫ x in Iwin M₃ ℓ, g x)
      = ∫ t in Set.Icc (-(2 / M₃)) (2 / M₃), g ((ℓ : ℝ) + t) := by
    intro ℓ
    have h2c : (0:ℝ) < 2 / M₃ := by positivity
    have h := win_mass_Icc_comp_add_left g (c := 2 / M₃) (d := (ℓ : ℝ)) h2c.le
    rw [Iwin]
    exact h.symm
  have hfin : ∀ s : Finset ℤ,
      (∑ ℓ ∈ s, ∫ x in Iwin M₃ ℓ, g x) ≤ (1 + 4 / M₃) * ∫ x, g x := by
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
        ≤ ∫ x, g x * (1 + 4 / M₃) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => ?_))
        (hgint.mul_const _) (Filter.Eventually.of_forall (fun x => ?_))
      · exact mul_nonneg (hgnn x)
          (Finset.sum_nonneg (fun ℓ _ => (Set.indicator_nonneg (fun _ _ => zero_le_one)) x))
      · exact mul_le_mul_of_nonneg_left (finset_sum_indicator_Iwin_le hM₃ x s) (hgnn x)
    have h3 : (∫ x, g x * (1 + 4 / M₃)) = (1 + 4 / M₃) * ∫ x, g x := by
      rw [MeasureTheory.integral_mul_const, mul_comm]
    rw [h1]
    exact h2.trans (le_of_eq h3)
  have hsumA : Summable (fun ℓ : ℤ => ∫ t in Set.Icc (-(2 / M₃)) (2 / M₃), g ((ℓ : ℝ) + t)) := by
    refine summable_of_sum_le (c := (1 + 4 / M₃) * ∫ x, g x)
      (fun ℓ => integral_nonneg (fun t => hgnn _)) (fun s => ?_)
    rw [Finset.sum_congr rfl (fun ℓ _ => (hIwinJ ℓ).symm)]
    exact hfin s
  have hswap : (∑' ℓ : ℤ, ∫ t in Set.Icc (-(2 / M₃)) (2 / M₃), g ((ℓ : ℝ) + t))
      = ∫ t in Set.Icc (-(2 / M₃)) (2 / M₃), ∑' ℓ : ℤ, g ((ℓ : ℝ) + t) := by
    have hFint : ∀ ℓ : ℤ,
        Integrable (fun t : ℝ => g ((ℓ : ℝ) + t))
          (volume.restrict (Set.Icc (-(2 / M₃)) (2 / M₃))) :=
      fun ℓ => (hgint.comp_add_left (ℓ : ℝ)).integrableOn
    have hFsum : Summable (fun ℓ : ℤ =>
        ∫ t : ℝ, ‖g ((ℓ : ℝ) + t)‖ ∂(volume.restrict (Set.Icc (-(2 / M₃)) (2 / M₃)))) := by
      refine hsumA.congr (fun ℓ => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
      simp only [Real.norm_of_nonneg (hgnn ((ℓ : ℝ) + t))]
    exact MeasureTheory.integral_tsum_of_summable_integral_norm
      (μ := volume.restrict (Set.Icc (-(2 / M₃)) (2 / M₃)))
      (F := fun (ℓ : ℤ) (t : ℝ) => g ((ℓ : ℝ) + t)) hFint hFsum
  have hmain : WinMass f M₂ M₃
      = M₃ * ∫ t in Set.Icc (-(2 / M₃)) (2 / M₃), ∑' ℓ : ℤ, g ((ℓ : ℝ) + t) := by
    rw [WinMass, tsum_congr hterm, tsum_mul_left, hswap]
  rw [hmain]

end

end Work.GM.Affine
