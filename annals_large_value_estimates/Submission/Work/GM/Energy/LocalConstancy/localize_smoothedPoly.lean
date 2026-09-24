import Mathlib
import Submission.Work.GM.Energy.Defs
import Submission.Work.GM.Energy.LocalConstancy.Bump
import Submission.Work.GM.Energy.LocalConstancy.Phi
import Submission.Work.GM.Energy.LocalConstancy.dtp_eq_integral
import Submission.Work.GM.Energy.LocalConstancy.tail_integral_rpow

namespace Work.GM.Energy.LocalConstancy

open Complex Finset MeasureTheory
open scoped BigOperators FourierTransform
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **GM Lemma 11.3** (locality of a smoothed Dirichlet polynomial): the value of
`D t = smoothedPoly N b t = Σ_{n∈[N,2N]} w(n/N) b_n n^{it}` at a point is controlled by the
average of `‖D‖` over the window `[t-K,t+K]`, up to a `K^{-m}` multiple of the coefficient mass.
(Proof route: the exact identity `D t = ∫ ψ̂(ξ) D(t+ξ) dξ` for a fixed smooth bump `ψ`
with `ψ(log n / 2π) = 1` for all `n ∈ [N,2N]` (translated by `log N / 2π`), then restrict the
`ξ`-integral to `|ξ| ≤ K` using the rapid decay of `ψ̂` from
`Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay`.) -/
theorem localize_smoothedPoly (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) → ∀ (K : ℝ), 1 ≤ K → ∀ t : ℝ,
        ‖Submission.LargeValues.smoothedPoly N b t‖ ≤
          C * (∫ u in t - K..t + K, ‖Submission.LargeValues.smoothedPoly N b u‖)
            + C / K ^ (m : ℝ) * (∑ n ∈ Finset.Icc N (2 * N), ‖b n‖) := by
  -- the bump bound `|w| ≤ Cw`
  obtain ⟨Cw, hCw0, hCw⟩ := Submission.LargeValues.bumpW_deriv_bdd 0
  -- the two Fourier bounds for the bump: a uniform one and rapid decay
  set B : ℝ := ∫ x, ‖PsiBump x‖ with hBdef
  have hB0 : 0 ≤ B := integral_nonneg fun x => norm_nonneg _
  have hBbound : ∀ ξ : ℝ, ‖𝓕 PsiBump ξ‖ ≤ B := fun ξ => PsiBump_fourier_le_integral ξ
  obtain ⟨Cd, hCd0, hCd⟩ := PsiBump_fourier_decay (m + 1)
  refine ⟨max 1 (max B (2 * Cw * Cd)), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro N hN b hb K hK t
  set C : ℝ := max 1 (max B (2 * Cw * Cd)) with hCdef
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK
  have hBC : B ≤ C := by
    rw [hCdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have h2C : 2 * Cw * Cd ≤ C := by
    rw [hCdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  -- the mass and the trivial bound for `dtp`
  set S : ℝ := ∑ n ∈ Finset.Icc N (2 * N), ‖b n‖ with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun n hn => norm_nonneg _
  set M : ℝ := Cw * S with hMdef
  have hM0 : 0 ≤ M := mul_nonneg hCw0 hS0
  have hMc0 : 0 ≤ M * Cd := mul_nonneg hM0 hCd0
  have hnorm : ∀ u : ℝ, ‖dtp N b u‖ = ‖Submission.LargeValues.smoothedPoly N b u‖ := by
    intro u
    rw [smoothedPoly_eq_cpow_mul_dtp N hN b u, norm_mul, norm_cpow_I_mul N hN u, one_mul]
  have hdtpb : ∀ u : ℝ, ‖dtp N b u‖ ≤ M := by
    intro u
    rw [hMdef]
    exact norm_dtp_le N b Cw hCw u
  -- continuity and integrability of the integrand of the averaging identity
  have hcont : Continuous (fun ξ : ℝ => dtp N b (t + ξ) * (𝓕 PsiBump) ξ) :=
    ((continuous_dtp N b).comp (by fun_prop)).mul continuous_fourier_PsiBump
  have hint : Integrable (fun ξ : ℝ => dtp N b (t + ξ) * (𝓕 PsiBump) ξ) := by
    refine Integrable.mono' ((PsiBump_fourier_integrable.norm).const_mul M)
      hcont.aestronglyMeasurable ?_
    filter_upwards with ξ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hdtpb (t + ξ)) (norm_nonneg _)
  have hgnorm : Integrable (fun ξ : ℝ => ‖dtp N b (t + ξ) * (𝓕 PsiBump) ξ‖) := hint.norm
  have hid := dtp_eq_integral N hN b t
  -- split the averaging integral at `|ξ| ≤ K`
  have hsplit : ∫ ξ, ‖dtp N b (t + ξ) * (𝓕 PsiBump) ξ‖
      = (∫ ξ in Set.Icc (-K) K, ‖dtp N b (t + ξ) * (𝓕 PsiBump) ξ‖)
        + ∫ ξ in (Set.Icc (-K) K)ᶜ, ‖dtp N b (t + ξ) * (𝓕 PsiBump) ξ‖ :=
    (integral_add_compl (s := Set.Icc (-K) K) measurableSet_Icc hgnorm).symm
  -- the main term is bounded by the window average
  have hmain : ∫ ξ in Set.Icc (-K) K, ‖dtp N b (t + ξ) * (𝓕 PsiBump) ξ‖
      ≤ B * ∫ u in t - K..t + K, ‖Submission.LargeValues.smoothedPoly N b u‖ := by
    have hstep : ∫ ξ in Set.Icc (-K) K, ‖dtp N b (t + ξ) * (𝓕 PsiBump) ξ‖
        ≤ B * ∫ ξ in Set.Icc (-K) K, ‖dtp N b (t + ξ)‖ := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_mono_ae hgnorm.integrableOn ?_ ?_
      · exact ((continuous_const.mul
          ((continuous_dtp N b).comp (by fun_prop)).norm)).integrableOn_Icc
      · filter_upwards with ξ
        calc ‖dtp N b (t + ξ) * (𝓕 PsiBump) ξ‖
            = ‖𝓕 PsiBump ξ‖ * ‖dtp N b (t + ξ)‖ := by rw [norm_mul, mul_comm]
          _ ≤ B * ‖dtp N b (t + ξ)‖ :=
              mul_le_mul_of_nonneg_right (hBbound ξ) (norm_nonneg _)
    have hEq : ∫ ξ in Set.Icc (-K) K, ‖dtp N b (t + ξ)‖
        = ∫ u in t - K..t + K, ‖dtp N b u‖ := by
      have hIcc : ∫ ξ in Set.Icc (-K) K, ‖dtp N b (t + ξ)‖
          = ∫ ξ in Set.Ioc (-K) K, ‖dtp N b (t + ξ)‖ :=
        MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := (-K)) (b := K)).symm
      have hIoc : ∫ ξ in Set.Ioc (-K) K, ‖dtp N b (t + ξ)‖
          = ∫ ξ in (-K)..K, ‖dtp N b (t + ξ)‖ :=
        (intervalIntegral.integral_of_le (show -K ≤ K by linarith)).symm
      have hshift : ∫ ξ in (-K)..K, ‖dtp N b (t + ξ)‖
          = ∫ u in t - K..t + K, ‖dtp N b u‖ := by
        have hcomm : (∫ ξ in (-K)..K, ‖dtp N b (t + ξ)‖)
            = ∫ ξ in (-K)..K, ‖dtp N b (ξ + t)‖ :=
          intervalIntegral.integral_congr fun x hx => by rw [add_comm]
        rw [hcomm, intervalIntegral.integral_comp_add_right (fun u => ‖dtp N b u‖) t,
          show -K + t = t - K by ring, show K + t = t + K by ring]
      rw [hIcc, hIoc, hshift]
    calc ∫ ξ in Set.Icc (-K) K, ‖dtp N b (t + ξ) * (𝓕 PsiBump) ξ‖
        ≤ B * ∫ ξ in Set.Icc (-K) K, ‖dtp N b (t + ξ)‖ := hstep
      _ = B * ∫ u in t - K..t + K, ‖dtp N b u‖ := by rw [hEq]
      _ = B * ∫ u in t - K..t + K, ‖Submission.LargeValues.smoothedPoly N b u‖ := by
          congr 1
          exact intervalIntegral.integral_congr fun u hu => hnorm u
  -- the tail is bounded using the rapid decay of `𝓕ψ`
  have htail : ∫ ξ in (Set.Icc (-K) K)ᶜ, ‖dtp N b (t + ξ) * (𝓕 PsiBump) ξ‖
      ≤ 2 * (M * Cd) * K ^ (-(m : ℝ)) := by
    have hle_abs : ∀ ξ : ℝ, ξ ∉ Set.Icc (-K) K → K < |ξ| := by
      intro ξ hξ
      by_contra h
      rw [not_lt] at h
      exact hξ (Set.mem_Icc.mpr (abs_le.mp h))
    have hne_of : ∀ ξ : ℝ, K < |ξ| → ξ ≠ 0 := by
      intro ξ h h0
      rw [h0, abs_zero] at h
      linarith
    have hmaj : IntegrableOn (fun ξ : ℝ => M * Cd * (|ξ| ^ (m + 1))⁻¹)
        (Set.Icc (-K) K)ᶜ := by
      refine Integrable.mono' (g := fun ξ : ℝ => (2 * (M * Cd)) * (1 + ξ ^ 2)⁻¹) ?_ ?_ ?_
      · exact (integrable_inv_one_add_sq.integrableOn (s := (Set.Icc (-K) K)ᶜ)).const_mul _
      · exact ((continuous_abs.pow (m + 1)).measurable.inv.const_mul (M * Cd)).aestronglyMeasurable
      · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Icc.compl)] with ξ hξ
        rw [Real.norm_of_nonneg (by positivity)]
        have habs : 1 ≤ |ξ| := le_trans hK (le_of_lt (hle_abs ξ hξ))
        have h1 : (|ξ| ^ (m + 1))⁻¹ ≤ (|ξ| ^ 2)⁻¹ := by
          refine inv_anti₀ (by positivity) ?_
          exact pow_le_pow_right₀ habs (by omega)
        have h2 : (|ξ| ^ 2)⁻¹ ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
          have h3 : (1 + ξ ^ 2) / 2 ≤ |ξ| ^ 2 := by
            have h : (1 : ℝ) ≤ |ξ| ^ 2 := by nlinarith [habs, abs_nonneg ξ]
            have h' : (|ξ| : ℝ) ^ 2 = ξ ^ 2 := sq_abs ξ
            nlinarith [h, h']
          have h4 : ((1 + ξ ^ 2) / 2)⁻¹ = 2 * (1 + ξ ^ 2)⁻¹ := by
            rw [div_eq_mul_inv, mul_inv, inv_inv]; ring
          exact (inv_anti₀ (by positivity) h3).trans (le_of_eq h4)
        calc M * Cd * (|ξ| ^ (m + 1))⁻¹ ≤ M * Cd * (|ξ| ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_left h1 hMc0
          _ ≤ M * Cd * (2 * (1 + ξ ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h2 hMc0
          _ = (2 * (M * Cd)) * (1 + ξ ^ 2)⁻¹ := by ring
    refine (MeasureTheory.setIntegral_mono_ae_restrict hgnorm.integrableOn hmaj ?_).trans ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_Icc.compl)] with ξ hξ
      have hξne : ξ ≠ 0 := hne_of ξ (hle_abs ξ hξ)
      calc ‖dtp N b (t + ξ) * (𝓕 PsiBump) ξ‖
          = ‖dtp N b (t + ξ)‖ * ‖𝓕 PsiBump ξ‖ := norm_mul _ _
        _ ≤ M * ‖𝓕 PsiBump ξ‖ :=
            mul_le_mul_of_nonneg_right (hdtpb (t + ξ)) (norm_nonneg _)
        _ ≤ M * (Cd / |ξ| ^ (m + 1)) := mul_le_mul_of_nonneg_left (hCd ξ hξne) hM0
        _ = M * Cd * (|ξ| ^ (m + 1))⁻¹ := by rw [div_eq_mul_inv]; ring
    · have hconst : ∫ ξ in (Set.Icc (-K) K)ᶜ, M * Cd * (|ξ| ^ (m + 1))⁻¹
          = (M * Cd) * ∫ ξ in (Set.Icc (-K) K)ᶜ, (|ξ| ^ (m + 1))⁻¹ := by
        rw [← MeasureTheory.integral_const_mul]
      rw [hconst]
      have heq : ∀ ξ : ℝ, (|ξ| ^ (m + 1))⁻¹ = |ξ| ^ (-(m : ℝ) - 1) := by
        intro ξ
        rw [show -(m : ℝ) - 1 = -((m : ℝ) + 1) by ring, Real.rpow_neg (abs_nonneg ξ),
          ← Real.rpow_natCast (|ξ|) (m + 1)]
        congr 1
        push_cast
        ring
      have hKbound : ∫ ξ in (Set.Icc (-K) K)ᶜ, (|ξ| ^ (m + 1))⁻¹ ≤ 2 * K ^ (-(m : ℝ)) := by
        rw [MeasureTheory.setIntegral_congr_fun (measurableSet_Icc.compl) fun ξ hξ => heq ξ]
        exact tail_integral_rpow m (by omega) hK
      calc (M * Cd) * ∫ ξ in (Set.Icc (-K) K)ᶜ, (|ξ| ^ (m + 1))⁻¹
          ≤ (M * Cd) * (2 * K ^ (-(m : ℝ))) := mul_le_mul_of_nonneg_left hKbound hMc0
        _ = 2 * (M * Cd) * K ^ (-(m : ℝ)) := by ring
  -- put everything together
  calc ‖Submission.LargeValues.smoothedPoly N b t‖
      = ‖∫ ξ, dtp N b (t + ξ) * (𝓕 PsiBump) ξ‖ := by rw [← hnorm t, hid]
    _ ≤ ∫ ξ, ‖dtp N b (t + ξ) * (𝓕 PsiBump) ξ‖ := norm_integral_le_integral_norm _
    _ = (∫ ξ in Set.Icc (-K) K, ‖dtp N b (t + ξ) * (𝓕 PsiBump) ξ‖)
          + ∫ ξ in (Set.Icc (-K) K)ᶜ, ‖dtp N b (t + ξ) * (𝓕 PsiBump) ξ‖ := hsplit
    _ ≤ B * (∫ u in t - K..t + K, ‖Submission.LargeValues.smoothedPoly N b u‖)
          + 2 * (M * Cd) * K ^ (-(m : ℝ)) := add_le_add hmain htail
    _ ≤ C * (∫ u in t - K..t + K, ‖Submission.LargeValues.smoothedPoly N b u‖)
          + C / K ^ (m : ℝ) * S := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_right hBC
            (intervalIntegral.integral_nonneg (by linarith) fun u hu => norm_nonneg _)
        · rw [hMdef, Real.rpow_neg (le_of_lt hKpos), div_eq_mul_inv]
          have hKinv : 0 ≤ (K ^ (m : ℝ))⁻¹ := by positivity
          calc 2 * (Cw * S * Cd) * (K ^ (m : ℝ))⁻¹
              = (2 * Cw * Cd) * S * (K ^ (m : ℝ))⁻¹ := by ring
            _ ≤ C * S * (K ^ (m : ℝ))⁻¹ := by
                refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2C hS0) hKinv
            _ = C * (K ^ (m : ℝ))⁻¹ * S := by ring

end Work.GM.Energy.LocalConstancy
