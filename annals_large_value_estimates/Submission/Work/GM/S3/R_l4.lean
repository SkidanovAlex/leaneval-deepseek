import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Rl4Aux
import Submission.Work.GM.S3.l4_bump
import Submission.Work.GM.S3.l4_expansion
import Submission.Work.GM.S3.l4_scaled_integral
import Submission.Work.GM.S3.l4_scaled_integrable
import Submission.Work.GM.S3.l4_Rfun_exp
import Submission.Work.GM.S3.l4_card_bound
import Submission.Work.GM.S3.l4_rpow_absorb

/-!
# GM Lemma 8.3: the `L⁴` bound for `R`

`Rfun W v = Σ_{t ∈ W} |v|^{it}`; we prove `∫_1^2 ‖Rfun W v‖^4 dv ≤ C N^ε E(W)` for every
`ε > 0`, every `(N^{6/5})^ε`-separated `W ⊆ [0, N^{6/5}]`, where
`E(W) = #{(t₁,t₂,t₃,t₄) ∈ W⁴ : |t₁+t₂-t₃-t₄| ≤ 1}` is the additive energy.

The proof follows GM §8: change variables `v = e^τ`, majorise by a bump `ψ(τ/T^η)` with
rapidly decaying Fourier transform, expand `‖Σ_t e^{iτt}‖^4` as the quadruple sum
`Σ_{t₁,t₂,t₃,t₄} e^{iτ(t₁+t₂-t₃-t₄)}`, and evaluate `∫ ψ(τ/T^η)e^{isτ}dτ = T^η 𝓕ψ(-T^η s/2π)`:
the terms with `|t₁+t₂-t₃-t₄| ≤ 1` make up exactly `energy W`, the others are
`O(T^{η(1-j)}|W|^4) = O(1)` for `η(j-1) ≥ 7`.

The ingredients `l4_bump`, `l4_expansion`, `l4_scaled_integral`, `l4_scaled_integrable`,
`l4_card_bound` and `l4_rpow_absorb` are proved in their own modules; `R_l4_core` is the
assembly, and `R_l4` is the statement of GM Lemma 8.3.
-/

namespace Work.GM.S3
open MeasureTheory Finset Complex
open scoped BigOperators
open Submission.GM (Rfun energy Separated)

open MeasureTheory Finset Complex
open scoped BigOperators
open Submission.GM (Rfun energy Separated)

private lemma far_arith {T η : ℝ} (hT : 1 ≤ T) {j : ℕ} {Cj s : ℝ}
    (hCj : 0 ≤ Cj) (hs : 1 < |s|) :
    T ^ η * (Cj / |-(T ^ η * s) / (2 * Real.pi)| ^ j) ≤
      (2 * Real.pi) ^ j * Cj * T ^ (η * (1 - (j : ℝ))) := by
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT
  have hTnn : 0 ≤ T := hTpos.le
  have hpi : 0 < 2 * Real.pi := by positivity
  have hApos : 0 < T ^ η := Real.rpow_pos_of_pos hTpos η
  have hAnn : 0 ≤ T ^ η := hApos.le
  have hsj : 1 ≤ |s| ^ j := one_le_pow₀ hs.le
  have hX : |-(T ^ η * s) / (2 * Real.pi)| = T ^ η * |s| / (2 * Real.pi) := by
    rw [abs_div, abs_neg, abs_mul, abs_of_nonneg hAnn, abs_of_pos hpi]
  have hkey : T ^ (η * (1 - (j : ℝ))) = T ^ η / (T ^ η) ^ j := by
    rw [Real.rpow_mul hTnn η (1 - (j:ℝ)), Real.rpow_sub hApos 1 (j:ℝ), Real.rpow_one,
      Real.rpow_natCast]
  rw [hX, div_pow, mul_pow, div_div_eq_mul_div]
  have hstep : Cj * (2 * Real.pi) ^ j / ((T^η)^j * |s|^j) ≤ Cj * (2*Real.pi)^j / (T^η)^j :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos hApos j)
      (le_mul_of_one_le_right (pow_nonneg hAnn j) hsj)
  calc T ^ η * (Cj * (2 * Real.pi) ^ j / ((T^η)^j * |s|^j))
      ≤ T ^ η * (Cj * (2 * Real.pi)^j / (T^η)^j) :=
        mul_le_mul_of_nonneg_left hstep hAnn
    _ = (2 * Real.pi)^j * Cj * T ^ (η * (1 - (j:ℝ))) := by
        rw [hkey]
        field_simp

private lemma term_bound
    (hscale : ∀ {ψ : ℝ → ℝ}, Continuous ψ → HasCompactSupport ψ → ∀ {T η : ℝ}, 0 < T → 0 < η →
      ∀ s : ℝ, (∫ τ : ℝ, ((ψ (τ / T ^ η) : ℝ) : ℂ) * cexp (I * ((s * τ : ℝ) : ℂ)))
        = ((T ^ η : ℝ) : ℂ) * FourierTransform.fourier (fun x : ℝ => (ψ x : ℂ))
            (-(T ^ η * s) / (2 * Real.pi)))
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hcs : HasCompactSupport ψ)
    {A : ℝ} (hA : ∀ ξ : ℝ, ‖FourierTransform.fourier (fun x : ℝ => (ψ x : ℂ)) ξ‖ ≤ A)
    {j : ℕ} {Cj : ℝ}
    (hCj : ∀ ξ : ℝ, ξ ≠ 0 → ‖FourierTransform.fourier (fun x : ℝ => (ψ x : ℂ)) ξ‖ ≤ Cj / |ξ| ^ j)
    {T η : ℝ} (hT : 1 ≤ T) (hη : 0 < η) (s : ℝ) :
    ‖∫ τ : ℝ, ((ψ (τ / T ^ η) : ℝ) : ℂ) * cexp (I * ((s * τ : ℝ) : ℂ))‖
      ≤ if |s| ≤ 1 then T ^ η * A else (2 * Real.pi) ^ j * Cj * T ^ (η * (1 - (j : ℝ))) := by
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT
  have hTnn : 0 ≤ T := hTpos.le
  have hAnn : 0 ≤ T ^ η := Real.rpow_nonneg hTnn η
  have hCjnn : 0 ≤ Cj := by
    have h1 := hCj 1 one_ne_zero
    simpa using le_trans (norm_nonneg _) h1
  rw [hscale hψ hcs hTpos hη s, norm_mul,
    show ‖((T ^ η : ℝ) : ℂ)‖ = |T ^ η| from by simp, abs_of_nonneg hAnn]
  by_cases hs : |s| ≤ 1
  · rw [if_pos hs]
    exact mul_le_mul_of_nonneg_left (hA _) hAnn
  · rw [if_neg hs]
    have hs1 : 1 < |s| := lt_of_not_ge hs
    have hs0 : s ≠ 0 := by intro h; rw [h, abs_zero] at hs1; norm_num at hs1
    have hne : -(T ^ η * s) / (2 * Real.pi) ≠ 0 := by
      simp [hs0, (Real.rpow_pos_of_pos hTpos η).ne']
    refine (mul_le_mul_of_nonneg_left (hCj _ hne) hAnn).trans ?_
    exact far_arith hT hCjnn hs1

private lemma quad_sum_bound {A Kfar : ℝ} (hK : 0 ≤ Kfar)
    {W : Finset ℝ} {c : ℝ × ℝ × ℝ × ℝ → ℝ}
    (hterm : ∀ q, c q ≤ if |qs q| ≤ 1 then A else Kfar) :
    ∑ q ∈ Quad W, c q ≤ (energy W : ℝ) * A + ((Quad W).card : ℝ) * Kfar := by
  classical
  calc ∑ q ∈ Quad W, c q
      ≤ ∑ q ∈ Quad W, (if |qs q| ≤ 1 then A else Kfar) := Finset.sum_le_sum fun q hq => hterm q
    _ = ∑ q ∈ (Quad W).filter (fun q => |qs q| ≤ 1), A
        + ∑ q ∈ (Quad W).filter (fun q => ¬ (|qs q| ≤ 1)), Kfar := Finset.sum_ite _ _
    _ = ((Quad W).filter (fun q => |qs q| ≤ 1)).card * A
        + ((Quad W).filter (fun q => ¬ (|qs q| ≤ 1))).card * Kfar := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    _ ≤ (energy W : ℝ) * A + ((Quad W).card : ℝ) * Kfar := by
        have h1 : ((Quad W).filter (fun q => |qs q| ≤ 1)).card = energy W := energy_eq_filter W
        rw [h1]
        refine add_le_add le_rfl ?_
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le _ _) hK

private lemma final_arith {Tη A Kf E Qf Ne K : ℝ} (hTηA : Tη * A ≤ Ne * A) (hKf : Qf * Kf ≤ 16 * K)
    (hE : 1 ≤ E) (hNe : 1 ≤ Ne) (hK : 0 ≤ K) :
    2 * (E * (Tη * A) + Qf * Kf) ≤ (2 * (A + 16 * K) + 1) * Ne * E := by
  nlinarith [hTηA, hKf, hE, hNe, hK, mul_nonneg (sub_nonneg.mpr hE) (sub_nonneg.mpr hNe),
    mul_nonneg hK (mul_nonneg (sub_nonneg.mpr hE) (sub_nonneg.mpr hNe))]

theorem R_l4_core
    (hbump : ∃ ψ : ℝ → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧
      (∀ x : ℝ, 0 ≤ ψ x) ∧ (∀ x ∈ Set.Icc (0 : ℝ) (Real.log 2), 1 ≤ ψ x) ∧
      (∃ A : ℝ, 0 ≤ A ∧ ∀ ξ : ℝ,
        ‖FourierTransform.fourier (fun x : ℝ => (ψ x : ℂ)) ξ‖ ≤ A) ∧
      (∀ j : ℕ, ∃ Cj : ℝ, 0 < Cj ∧ ∀ ξ : ℝ, ξ ≠ 0 →
        ‖FourierTransform.fourier (fun x : ℝ => (ψ x : ℂ)) ξ‖ ≤ Cj / |ξ| ^ j))
    (hexp : ∀ (W : Finset ℝ) (τ : ℝ),
      ((‖Gfun W τ‖ ^ 4 : ℝ) : ℂ) = ∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ)))
    (hscale : ∀ {ψ : ℝ → ℝ}, Continuous ψ → HasCompactSupport ψ → ∀ {T η : ℝ}, 0 < T → 0 < η →
      ∀ s : ℝ, (∫ τ : ℝ, ((ψ (τ / T ^ η) : ℝ) : ℂ) * cexp (I * ((s * τ : ℝ) : ℂ)))
        = ((T ^ η : ℝ) : ℂ) * FourierTransform.fourier (fun x : ℝ => (ψ x : ℂ))
            (-(T ^ η * s) / (2 * Real.pi)))
    (hscaleint : ∀ {ψ : ℝ → ℝ}, Continuous ψ → HasCompactSupport ψ → ∀ {T η : ℝ}, 0 < T → 0 < η →
      ∀ s : ℝ, Integrable (fun τ : ℝ => ((ψ (τ / T ^ η) : ℝ) : ℂ) * cexp (I * ((s * τ : ℝ) : ℂ))))
    (hcard : ∀ {W : Finset ℝ} {δ T : ℝ}, 1 ≤ T → 1 ≤ δ →
      (∀ t ∈ W, t ∈ Set.Icc 0 T) → (∀ t ∈ W, ∀ s ∈ W, t ≠ s → δ ≤ |t - s|) →
      (W.card : ℝ) ≤ T + 1) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Separated W ((Submission.LargeValues.M N) ^ ε) →
      ∫ v in (1 : ℝ)..2, ‖Rfun W v‖ ^ 4 ≤
        C * (N : ℝ) ^ ε * (energy W : ℝ) := by
  intro ε hε
  obtain ⟨ψ, hψc, hψcs, hψnn, hψge1, ⟨A, hAnn, hAbound⟩, hdecay⟩ := hbump
  have hlog2nn : (0 : ℝ) ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  set η : ℝ := ε / 2 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  set j : ℕ := Nat.ceil (7 / η) + 1 with hjdef
  have hj7 : 7 ≤ η * ((j : ℝ) - 1) := by
    have hc : 7 / η ≤ (Nat.ceil (7 / η) : ℝ) := Nat.le_ceil _
    have hjcast : ((j : ℝ) - 1) = (Nat.ceil (7 / η) : ℝ) := by
      rw [hjdef]; push_cast; ring
    rw [hjcast]
    calc (7 : ℝ) = η * (7 / η) := by field_simp
      _ ≤ η * (Nat.ceil (7 / η) : ℝ) := mul_le_mul_of_nonneg_left hc hη.le
  obtain ⟨Cj, hCjpos, hCjbound⟩ := hdecay j
  refine ⟨2 * (A + 16 * (2 * Real.pi) ^ j * Cj) + 1, ?_, 1, ?_⟩
  · have h1 : 0 < (2 * Real.pi) ^ j := pow_pos (by positivity) j
    have h2 : 0 < 16 * (2 * Real.pi) ^ j * Cj := mul_pos (mul_pos (by norm_num) h1) hCjpos
    linarith
  · intro N hN W hWsub hWsep
    have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    set T : ℝ := Submission.LargeValues.M N with hTdef
    have hT1 : 1 ≤ T := by rw [hTdef]; exact Submission.LargeValues.M_ge_one hN
    have hTnn : 0 ≤ T := le_trans zero_le_one hT1
    have hTpos : 0 < T := lt_of_lt_of_le one_pos hT1
    have hTetanonneg : 0 ≤ T ^ η := Real.rpow_nonneg hTnn η
    have hδ1 : 1 ≤ T ^ ε := by
      rw [hTdef]; exact Real.one_le_rpow (Submission.LargeValues.M_ge_one hN) hε.le
    have hWsub' : ∀ t ∈ W, t ∈ Set.Icc 0 T := by
      intro t ht; rw [hTdef]; exact hWsub t ht
    have hWsep' : ∀ t ∈ W, ∀ s ∈ W, t ≠ s → T ^ ε ≤ |t - s| := by
      intro t ht s hs hts; rw [hTdef]; exact hWsep t ht s hs hts
    have hcardW : (W.card : ℝ) ≤ T + 1 := hcard hT1 hδ1 hWsub' hWsep'
    by_cases hWne : W.Nonempty
    · have henergy1 : (1 : ℝ) ≤ (energy W : ℝ) := by exact_mod_cast one_le_energy hWne
      set K : ℝ := (2 * Real.pi) ^ j * Cj with hKdef
      have hKnn : 0 ≤ K := by
        rw [hKdef]; exact mul_nonneg (pow_nonneg (by positivity) j) hCjpos.le
      have hNeps : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow hNr hε.le
      have hTeta_absorb : T ^ η ≤ (N : ℝ) ^ ε := by
        rw [hTdef, hηdef]; exact l4_rpow_absorb hε hN
      have hTA : T ^ η * A ≤ (N : ℝ) ^ ε * A := mul_le_mul_of_nonneg_right hTeta_absorb hAnn
      have hQcard : ((Quad W).card : ℝ) ≤ 16 * T ^ 4 := by
        rw [Quad_card]
        push_cast
        calc (W.card : ℝ) ^ 4 ≤ (T + 1) ^ 4 := pow_le_pow_left₀ (by positivity) hcardW 4
          _ ≤ (2 * T) ^ 4 := by
              apply pow_le_pow_left₀ (by positivity)
              linarith
          _ = 16 * T ^ 4 := by ring
      have hKfar_bound : ((Quad W).card : ℝ) * (K * T ^ (η * (1 - (j : ℝ)))) ≤ 16 * K := by
        have h4T : T ^ 4 * T ^ (η * (1 - (j:ℝ))) ≤ 1 := by
          have h4e : (4:ℝ) + η * (1 - (j:ℝ)) ≤ 0 := by linarith [hj7]
          have hT4 : T ^ 4 * T ^ (η * (1 - (j:ℝ))) = T ^ ((4:ℝ) + η * (1 - (j:ℝ))) := by
            rw [← Real.rpow_natCast T 4, ← Real.rpow_add hTpos]
            norm_num
          rw [hT4]
          calc T ^ ((4:ℝ) + η * (1 - (j:ℝ))) ≤ T ^ 0 := Real.rpow_le_rpow_of_exponent_le hT1 h4e
            _ = 1 := by simp
        calc ((Quad W).card : ℝ) * (K * T ^ (η * (1 - (j : ℝ))))
            ≤ (16 * T ^ 4) * (K * T ^ (η * (1 - (j : ℝ)))) := by
              apply mul_le_mul_of_nonneg_right hQcard
              exact mul_nonneg hKnn (Real.rpow_nonneg hTnn _)
          _ = 16 * K * (T ^ 4 * T ^ (η * (1 - (j : ℝ)))) := by ring
          _ ≤ 16 * K * 1 := mul_le_mul_of_nonneg_left h4T (by positivity)
          _ = 16 * K := by ring
      have hscaleint' : ∀ s : ℝ, Integrable (fun τ : ℝ =>
          ((ψ (τ / T ^ η) : ℝ) : ℂ) * cexp (I * ((s * τ : ℝ) : ℂ))) :=
        fun s => hscaleint hψc hψcs hTpos hη s
      have hψint0 : Integrable (fun τ : ℝ => ((ψ (τ / T ^ η) : ℝ) : ℂ)) := by
        simpa using hscaleint' 0
      have hcontG : Continuous (fun τ : ℝ => ψ (τ / T ^ η) * ‖Gfun W τ‖ ^ 4) :=
        (hψc.comp (continuous_id.div_const _)).mul ((Gfun_continuous W).norm.pow 4)
      have hGint : Integrable (fun τ : ℝ => ψ (τ / T ^ η) * ‖Gfun W τ‖ ^ 4) := by
        refine Integrable.mono' (hψint0.norm.const_mul ((W.card : ℝ) ^ 4))
          hcontG.aestronglyMeasurable ?_
        filter_upwards with τ
        have hcard4 : ‖Gfun W τ‖ ^ 4 ≤ (W.card : ℝ) ^ 4 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_Gfun_le_card W τ) 4
        rw [Real.norm_eq_abs, abs_mul,
          show ‖((ψ (τ / T ^ η) : ℝ) : ℂ)‖ = |ψ (τ / T ^ η)| from by simp,
          abs_of_nonneg (pow_nonneg (norm_nonneg _) 4), abs_of_nonneg (hψnn _)]
        calc ψ (τ / T ^ η) * ‖Gfun W τ‖ ^ 4
            ≤ ψ (τ / T ^ η) * (W.card : ℝ) ^ 4 := mul_le_mul_of_nonneg_left hcard4 (hψnn _)
          _ = (W.card : ℝ) ^ 4 * ψ (τ / T ^ η) := by ring
      have stepA : ∫ v in (1:ℝ)..2, ‖Rfun W v‖^4
          = ∫ τ in (0:ℝ)..(Real.log 2), Real.exp τ * ‖Gfun W τ‖^4 := by
        rw [integral_exp_subst (fun v => ‖Rfun W v‖ ^ 4)]
        simp_rw [Rfun_eq_Gfun_exp]
      have stepB : ∫ τ in (0:ℝ)..(Real.log 2), Real.exp τ * ‖Gfun W τ‖^4
          ≤ ∫ τ in (0:ℝ)..(Real.log 2), 2 * ‖Gfun W τ‖^4 := by
        refine intervalIntegral.integral_mono_on hlog2nn ?_ ?_ ?_
        · exact (Real.continuous_exp.mul ((Gfun_continuous W).norm.pow 4)).intervalIntegrable _ _
        · exact (continuous_const.mul ((Gfun_continuous W).norm.pow 4)).intervalIntegrable _ _
        · intro τ hτ
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg _) 4)
          calc Real.exp τ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hτ.2
            _ = 2 := Real.exp_log (by norm_num)
      have stepC : ∫ τ in (0:ℝ)..(Real.log 2), 2 * ‖Gfun W τ‖^4
          ≤ 2 * ∫ τ : ℝ, ψ (τ / T ^ η) * ‖Gfun W τ‖^4 := by
        rw [intervalIntegral.integral_const_mul]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [intervalIntegral.integral_of_le hlog2nn]
        have h1 : IntegrableOn (fun τ : ℝ => ‖Gfun W τ‖^4) (Set.Icc 0 (Real.log 2)) :=
          (((Gfun_continuous W).norm.pow 4).continuousOn).integrableOn_Icc
        have h2 : IntegrableOn (fun τ : ℝ => ψ (τ / T ^ η) * ‖Gfun W τ‖^4)
            (Set.Icc 0 (Real.log 2)) := hGint.integrableOn
        have h3 : ∫ τ in Set.Ioc 0 (Real.log 2), ‖Gfun W τ‖^4
            ≤ ∫ τ in Set.Icc 0 (Real.log 2), ‖Gfun W τ‖^4 :=
          setIntegral_mono_set h1 (Filter.Eventually.of_forall fun τ => pow_nonneg (norm_nonneg _) 4)
            (Filter.Eventually.of_forall fun τ hτ => ⟨le_of_lt hτ.1, hτ.2⟩)
        have h4 : ∫ τ in Set.Icc 0 (Real.log 2), ‖Gfun W τ‖^4
            ≤ ∫ τ in Set.Icc 0 (Real.log 2), ψ (τ / T ^ η) * ‖Gfun W τ‖^4 := by
          refine setIntegral_mono_on h1 h2 measurableSet_Icc fun τ hτ => ?_
          have hψge : 1 ≤ ψ (τ / T ^ η) := by
            apply hψge1
            refine ⟨div_nonneg hτ.1 hTetanonneg, ?_⟩
            calc τ / T ^ η ≤ τ := div_le_self hτ.1 (Real.one_le_rpow hT1 hη.le)
              _ ≤ Real.log 2 := hτ.2
          exact le_mul_of_one_le_left (pow_nonneg (norm_nonneg (Gfun W τ)) 4) hψge
        have h5 : ∫ τ in Set.Icc 0 (Real.log 2), ψ (τ / T ^ η) * ‖Gfun W τ‖^4
            ≤ ∫ τ in Set.univ, ψ (τ / T ^ η) * ‖Gfun W τ‖^4 :=
          setIntegral_mono_set hGint.integrableOn
            (Filter.Eventually.of_forall fun τ => mul_nonneg (hψnn _) (pow_nonneg (norm_nonneg _) 4))
            (Filter.Eventually.of_forall fun τ _ => trivial)
        have h5' : ∫ τ in Set.Icc 0 (Real.log 2), ψ (τ / T ^ η) * ‖Gfun W τ‖^4
            ≤ ∫ τ : ℝ, ψ (τ / T ^ η) * ‖Gfun W τ‖^4 := by
          simpa [setIntegral_univ] using h5
        linarith [h3, h4, h5']
      have stepD : ∫ τ : ℝ, ψ (τ / T ^ η) * ‖Gfun W τ‖^4
          ≤ ‖∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) *
              (∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ)))‖ := by
        have hcont_c : Continuous (fun τ : ℝ => (ψ (τ / T ^ η) : ℂ) *
            (∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ)))) := by
          refine (Complex.continuous_ofReal.comp (hψc.comp (continuous_id.div_const _))).mul ?_
          refine continuous_finsetSum _ (fun q hq => ?_)
          have h1 : Continuous (fun τ : ℝ => qs q * τ) := continuous_const.mul continuous_id
          have h2 : Continuous (fun τ : ℝ => ((qs q * τ : ℝ) : ℂ)) :=
            Complex.continuous_ofReal.comp h1
          exact Complex.continuous_exp.comp (continuous_const.mul h2)
        have hIntc : Integrable (fun τ : ℝ => (ψ (τ / T ^ η) : ℂ) *
            (∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ)))) := by
          refine Integrable.mono' (hψint0.norm.const_mul ((Quad W).card : ℝ))
            hcont_c.aestronglyMeasurable ?_
          filter_upwards with τ
          have hsum : ‖∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ))‖ ≤ ((Quad W).card : ℝ) := by
            calc ‖∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ))‖
                ≤ ∑ q ∈ Quad W, ‖cexp (I * ((qs q * τ : ℝ) : ℂ))‖ := norm_sum_le _ _
              _ = ∑ _q ∈ Quad W, (1 : ℝ) := by
                  refine Finset.sum_congr rfl fun q hq => ?_
                  rw [Complex.norm_exp]; simp
              _ = ((Quad W).card : ℝ) := by simp
          rw [norm_mul, show ‖((ψ (τ / T ^ η) : ℝ) : ℂ)‖ = |ψ (τ / T ^ η)| from by simp]
          calc |ψ (τ / T ^ η)| * ‖∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ))‖
              ≤ |ψ (τ / T ^ η)| * ((Quad W).card : ℝ) :=
                mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
            _ = ((Quad W).card : ℝ) * |ψ (τ / T ^ η)| := by ring
        have hre : RCLike.re (∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) *
            (∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ))))
            = ∫ τ : ℝ, ψ (τ / T ^ η) * ‖Gfun W τ‖^4 := by
          rw [← integral_re hIntc]
          refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
          simp only
          rw [← hexp W τ, ← Complex.ofReal_mul, RCLike.re_to_complex, Complex.ofReal_re]
        calc ∫ τ : ℝ, ψ (τ / T ^ η) * ‖Gfun W τ‖^4
            = RCLike.re (∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) *
                (∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ)))) := hre.symm
          _ ≤ ‖∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) *
                (∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ)))‖ := by
              rw [RCLike.re_to_complex]
              exact Complex.re_le_norm _
      have stepE : (∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) *
            (∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ))))
          = ∑ q ∈ Quad W, ∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) * cexp (I * ((qs q * τ : ℝ) : ℂ)) := by
        have h1 : (∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) *
              (∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ))))
            = ∫ τ : ℝ, ∑ q ∈ Quad W, (ψ (τ / T ^ η) : ℂ) * cexp (I * ((qs q * τ : ℝ) : ℂ)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
          simp only
          rw [Finset.mul_sum]
        rw [h1, integral_finsetSum (Quad W) (fun q hq => hscaleint' (qs q))]
      have stepF : ‖∑ q ∈ Quad W, ∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) * cexp (I * ((qs q * τ : ℝ) : ℂ))‖
          ≤ ∑ q ∈ Quad W, ‖∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) * cexp (I * ((qs q * τ : ℝ) : ℂ))‖ :=
        norm_sum_le _ _
      have stepG : ∑ q ∈ Quad W, ‖∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) * cexp (I * ((qs q * τ : ℝ) : ℂ))‖
          ≤ (energy W : ℝ) * (T ^ η * A) + ((Quad W).card : ℝ) * (K * T ^ (η * (1 - (j : ℝ)))) := by
        refine quad_sum_bound (A := T ^ η * A) (Kfar := K * T ^ (η * (1 - (j : ℝ))))
          (mul_nonneg hKnn (Real.rpow_nonneg hTnn _)) (fun q => ?_)
        rw [hKdef]
        exact term_bound hscale hψc hψcs hAbound hCjbound hT1 hη (qs q)
      calc ∫ v in (1:ℝ)..2, ‖Rfun W v‖^4
          = ∫ τ in (0:ℝ)..(Real.log 2), Real.exp τ * ‖Gfun W τ‖^4 := stepA
        _ ≤ ∫ τ in (0:ℝ)..(Real.log 2), 2 * ‖Gfun W τ‖^4 := stepB
        _ ≤ 2 * ∫ τ : ℝ, ψ (τ / T ^ η) * ‖Gfun W τ‖^4 := stepC
        _ ≤ 2 * ‖∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) *
              (∑ q ∈ Quad W, cexp (I * ((qs q * τ : ℝ) : ℂ)))‖ :=
            mul_le_mul_of_nonneg_left stepD (by norm_num)
        _ = 2 * ‖∑ q ∈ Quad W, ∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) * cexp (I * ((qs q * τ : ℝ) : ℂ))‖ := by
            rw [stepE]
        _ ≤ 2 * ∑ q ∈ Quad W, ‖∫ τ : ℝ, (ψ (τ / T ^ η) : ℂ) * cexp (I * ((qs q * τ : ℝ) : ℂ))‖ :=
            mul_le_mul_of_nonneg_left stepF (by norm_num)
        _ ≤ 2 * ((energy W : ℝ) * (T ^ η * A) +
              ((Quad W).card : ℝ) * (K * T ^ (η * (1 - (j : ℝ))))) :=
            mul_le_mul_of_nonneg_left stepG (by norm_num)
        _ ≤ (2 * (A + 16 * K) + 1) * (N : ℝ) ^ ε * (energy W : ℝ) :=
            final_arith hTA hKfar_bound henergy1 hNeps hKnn
        _ = (2 * (A + 16 * (2 * Real.pi) ^ j * Cj) + 1) * (N : ℝ) ^ ε * (energy W : ℝ) := by
            rw [hKdef]
            ring
    · have hempty : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hWne
      subst hempty
      simp [Submission.GM.Rfun, Submission.GM.energy]


/-- **GM Lemma 8.3** (L⁴ bound for `R`), with `Rfun W v = Σ_{t ∈ W} |v|^{i t}`, `T = M N = N^{6/5}` and
`energy W = #{(t₁,t₂,t₃,t₄) ∈ W⁴ : |t₁+t₂-t₃-t₄| ≤ 1}`. For every `ε > 0` there is `C > 0` and `N₀`
such that for `N ≥ N₀`, for every `W ⊆ [0, M N]` that is `(M N)^ε`-separated,
`∫_1^2 ‖Rfun W v‖^4 dv ≤ C * N^ε * energy W`.

Proof sketch (GM Lemma 8.3): change variables `v = exp(-2πτ)`; a smooth bump `ψ` with
`ψ(τ/T^η)` majorizing the range together with Poisson summation gives
`∫ ψ(τ/T^η) ‖R(exp(-2πτ))‖^4 dτ = T^η Σ_{t_i ∈ W} ψ̂(T^η(t₃+t₄-t₁-t₂))`, whose terms are rapidly
decaying unless `|t₁+t₂-t₃-t₄| ≤ T^{-η} ≤ 1`; hence `⪅ energy W` (the `T^η` is absorbed into `N^ε`).
`Commons.Analysis.Fourier.poisson_summation_scaled` is available. -/
theorem R_l4 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
      ∫ v in (1 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 4 ≤
        C * (N : ℝ) ^ ε * (Submission.GM.energy W : ℝ) := by
  intro ε hε
  refine R_l4_core l4_bump ?_
    (fun {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hcs : HasCompactSupport ψ)
      {T η : ℝ} (hT : 0 < T) (hη : 0 < η) (s : ℝ) =>
        l4_scaled_integral hψ hcs hT hη s)
    (fun {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hcs : HasCompactSupport ψ)
      {T η : ℝ} (hT : 0 < T) (hη : 0 < η) (s : ℝ) =>
        l4_scaled_integrable hψ hcs hT hη s)
    (fun {W : Finset ℝ} {δ T : ℝ} (hT : 1 ≤ T) (hδ : 1 ≤ δ)
      (hW : ∀ t ∈ W, t ∈ Set.Icc 0 T) (hsep : ∀ t ∈ W, ∀ s ∈ W, t ≠ s → δ ≤ |t - s|) =>
        l4_card_bound hT hδ hW hsep) ε hε
  intro W τ
  simpa [Gfun, Quad, qs] using l4_expansion W τ

end Work.GM.S3
