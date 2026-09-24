import Mathlib
import Submission.Work.GM.Affine.far_part_defs
import Submission.Work.GM.Affine.window_part_defs
import Submission.Work.GM.Affine.card_mul_pairs_le
import Submission.Work.GM.Affine.bsum_far_le_winmass
import Submission.Work.GM.Affine.FarMass_defs
import Submission.Work.GM.Affine.far_mass_le_integral_Bsum
import Submission.Work.GM.Affine.Hfun_sq_integral_le
import Submission.Work.GM.Affine.psi1hat_decay
import Submission.Work.GM.Affine.windowTrunc_L2_bound
import Submission.Work.GM.Affine.WindowFarPairCount
import Submission.Work.GM.Affine.WindowFarCountArith
import Submission.Work.GM.Affine.WindowPairMass_le_FarMass

/-!
# GM §9: the sharp window-part `L²` bound over the far region

This file proves `Work.GM.Affine.WindowFar_sharp_v2`: for `C₀ ≥ 1`, `K > 0` and every `ε > 0`
there is `C > 0` such that for `T ≥ 1`, `η > 0`, `2 ≤ B`, `2B ≤ T^η`, `M₁ > 0`, `M₂ > 0`,
`M₃ ≥ 1` and `f` continuous, non-negative with `SuppHyp C₀ f`,

`∫_{T^η M₁/M₃ < |ξ| ≤ T⁶} ‖Σ_{m₁∈R1 M₁} |m₁|⁻¹ Bsum f M₂ (ξ/m₁) Wwin K M₃ B (ξ/m₁)‖²
    ≤ C · B^{1+ε} · T^{6ε} · (M₁ + M₃) · WinMass f M₂ M₃.`

Here `Wwin K M₃ B y = M₃ Σ'_ℓ 1_{2/M₃ < |ℓ-y| ≤ B/M₃} ψ̂₁(M₃(ℓ-y))` is the *window* part of
the far weight, `R1 M₁ = {m : M₁ < |m| ≤ 2M₁}`, `Bsum f M₂ u = Σ_{m₂ ∈ R2 M₂} m₂ f̂(m₂u)`,
`WinMass f M₂ M₃ = Σ'_ℓ ∫_{|τ|≤2} ‖Bsum f M₂ (ℓ+τ/M₃)‖²dτ`, and
`FarMass K f M₂ M₃ = Σ'_ℓ ∫_{|τ|>2} ‖Bsum f M₂ (ℓ+τ/M₃)‖²‖ψ̂₁(τ)‖²dτ`.

## Route

Write `S(ξ)` for the sum inside the norm and `r := 2 B M₁/M₃`.

1. `Wwin_sum_eq_pairs` rewrites `S(ξ) = Σ_{p ∈ Pwin T M₁ M₃ B ξ} aTerm K M₂ M₃ f ξ p` for
   `|ξ| ≤ T⁶`; Cauchy–Schwarz gives `‖S(ξ)‖² ≤ #Pwin(ξ) · Σ_p ‖aTerm_p(ξ)‖²`.
2. The far region forces `|m₁ℓ - ξ| ≤ 2BM₁/M₃ ≤ T^η M₁/M₃ < |ξ|` for every pair, so the
   resonance count applies to `Pwin` (module `WindowFarPairCount`):
   `#Pwin(ξ) ≤ Cc (T⁶ + r + 2)^{ε/2} (2r+1)`.
3. The pair-mass bound (module `WindowPairMass_le_FarMass`, an `ℝ≥0∞` statement, so that no
   integrability of the pointwise majorant is needed) gives
   `∫_A Σ_p ‖aTerm_p‖² ≤ 16 M₃ FarMass K f M₂ M₃` for every `A`.
4. `bsum_far_le_winmass` gives `FarMass K f M₂ M₃ ≤ CW WinMass f M₂ M₃`.
5. The arithmetic of steps 2–4 (module `WindowFarCountArith`): if the region is non-empty then
   `M₁/M₃ ≤ T⁶`, and the three cases `4BM₁ ≤ M₃`, `4BM₁ > M₃ ≥ M₁`, `4BM₁ > M₃` with `M₁ > M₃`
   give the displayed constant `20·9^{ε/2} Cc Cmid CW + 1`; if the region is empty the integral
   vanishes.

The `L²`-integral is handled through `lintegral` (`integral_eq_lintegral_of_nonneg_ae`) so that
`Kc = Cc (T⁶+r+2)^{ε/2}(2r+1)` can be pulled out with `lintegral_const_mul'` without any
integrability hypothesis on the pair majorant.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.GM.Affine

noncomputable section


theorem WindowFar_sharp_v2 {C₀ K : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (T η B M₁ M₂ M₃ : ℝ), 1 ≤ T → 0 < η → 2 ≤ B → 2 * B ≤ T ^ η →
        0 < M₁ → 0 < M₂ → 1 ≤ M₃ →
      ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
      (∫ ξ in (Set.Icc (-(T ^ 6)) (T ^ 6))
          \ (Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃)),
        ‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
            Wwin K M₃ B (ξ / (m₁ : ℝ))‖ ^ 2)
      ≤ C * B ^ (1 + ε) * T ^ (6 * ε) * (M₁ + M₃) * WinMass f M₂ M₃ := by
  intro ε hε
  obtain ⟨Cmid, hCmidpos, hmid⟩ := WindowPairMass_le_FarMass (C₀ := C₀) (K := K) hC₀ hK
  obtain ⟨CW, hCWpos, hCW⟩ := bsum_far_le_winmass (C₀ := C₀) (K := K) hC₀ hK
  obtain ⟨Cc, hCcpos, hcc⟩ := WindowFarPairCount (ε := ε / 2) (by linarith)
  refine ⟨20 * 9 ^ (ε / 2) * Cc * Cmid * CW + 1, by positivity, ?_⟩
  intro T η B M₁ M₂ M₃ hT hη hB h2B hM₁ hM₂ hM₃ f hf hfnn hsup
  have hM₃pos : (0 : ℝ) < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  have hWnn : (0 : ℝ) ≤ WinMass f M₂ M₃ :=
    tsum_nonneg (fun ℓ => integral_nonneg (fun τ => by positivity))
  by_cases hA : (Set.Icc (-(T ^ 6)) (T ^ 6)
      \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃)) = ∅
  · rw [hA, MeasureTheory.setIntegral_empty]
    exact mul_nonneg (by positivity) hWnn
  · obtain ⟨ξ₀, hξ₀⟩ := Set.nonempty_iff_ne_empty.mpr hA
    have hratio : M₁ / M₃ ≤ T ^ 6 := by
      obtain ⟨h1, h2⟩ := mem_wtrRegion (T := T) (η := η) (M₁ := M₁) (M₃ := M₃) hξ₀
      have hTη : (1 : ℝ) ≤ T ^ η := Real.one_le_rpow hT hη.le
      have hpos : (0 : ℝ) ≤ M₁ / M₃ := le_of_lt (div_pos hM₁ hM₃pos)
      have h3 : M₁ / M₃ ≤ T ^ η * M₁ / M₃ := by
        have h := mul_le_mul_of_nonneg_right hTη hpos
        rw [one_mul] at h
        rwa [show T ^ η * M₁ / M₃ = T ^ η * (M₁ / M₃) from by ring]
      linarith
    set r : ℝ := 2 * B * M₁ / M₃ with hrdef
    have hrnn : 0 ≤ r := by rw [hrdef]; positivity
    set Kc : ℝ := Cc * (T ^ 6 + r + 2) ^ (ε / 2) * (2 * r + 1) with hKcdef
    have hKcnn : 0 ≤ Kc := by rw [hKcdef]; positivity
    have hcs : HasCompactSupport f := hasCompactSupport_of_SuppHyp hsup
    have hAmeas : MeasurableSet (Set.Icc (-(T ^ 6)) (T ^ 6)
        \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃)) :=
      measurableSet_Icc.diff measurableSet_Icc
    -- the pointwise Cauchy-Schwarz bound, with the pair count
    have hpoint : ∀ ξ ∈ (Set.Icc (-(T ^ 6)) (T ^ 6)
        \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃)),
        ‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
            Wwin K M₃ B (ξ / (m₁ : ℝ))‖ ^ 2
        ≤ Kc * ∑ p ∈ Pwin T M₁ M₃ B ξ, ‖aTerm K M₂ M₃ f ξ p‖ ^ 2 := by
      intro ξ hξ
      have hξle : |ξ| ≤ T ^ 6 := (mem_wtrRegion hξ).1
      rw [Wwin_sum_eq_pairs K T M₁ M₂ M₃ B hM₁ hM₃pos hξle]
      refine (norm_sum_sq_le_card_mul_sum_norm_sq (Pwin T M₁ M₃ B ξ)
        (fun p => aTerm K M₂ M₃ f ξ p)).trans ?_
      have hcard : ((Pwin T M₁ M₃ B ξ).card : ℝ) ≤ Kc := by
        have h := hcc T η B M₁ M₃ hT hη hB h2B hM₁ hM₃ ξ hξ
        rwa [hKcdef, hrdef]
      exact mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg (fun p _ => by positivity))

    have hFnn' : (0 : ℝ) ≤ FarMass K f M₂ M₃ :=
      tsum_nonneg (fun ℓ => integral_nonneg (fun τ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    have hFnn : 0 ≤ᵐ[volume.restrict (Set.Icc (-(T ^ 6)) (T ^ 6)
        \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃))]
        (fun ξ => ‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
            Wwin K M₃ B (ξ / (m₁ : ℝ))‖ ^ 2) :=
      Filter.Eventually.of_forall (fun ξ => sq_nonneg _)
    have hFmeas : AEStronglyMeasurable (fun ξ => ‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ *
        Bsum f M₂ (ξ / (m₁ : ℝ)) * Wwin K M₃ B (ξ / (m₁ : ℝ))‖ ^ 2)
        (volume.restrict (Set.Icc (-(T ^ 6)) (T ^ 6)
          \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃))) := by
      have h1 : AEStronglyMeasurable (fun ξ => ‖wtrS K T M₁ M₂ M₃ B f ξ‖ ^ 2)
          (volume.restrict (Set.Icc (-(T ^ 6)) (T ^ 6)
            \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃))) :=
        ((measurable_wtrS (K := K) (T := T) (M₁ := M₁) (M₂ := M₂) (M₃ := M₃) (B := B)
          hf hcs).norm.pow_const 2).aestronglyMeasurable
      refine h1.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hAmeas] with ξ hξ
      rw [wtrS_eq hM₁ hM₃pos hξ]
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hFnn hFmeas]
    have h1 : (∫⁻ ξ, ENNReal.ofReal (‖∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ *
          Bsum f M₂ (ξ / (m₁ : ℝ)) * Wwin K M₃ B (ξ / (m₁ : ℝ))‖ ^ 2)
          ∂(volume.restrict (Set.Icc (-(T ^ 6)) (T ^ 6)
            \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃))))
        ≤ ∫⁻ ξ, ENNReal.ofReal (Kc * ∑ p ∈ Pwin T M₁ M₃ B ξ, ‖aTerm K M₂ M₃ f ξ p‖ ^ 2)
          ∂(volume.restrict (Set.Icc (-(T ^ 6)) (T ^ 6)
            \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃))) := by
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem hAmeas] with ξ hξ
      exact ENNReal.ofReal_le_ofReal (hpoint ξ hξ)
    have h2 : (∫⁻ ξ, ENNReal.ofReal (Kc * ∑ p ∈ Pwin T M₁ M₃ B ξ, ‖aTerm K M₂ M₃ f ξ p‖ ^ 2)
          ∂(volume.restrict (Set.Icc (-(T ^ 6)) (T ^ 6)
            \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃))))
        = ENNReal.ofReal Kc * ∫⁻ ξ, ENNReal.ofReal (∑ p ∈ Pwin T M₁ M₃ B ξ,
            ‖aTerm K M₂ M₃ f ξ p‖ ^ 2)
          ∂(volume.restrict (Set.Icc (-(T ^ 6)) (T ^ 6)
            \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃))) := by
      have hpt : (fun ξ => ENNReal.ofReal (Kc * ∑ p ∈ Pwin T M₁ M₃ B ξ,
            ‖aTerm K M₂ M₃ f ξ p‖ ^ 2))
          = fun ξ => ENNReal.ofReal Kc * ENNReal.ofReal (∑ p ∈ Pwin T M₁ M₃ B ξ,
            ‖aTerm K M₂ M₃ f ξ p‖ ^ 2) := by
        funext ξ
        exact ENNReal.ofReal_mul hKcnn
      rw [hpt]
      exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    have h3 : (∫⁻ ξ, ENNReal.ofReal (∑ p ∈ Pwin T M₁ M₃ B ξ, ‖aTerm K M₂ M₃ f ξ p‖ ^ 2)
          ∂(volume.restrict (Set.Icc (-(T ^ 6)) (T ^ 6)
            \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃))))
        ≤ ENNReal.ofReal (Cmid * M₃ * FarMass K f M₂ M₃) :=
      hmid T M₁ M₂ M₃ B hM₁ hM₂ hM₃ f hf hfnn hsup
        (Set.Icc (-(T ^ 6)) (T ^ 6) \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃))
    have hfin : (∫⁻ ξ, ENNReal.ofReal (Kc * ∑ p ∈ Pwin T M₁ M₃ B ξ, ‖aTerm K M₂ M₃ f ξ p‖ ^ 2)
          ∂(volume.restrict (Set.Icc (-(T ^ 6)) (T ^ 6)
            \ Set.Icc (-(T ^ η * M₁ / M₃)) (T ^ η * M₁ / M₃)))) ≠ ⊤ := by
      rw [h2]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h3)
    have h4 : FarMass K f M₂ M₃ ≤ CW * WinMass f M₂ M₃ :=
      hCW M₂ M₃ hM₂ hM₃ f hf hfnn hsup
    have h5 : Kc * (Cmid * M₃ * FarMass K f M₂ M₃)
        ≤ Kc * (Cmid * M₃ * (CW * WinMass f M₂ M₃)) := by
      apply mul_le_mul_of_nonneg_left _ hKcnn
      apply mul_le_mul_of_nonneg_left h4
      positivity
    refine (ENNReal.toReal_mono hfin h1).trans ?_
    rw [h2, ENNReal.toReal_mul, ENNReal.toReal_ofReal hKcnn]
    refine (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono ENNReal.ofReal_ne_top h3) hKcnn).trans ?_
    rw [ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg hCmidpos.le hM₃pos.le) hFnn')]
    refine h5.trans ?_
    rw [hKcdef, hrdef]
    have harith := WindowFarCountArith (ε := ε) (εc := ε / 2) (Cc := Cc) (Cmid := Cmid) (CW := CW)
      (T := T) (B := B) (M₁ := M₁) (M₃ := M₃) (by linarith) (by linarith)
      hCcpos hCmidpos hCWpos hT hB hM₁ hM₃ hratio
    have h := mul_le_mul_of_nonneg_right harith hWnn
    have e1 : Cc * (T ^ 6 + 2 * B * M₁ / M₃ + 2) ^ (ε / 2) * (2 * (2 * B * M₁ / M₃) + 1) *
          (Cmid * M₃ * (CW * WinMass f M₂ M₃))
        = (Cc * (T ^ 6 + 2 * B * M₁ / M₃ + 2) ^ (ε / 2) * (2 * (2 * B * M₁ / M₃) + 1)
            * Cmid * M₃ * CW) * WinMass f M₂ M₃ := by ring
    rw [e1]
    exact h

end

end Work.GM.Affine
