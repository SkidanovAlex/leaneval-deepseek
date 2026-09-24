import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.assembly_aux
import Submission.Work.GM.Affine.plancherel_continuous
import Submission.Work.GM.Affine.low_freq_defs
import Submission.Commons.Analysis.Fourier.fejer_window_localization_majorant
import Submission.Work.GM.Affine.weighted_plancherel_sinc_sq
import Submission.Work.GM.Affine.fhat_tail_le_of_decay
import Submission.Work.GM.Affine.far_arith_le
import Submission.Work.GM.Affine.integral_sq_le_local_mass
import Submission.Work.GM.Affine.tri_weighted_le_local_mass

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option maxHeartbeats 4000000

namespace Work.GM.Affine

theorem local_mass_comparison {C₀ T₀ : ℝ} (hC₀ : 1 ≤ C₀) (hT₀ : 1 ≤ T₀)
    (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → Work.GM.Affine.SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Work.GM.Affine.Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∫ u, (f u) ^ 2 ≤ C * T ^ (2 * δ) * T
          * ∫ u, (f u) * (∫ v in Set.Icc (u - 1 / T) (u + 1 / T), f v) := by
  have hδ2 : (0:ℝ) < 2 * δ := by linarith
  have hxpos : 0 < (7 + 2 * δ) / (2 * δ) := by positivity
  set K : ℕ := Nat.ceil ((7 + 2 * δ) / (2 * δ)) with hKdef
  have hKle : ((7 + 2 * δ) / (2 * δ)) ≤ (K : ℝ) := Nat.le_ceil _
  set J : ℕ := K + 1 with hJdef
  have hK1 : 1 ≤ K := Nat.ceil_pos.mpr hxpos
  have hJ2 : 2 ≤ J := by omega
  have hMδ : 7 + 2 * δ ≤ ((2 * J - 1 : ℕ) : ℝ) * (2 * δ) := by
    have hcast : ((2 * J - 1 : ℕ) : ℝ) = 2 * (K:ℝ) + 1 := by
      have : (2 * J - 1 : ℕ) = 2 * K + 1 := by omega
      rw [this]; push_cast; ring
    rw [hcast]
    have h1 : 7 + 2 * δ ≤ (2 * δ) * (K:ℝ) := by
      have h2 := (div_le_iff₀ hδ2).mp hKle
      linarith
    nlinarith [h1]
  set cJ : ℝ := c J δ with hcJdef
  set X₀ : ℝ := (2 * cJ ^ 2 * (16 * (c 2 1)) ^ 2 * 4 ^ (2 * J - 1)
      / (((2 * J - 1 : ℕ)) : ℝ)) ^ ((1:ℝ) / (((2 * J - 1 : ℕ)) : ℝ)) with hX₀def
  set X₁ : ℝ := max X₀ 1 with hX₁def
  have hX₁1 : 1 ≤ X₁ := le_max_right _ _
  have hX₁X₀ : X₀ ≤ X₁ := le_max_left _ _
  refine ⟨2 * X₁ + 8 * C₀, by linarith, ?_⟩
  intro T hT f hf hnn hsupp Λ hΛpos hdec hcompat
  have hT1 : 1 ≤ T := le_trans hT₀ hT
  have hTpos : 0 < T := by linarith
  have hcs : HasCompactSupport f := hasCompactSupport_of_suppHyp hC₀ hsupp
  set V : ℝ := ∫ u, f u with hVdef
  have hVnn : 0 ≤ V := integral_nonneg hnn
  set Q : ℝ := ∫ u, f u * (∫ v in Set.Icc (u - 1 / T) (u + 1 / T), f v) with hQdef
  have hQnn : 0 ≤ Q := by
    rw [hQdef]; refine integral_nonneg (fun u => ?_)
    exact mul_nonneg (hnn u) (integral_nonneg hnn)
  by_cases hcJpos : 0 < c J δ
  swap
  · have hpt : ∀ ξ : ℝ, ξ ≠ 0 → Fhat f ξ = 0 := by
      intro ξ hξ
      have h1 := hdec J δ hδ ξ hξ
      have hTn : 0 ≤ T ^ δ := (Real.rpow_pos_of_pos hTpos _).le
      have hpn : 0 ≤ (T / |ξ|) ^ J := by positivity
      have hstep : c J δ * T ^ δ * (T / |ξ|) ^ J ≤ 0 := by
        have h2 : c J δ * T ^ δ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hcJpos) hTn
        exact mul_nonpos_of_nonpos_of_nonneg h2 hpn
      have h3 : c J δ * T ^ δ * (T / |ξ|) ^ J * Λ ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hstep hΛpos.le
      exact norm_eq_zero.mp (le_antisymm (le_trans h1 h3) (norm_nonneg _))
    have hzero : ∫ u, (f u) ^ 2 = 0 := by
      have hplan : ∫ u, (f u) ^ 2 = ∫ ξ, ‖Fhat f ξ‖ ^ 2 := by
        have h := plancherel_continuous (fun u : ℝ => ((f u : ℝ) : ℂ))
          (Complex.continuous_ofReal.comp hf) (hcs.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp))
        have hL : (∫ x, ‖(fun u : ℝ => ((f u : ℝ) : ℂ)) x‖ ^ 2) = ∫ u, (f u) ^ 2 := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with u
          simp
        rw [hL] at h
        have hR : (∫ ξ, ‖FourierTransform.fourier (fun u : ℝ => ((f u : ℝ) : ℂ)) ξ‖ ^ 2)
            = ∫ ξ, ‖Fhat f ξ‖ ^ 2 := rfl
        rw [hR] at h
        exact h
      rw [hplan]
      have hae : (fun ξ : ℝ => ‖Fhat f ξ‖ ^ 2) =ᵐ[volume] 0 := by
        rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
        apply measure_mono_null (t := {0})
        · intro ξ hξ
          simp only [Pi.zero_apply] at hξ ⊢
          by_contra h
          exact hξ (by rw [hpt ξ h]; simp)
        · simp
      exact MeasureTheory.integral_eq_zero_of_ae hae
    rw [hzero]
    have : 0 ≤ (2 * X₁ + 8 * C₀) * T ^ (2 * δ) * T * Q := by
      have h1 : 0 < (2 * X₁ + 8 * C₀) := by linarith
      have h2 : 0 < T ^ (2 * δ) := Real.rpow_pos_of_pos hTpos _
      positivity
    linarith
  · by_cases hcompos : 0 < 16 * (c 2 1) * T ^ 3 * V
    swap
    · exfalso
      linarith [hcompat, not_lt.mp hcompos, hΛpos]
    · -- MAIN case
      have hcJ' : 0 < cJ := hcJdef ▸ hcJpos
      have h16T3 : 0 < 16 * T ^ 3 := by positivity
      have hc21V : 0 < (c 2 1) * V := by
        have heq : 16 * (c 2 1) * T ^ 3 * V = (16 * T^3) * ((c 2 1) * V) := by ring
        exact (mul_pos_iff_of_pos_left h16T3).mp (heq ▸ hcompos)
      have hVpos : 0 < V := by
        rcases eq_or_lt_of_le hVnn with h | h
        · rw [← h] at hc21V; simp at hc21V
        · exact h
      have hc21pos : 0 < c 2 1 := by
        rcases lt_trichotomy (c 2 1) 0 with h | h | h
        · nlinarith [hc21V, hVnn, h]
        · rw [h, zero_mul] at hc21V; exact absurd hc21V (lt_irrefl 0)
        · exact h
      set B : ℝ := (cJ * 16 * (c 2 1) * (T ^ 3 * T ^ δ)) * V with hBdef
      have hBnn : 0 ≤ B := by
        rw [hBdef]
        have h1 : 0 < cJ * 16 * (c 2 1) * (T ^ 3 * T ^ δ) := by
          have := Real.rpow_pos_of_pos hTpos δ
          positivity
        exact mul_nonneg h1.le hVpos.le
      have hlev : ∀ ξ : ℝ, ξ ≠ 0 → ‖Fhat f ξ‖ ≤ B * (T / |ξ|) ^ J := by
        intro ξ hξ
        have h1 := hdec J δ hδ ξ hξ
        have h2 : c J δ * T ^ δ * (T / |ξ|) ^ J * Λ
            ≤ c J δ * T ^ δ * (T / |ξ|) ^ J * (16 * (c 2 1) * T ^ 3 * V) :=
          mul_le_mul_of_nonneg_left hcompat (by positivity)
        calc ‖Fhat f ξ‖ ≤ c J δ * T ^ δ * (T / |ξ|) ^ J * (16 * (c 2 1) * T ^ 3 * V) := le_trans h1 h2
          _ = B * (T / |ξ|) ^ J := by rw [hBdef]; ring
      have hplan : ∫ u, (f u) ^ 2 = ∫ ξ, ‖Fhat f ξ‖ ^ 2 := by
        have h := plancherel_continuous (fun u : ℝ => ((f u : ℝ) : ℂ))
          (Complex.continuous_ofReal.comp hf) (hcs.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp))
        have hL : (∫ x, ‖(fun u : ℝ => ((f u : ℝ) : ℂ)) x‖ ^ 2) = ∫ u, (f u) ^ 2 := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with u
          simp
        rw [hL] at h
        have hR : (∫ ξ, ‖FourierTransform.fourier (fun u : ℝ => ((f u : ℝ) : ℂ)) ξ‖ ^ 2)
            = ∫ ξ, ‖Fhat f ξ‖ ^ 2 := rfl
        rw [hR] at h
        exact h
      by_cases hS0 : ∫ u, (f u) ^ 2 = 0
      · rw [hS0]
        have : 0 ≤ (2 * X₁ + 8 * C₀) * T ^ (2 * δ) * T * Q := by
          have h1 : 0 < (2 * X₁ + 8 * C₀) := by linarith
          have h2 : 0 < T ^ (2 * δ) := Real.rpow_pos_of_pos hTpos _
          positivity
        linarith
      · have hint : Integrable (fun ξ : ℝ => ‖Fhat f ξ‖ ^ 2) := by
          by_contra hcon
          have hz : (∫ ξ, ‖Fhat f ξ‖ ^ 2) = 0 := integral_undef hcon
          rw [← hplan] at hz
          exact hS0 hz
        set Y : ℝ := T ^ (1 + 2 * δ) * X₁ with hYdef
        have hYpos : 0 < Y := by
          rw [hYdef]; have := Real.rpow_pos_of_pos hTpos (1 + 2*δ); positivity
        have hYT : T ≤ Y := by
          rw [hYdef]
          have h1 : T ≤ T ^ (1 + 2 * δ) := by
            have h2 := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith : (1:ℝ) ≤ 1 + 2 * δ)
            rwa [Real.rpow_one] at h2
          have h3 : 0 ≤ T ^ (1 + 2 * δ) := (Real.rpow_pos_of_pos hTpos _).le
          nlinarith [h1, hX₁1, h3]
        set ψ : ℝ → ℝ := fun ξ => (Real.sinc (Real.pi * (ξ / Y))) ^ 2 with hψdef
        have hψnn : ∀ ξ, 0 ≤ ψ ξ := fun ξ => by rw [hψdef]; positivity
        have hψle : ∀ ξ, ψ ξ ≤ 1 := by
          intro ξ
          rw [hψdef]
          have h := Real.abs_sinc_le_one (Real.pi * (ξ / Y))
          nlinarith [h, abs_nonneg (Real.sinc (Real.pi * (ξ / Y))), sq_abs (Real.sinc (Real.pi * (ξ/Y)))]
        have hψcont : Continuous ψ := by rw [hψdef]; fun_prop
        have hintψ : Integrable (fun ξ : ℝ => ψ ξ * ‖Fhat f ξ‖ ^ 2) := by
          have hb : ∀ᵐ ξ ∂(volume : Measure ℝ), ‖ψ ξ‖ ≤ 1 := by
            filter_upwards with ξ
            rw [Real.norm_eq_abs, abs_of_nonneg (hψnn ξ)]
            exact hψle ξ
          exact hint.bdd_mul (f := ψ) hψcont.aestronglyMeasurable hb
        -- (A) low part controlled by the weighted integral
        have hA : ∫ ξ in Set.Ioo (-(Y/4)) (Y/4), ‖Fhat f ξ‖ ^ 2
            ≤ 2 * ∫ ξ, ψ ξ * ‖Fhat f ξ‖ ^ 2 := by
          have hpt : ∀ ξ ∈ Set.Ioo (-(Y/4)) (Y/4), ‖Fhat f ξ‖ ^ 2 ≤ 2 * ψ ξ * ‖Fhat f ξ‖ ^ 2 := by
            intro ξ hξ
            rw [Set.mem_Ioo] at hξ
            have h1 : |ξ| < Y / 4 := by rw [abs_lt]; exact ⟨by linarith [hξ.1], hξ.2⟩
            have h2 : |ξ / Y| ≤ 1 / 4 := by
              rw [abs_div, abs_of_pos hYpos, div_le_iff₀ hYpos]
              linarith [h1.le]
            have h3 : (1:ℝ)/2 ≤ ψ ξ := by
              rw [hψdef]; exact Commons.Analysis.Fourier.sinc_pi_sq_lower_bound h2
            nlinarith [h3, sq_nonneg ‖Fhat f ξ‖]
          have hint2 : Integrable (fun ξ : ℝ => 2 * ψ ξ * ‖Fhat f ξ‖ ^ 2) := by
            simpa only [mul_assoc] using hintψ.const_mul 2
          have hmono : ∫ ξ in Set.Ioo (-(Y/4)) (Y/4), ‖Fhat f ξ‖ ^ 2
              ≤ ∫ ξ in Set.Ioo (-(Y/4)) (Y/4), 2 * ψ ξ * ‖Fhat f ξ‖ ^ 2 :=
            setIntegral_mono_on (hint.integrableOn) (hint2.integrableOn)
              measurableSet_Ioo (fun ξ hξ => hpt ξ hξ)
          have hle : ∫ ξ in Set.Ioo (-(Y/4)) (Y/4), 2 * ψ ξ * ‖Fhat f ξ‖ ^ 2
              ≤ ∫ ξ, 2 * ψ ξ * ‖Fhat f ξ‖ ^ 2 :=
            setIntegral_le_integral hint2
              (Filter.Eventually.of_forall (fun ξ => by positivity))
          have hconst : ∫ ξ, 2 * ψ ξ * ‖Fhat f ξ‖ ^ 2 = 2 * ∫ ξ, ψ ξ * ‖Fhat f ξ‖ ^ 2 := by
            rw [← integral_const_mul]
            congr 1
            ext ξ
            ring
          linarith [hmono, hle, hconst.le, hconst.ge]
        -- (B) the weighted integral is bounded by Y*Q
        have hBw : ∫ ξ, ψ ξ * ‖Fhat f ξ‖ ^ 2 ≤ Y * Q := by
          have hw := weighted_plancherel_sinc_sq (Y := Y) hYpos hf hcs
          rw [hw, hQdef]
          exact tri_weighted_le_local_mass (T := T) (Y := Y) hT1 hYT hf hnn hcs
        -- (C) the high part
        have hC : ∫ ξ in {ξ : ℝ | Y / 4 ≤ |ξ|}, ‖Fhat f ξ‖ ^ 2 ≤ V ^ 2 := by
          have hY4 : 0 < Y / 4 := by linarith
          have htail := fhat_tail_le_of_decay (f := f) (B := B) (T := T) (Y := Y / 4) hJ2 hBnn hTpos hY4 hint hlev
          have hX₀pos : 0 < X₀ := by
            rw [hX₀def]
            apply Real.rpow_pos_of_pos
            have hden : (0:ℝ) < (((2 * J - 1 : ℕ)) : ℝ) := by
              have h : (1:ℕ) ≤ 2 * J - 1 := by omega
              exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h
            have h1 : 0 < cJ := hcJ'
            have h2 : 0 < c 2 1 := hc21pos
            positivity
          have hX₀eq : X₀ ^ (2 * J - 1) * (((2 * J - 1 : ℕ)) : ℝ)
              = 2 * (cJ * 16 * (c 2 1)) ^ 2 * 4 ^ (2 * J - 1) := by
            have hden : (0:ℝ) < (((2 * J - 1 : ℕ)) : ℝ) := by
              have h : (1:ℕ) ≤ 2 * J - 1 := by omega
              exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h
            have hbase : (0:ℝ) ≤ 2 * cJ ^ 2 * (16 * (c 2 1)) ^ 2 * 4 ^ (2 * J - 1)
                / (((2 * J - 1 : ℕ)) : ℝ) := by positivity
            rw [hX₀def, ← Real.rpow_natCast, ← Real.rpow_mul hbase]
            rw [one_div, inv_mul_cancel₀ (ne_of_gt hden), Real.rpow_one]
            field_simp
          have harith : 2 * B ^ 2 * T ^ (2 * J)
              / ((2 * (J:ℝ) - 1) * (Y / 4) ^ (2 * J - 1)) ≤ V ^ 2 := by
            have hfar := far_arith_le (T := T) (V := V) (a := cJ * 16 * (c 2 1)) (X₀ := X₀)
              (X₁ := X₁) (δ := δ) (M := 2 * J - 1) hT1 hVnn (by omega) hδ hMδ hX₀pos hX₁X₀ hX₀eq
            have hM1 : (2 * J - 1) + 1 = 2 * J := by omega
            rw [hM1] at hfar
            have hcast : ((2 * J - 1 : ℕ) : ℝ) = 2 * (J:ℝ) - 1 := by
              have h : (1:ℕ) ≤ 2 * J := by omega
              push_cast [Nat.cast_sub h]
              ring
            rw [hcast] at hfar
            rw [hBdef, hYdef]
            exact hfar
          calc ∫ ξ in {ξ : ℝ | Y / 4 ≤ |ξ|}, ‖Fhat f ξ‖ ^ 2
              ≤ 2 * B ^ 2 * T ^ (2 * J)
                  / ((2 * (J:ℝ) - 1) * (Y / 4) ^ (2 * J - 1)) := htail
            _ ≤ V ^ 2 := harith
        -- split
        have hsplit := MeasureTheory.integral_add_compl (s := Set.Ioo (-(Y/4)) (Y/4))
          measurableSet_Ioo hint
        have hcompl : (Set.Ioo (-(Y/4)) (Y/4))ᶜ = {ξ : ℝ | Y / 4 ≤ |ξ|} := by
          ext ξ
          simp only [Set.mem_compl_iff, Set.mem_Ioo, Set.mem_setOf_eq]
          rw [le_abs]
          constructor
          · intro h
            by_cases hc : -(Y / 4) < ξ
            · left; by_contra h2; exact h ⟨hc, lt_of_not_ge h2⟩
            · right; push_neg at hc; linarith
          · rintro (h | h) ⟨h1, h2⟩ <;> linarith
        have hSle : ∫ ξ, ‖Fhat f ξ‖ ^ 2 ≤ 2 * (Y * Q) + V ^ 2 := by
          have := hsplit
          rw [hcompl] at this
          linarith [this, hA, hBw, hC]
        have hV2 : V ^ 2 ≤ 4 * C₀ * T * Q := by
          rw [hVdef, hQdef]
          exact integral_sq_le_local_mass (C₀ := C₀) (T := T) hC₀ hT1 hf hnn hsupp
        rw [hplan]
        have hfin : 2 * (Y * Q) + V ^ 2 ≤ (2 * X₁ + 8 * C₀) * T ^ (2 * δ) * T * Q := by
          have hYeq : Y = T ^ (1 + 2 * δ) * X₁ := hYdef
          have hTR : T ^ (2 * δ) * T = T ^ (1 + 2 * δ) := by
            have h1 : T ^ (2 * δ) * T = T ^ (2 * δ) * T ^ (1:ℝ) := by rw [Real.rpow_one]
            rw [h1, ← Real.rpow_add hTpos (2 * δ) 1]
            congr 1
            ring
          have hTX : T ≤ T ^ (1 + 2 * δ) := by
            have h2 := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith : (1:ℝ) ≤ 1 + 2 * δ)
            rwa [Real.rpow_one] at h2
          rw [hYeq]
          rw [show (2 * X₁ + 8 * C₀) * T ^ (2 * δ) * T * Q
              = (2 * X₁ + 8 * C₀) * (T ^ (2 * δ) * T) * Q from by ring, hTR]
          have hp := Real.rpow_pos_of_pos hTpos (1 + 2 * δ)
          nlinarith [hV2, hTX, hQnn, hX₁1, hp, hTpos, hC₀]
        linarith [hfin, hSle]



end Work.GM.Affine
