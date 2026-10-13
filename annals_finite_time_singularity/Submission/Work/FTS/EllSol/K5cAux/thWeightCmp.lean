/-
# `Work.FTS.EllSol.K5cAux.thWeightCmp`

The angular weight `σ θ = sin(2θ)^{-η}` (`η = Work.Spaces.eta = 99/100`) is comparable with
itself mollified at scale `ε ≤ 1/2` with the (doubly odd) kernel `sKer ε`:

  `∫_{Iθ} σ θ · (ρ_ε(θ-u) + ρ_ε(θ+u) + ρ_ε(θ+u-π)) ≤ K · σ u`  for `u ∈ (0, π/2)`.

The three kernels are the three "images" of `u` under the reflections generating the doubly odd
extension, so the statement is the standard power-weight comparison for a mollifier.  The
elementary estimates live in `Submission.Work.FTS.EllSol.K5cAux.thWeightAux`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllSol.K5cAux.thWeightAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.K5cAux

open Work.FTS.EllSol.PkgK5.K5c

local notation "σ" => Work.FTS.EllipticEst.thEta
local notation "η" => Work.Spaces.eta
local notation "Iθ" => Work.Spaces.Iθ


theorem thWeightCmp : ∃ K : ℝ, 0 < K ∧ ∀ (ε u : ℝ), 0 < ε → ε ≤ 1 / 2 →
    u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ *
        (Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ - u) + Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + u)
          + Work.FTS.EllSol.PkgK5.K5c.sKer ε (θ + u - Real.pi)))
      ≤ K * Work.FTS.EllipticEst.thEta u := by
  set Clayer : ℝ := (Real.pi / 4) ^ η / (1 - η) with hCl
  set K₁ : ℝ := Clayer * 3 ^ (1 - η) * 4 ^ η * sMass⁻¹ with hK₁
  set K₂ : ℝ := Clayer * 2 ^ η * sMass⁻¹ with hK₂
  set K₃ : ℝ := 30000 * ((Real.pi / 12) * sMass)⁻¹ with hK₃
  set Kbig : ℝ := 1 + (K₁ + Real.pi ^ η) + 2 * K₂ + K₃ with hKbig
  have hCl_nn : 0 ≤ Clayer := by
    rw [hCl]; exact div_nonneg (Real.rpow_nonneg (by positivity) _) one_sub_eta_pos.le
  have hπ_nn : 0 ≤ Real.pi ^ η := Real.rpow_nonneg (by positivity) _
  have hK₁_nn : 0 ≤ K₁ := by
    rw [hK₁]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCl_nn (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg (by norm_num) _)) (inv_nonneg.mpr sMass_pos.le)
  have hK₂_nn : 0 ≤ K₂ := by
    rw [hK₂]
    exact mul_nonneg (mul_nonneg hCl_nn (Real.rpow_nonneg (by norm_num) _))
      (inv_nonneg.mpr sMass_pos.le)
  have hK₃_nn : 0 ≤ K₃ := by
    rw [hK₃]
    exact mul_nonneg (by norm_num)
      (inv_nonneg.mpr (mul_nonneg (by positivity) sMass_pos.le))
  have hKbig_pos : 0 < Kbig := by rw [hKbig]; linarith
  refine ⟨Kbig, hKbig_pos, ?_⟩
  intro ε u hε hε2 hu
  obtain ⟨hu0, hu2⟩ := hu
  have hσu_pos : 0 < σ u := sigma_pos hu0 hu2
  have hσu_nn : 0 ≤ σ u := hσu_pos.le
  have hsMass_nn : 0 ≤ sMass := sMass_pos.le
  have hinv_nn : 0 ≤ (ε * sMass)⁻¹ := inv_nonneg.mpr (mul_nonneg hε.le hsMass_nn)
  have hshift₁ := integrableOn_sigma_sKer_shift (ε := ε) (v := -u) hε
  have hshift₂ := integrableOn_sigma_sKer_shift (ε := ε) (v := u) hε
  have hshift₃ := integrableOn_sigma_sKer_shift (ε := ε) (v := u - Real.pi) hε
  have hshift₁' : IntegrableOn (fun θ : ℝ => σ θ * sKer ε (θ - u)) Iθ := hshift₁
  have hshift₃' : IntegrableOn (fun θ : ℝ => σ θ * sKer ε (θ + u - Real.pi)) Iθ := by
    simpa only [sub_eq_add_neg, add_assoc] using hshift₃
  have hsum_eq : (fun θ : ℝ => σ θ *
        (sKer ε (θ - u) + sKer ε (θ + u) + sKer ε (θ + u - Real.pi)))
      = fun θ : ℝ => (σ θ * sKer ε (θ - u) + σ θ * sKer ε (θ + u))
          + σ θ * sKer ε (θ + u - Real.pi) := by
    funext θ; ring
  have hsplit : (∫ θ in Iθ, σ θ *
        (sKer ε (θ - u) + sKer ε (θ + u) + sKer ε (θ + u - Real.pi)))
      = (∫ θ in Iθ, σ θ * sKer ε (θ - u)) + (∫ θ in Iθ, σ θ * sKer ε (θ + u))
        + (∫ θ in Iθ, σ θ * sKer ε (θ + u - Real.pi)) := by
    have h1 : (∫ θ in Iθ, σ θ * sKer ε (θ - u) + σ θ * sKer ε (θ + u))
        = (∫ θ in Iθ, σ θ * sKer ε (θ - u)) + (∫ θ in Iθ, σ θ * sKer ε (θ + u)) :=
      integral_add hshift₁' hshift₂
    have h2 : (∫ θ in Iθ, (σ θ * sKer ε (θ - u) + σ θ * sKer ε (θ + u))
          + σ θ * sKer ε (θ + u - Real.pi))
        = (∫ θ in Iθ, σ θ * sKer ε (θ - u) + σ θ * sKer ε (θ + u))
          + (∫ θ in Iθ, σ θ * sKer ε (θ + u - Real.pi)) :=
      integral_add (hshift₁'.add hshift₂) hshift₃'
    rw [hsum_eq, h2, h1]
  by_cases hεbig : Real.pi / 12 < ε
  · -- Case I: `ε` is bounded below, so the crude bound suffices.
    have hpt : ∀ θ ∈ Iθ, σ θ * (sKer ε (θ - u) + sKer ε (θ + u) + sKer ε (θ + u - Real.pi))
        ≤ (3 * (ε * sMass)⁻¹) * σ θ := by
      intro θ hθ
      have hσ : 0 ≤ σ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
      have h1 := sKer_le_inv hε (θ - u)
      have h2 := sKer_le_inv hε (θ + u)
      have h3 := sKer_le_inv hε (θ + u - Real.pi)
      have hsum : sKer ε (θ - u) + sKer ε (θ + u) + sKer ε (θ + u - Real.pi)
          ≤ 3 * (ε * sMass)⁻¹ := by linarith
      calc σ θ * (sKer ε (θ - u) + sKer ε (θ + u) + sKer ε (θ + u - Real.pi))
          ≤ σ θ * (3 * (ε * sMass)⁻¹) := mul_le_mul_of_nonneg_left hsum hσ
        _ = (3 * (ε * sMass)⁻¹) * σ θ := by ring
    have hIntL : IntegrableOn (fun θ : ℝ => σ θ *
        (sKer ε (θ - u) + sKer ε (θ + u) + sKer ε (θ + u - Real.pi))) Iθ := by
      rw [hsum_eq]
      exact (hshift₁'.add hshift₂).add hshift₃'
    have hIntR : IntegrableOn (fun θ : ℝ => (3 * (ε * sMass)⁻¹) * σ θ) Iθ :=
      (Work.FTS.EllipticEst.integrableOn_thEta.1).const_mul _
    have hmono := integral_mono_ae hIntL hIntR
      (ae_restrict_of_forall_mem measurableSet_Icc hpt)
    rw [integral_const_mul] at hmono
    have hσint : (∫ θ in Iθ, σ θ) ≤ 10000 := Work.FTS.EllipticEst.integrableOn_thEta.2
    have hinv : (ε * sMass)⁻¹ ≤ ((Real.pi / 12) * sMass)⁻¹ :=
      inv_anti₀ (mul_pos (by positivity) sMass_pos)
        (mul_le_mul_of_nonneg_right hεbig.le hsMass_nn)
    have hstep : (∫ θ in Iθ, σ θ *
        (sKer ε (θ - u) + sKer ε (θ + u) + sKer ε (θ + u - Real.pi))) ≤ K₃ := by
      calc (∫ θ in Iθ, σ θ *
            (sKer ε (θ - u) + sKer ε (θ + u) + sKer ε (θ + u - Real.pi)))
          ≤ (3 * (ε * sMass)⁻¹) * (∫ θ in Iθ, σ θ) := hmono
        _ ≤ (3 * (ε * sMass)⁻¹) * 10000 :=
            mul_le_mul_of_nonneg_left hσint (by positivity)
        _ = 30000 * (ε * sMass)⁻¹ := by ring
        _ ≤ 30000 * ((Real.pi / 12) * sMass)⁻¹ := mul_le_mul_of_nonneg_left hinv (by norm_num)
        _ = K₃ := by rw [hK₃]
    calc (∫ θ in Iθ, σ θ *
          (sKer ε (θ - u) + sKer ε (θ + u) + sKer ε (θ + u - Real.pi))) ≤ K₃ := hstep
      _ = K₃ * 1 := (mul_one K₃).symm
      _ ≤ K₃ * σ u := mul_le_mul_of_nonneg_left (one_le_sigma hu0 hu2) hK₃_nn
      _ ≤ Kbig * σ u := by
          refine mul_le_mul_of_nonneg_right ?_ hσu_nn
          rw [hKbig]; linarith
  · -- Case II: `ε ≤ π/12`.
    push_neg at hεbig
    have h3ε : 3 * ε ≤ Real.pi / 4 := by linarith [Real.pi_pos]
    have h3π : 3 * ε ≤ Real.pi / 2 := by linarith [Real.pi_pos]
    -- the middle kernel
    have hTmid : (∫ θ in Iθ, σ θ * sKer ε (θ - u)) ≤ max K₁ (Real.pi ^ η) * σ u := by
      by_cases hfar : 2 * ε ≤ min u (Real.pi / 2 - u)
      · have hpt : ∀ θ ∈ Iθ, σ θ * sKer ε (θ - u) ≤ (Real.pi ^ η * σ u) * sKer ε (θ - u) := by
          intro θ _
          by_cases hk : sKer ε (θ - u) = 0
          · rw [hk, mul_zero, mul_zero]
          · have hkpos : 0 < sKer ε (θ - u) :=
              lt_of_le_of_ne (sKer_nonneg hε _) (Ne.symm hk)
            have habs : |θ - u| < ε := by
              by_contra hcon
              exact hk (sKer_eq_zero_of_le_abs hε (not_lt.mp hcon))
            exact mul_le_mul_of_nonneg_right (sigma_le_of_far hu0 hu2 hε hfar habs) hkpos.le
        have hIntR : IntegrableOn (fun θ : ℝ => (Real.pi ^ η * σ u) * sKer ε (θ - u)) Iθ :=
          (((continuous_sKer ε).comp (continuous_id.sub continuous_const)).integrableOn_Icc
            |>.const_mul _)
        have hmono := integral_mono_ae hshift₁' hIntR
          (ae_restrict_of_forall_mem measurableSet_Icc hpt)
        rw [integral_const_mul] at hmono
        have hstep : (∫ θ in Iθ, σ θ * sKer ε (θ - u)) ≤ Real.pi ^ η * σ u :=
          calc (∫ θ in Iθ, σ θ * sKer ε (θ - u))
              ≤ (Real.pi ^ η * σ u) * ∫ θ in Iθ, sKer ε (θ - u) := hmono
            _ ≤ (Real.pi ^ η * σ u) * 1 :=
                mul_le_mul_of_nonneg_left (integral_Iθ_sKer_sub_le_one hε)
                  (mul_nonneg hπ_nn hσu_nn)
            _ = Real.pi ^ η * σ u := by ring
        calc (∫ θ in Iθ, σ θ * sKer ε (θ - u)) ≤ Real.pi ^ η * σ u := hstep
          _ ≤ max K₁ (Real.pi ^ η) * σ u :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) hσu_nn
      · have hnear : min u (Real.pi / 2 - u) < 2 * ε := not_le.mp hfar
        have h4η : ε ^ (-η) ≤ 4 ^ η * σ u :=
          inv_rpow_le_four_of_le hε (sigma_ge_four_eps hu0 hu2 hε hnear)
        have hstep : (∫ θ in Iθ, σ θ * sKer ε (θ - u))
            ≤ Clayer * 3 ^ (1 - η) * 4 ^ η * sMass⁻¹ * σ u := by
          by_cases hu2e : u < 2 * ε
          · have hpt : ∀ θ ∈ Iθ, σ θ * sKer ε (θ - u) ≤
                (ε * sMass)⁻¹ * (σ θ *
                  Set.indicator (Set.Icc 0 (3 * ε)) (fun _ => (1 : ℝ)) θ) := by
              intro θ hθ
              have hθ0 : 0 ≤ θ := (show θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) from hθ).1
              have hσ : 0 ≤ σ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
              by_cases hle : θ ≤ 3 * ε
              · have hind : Set.indicator (Set.Icc (0 : ℝ) (3 * ε)) (fun _ => (1 : ℝ)) θ = 1 :=
                  Set.indicator_of_mem (by rw [Set.mem_Icc]; exact ⟨hθ0, hle⟩) _
                rw [hind, mul_one]
                calc σ θ * sKer ε (θ - u) ≤ σ θ * (ε * sMass)⁻¹ :=
                      mul_le_mul_of_nonneg_left (sKer_le_inv hε _) hσ
                  _ = (ε * sMass)⁻¹ * σ θ := by ring
              · have hzu : ε < θ - u := by linarith [not_le.mp hle]
                have hz : sKer ε (θ - u) = 0 := sKer_eq_zero_of_le_abs hε (by
                  rw [abs_of_pos (by linarith : (0 : ℝ) < θ - u)]; exact hzu.le)
                rw [hz, mul_zero]
                exact mul_nonneg hinv_nn
                  (mul_nonneg hσ (Set.indicator_nonneg (fun _ _ => zero_le_one) θ))
            have hmono := integral_mono_ae hshift₁'
              (integrableOn_sigma_indicator_mul (c := (ε * sMass)⁻¹) hinv_nn measurableSet_Icc)
              (ae_restrict_of_forall_mem measurableSet_Icc hpt)
            rw [integral_const_mul,
              indicator_left_setIntegral (b := 3 * ε) (by linarith) h3π] at hmono
            calc (∫ θ in Iθ, σ θ * sKer ε (θ - u))
                ≤ (ε * sMass)⁻¹ * (∫ θ in (0 : ℝ)..(3 * ε), σ θ) := hmono
              _ ≤ (ε * sMass)⁻¹ * (Clayer * (3 * ε) ^ (1 - η)) := by
                  refine mul_le_mul_of_nonneg_left ?_ hinv_nn
                  have h := integral_thEta_zero_a (a := 3 * ε) (by linarith) h3ε
                  rw [hCl]
                  calc ∫ θ in (0 : ℝ)..(3 * ε), σ θ
                      ≤ (Real.pi / 4) ^ η * (3 * ε) ^ (1 - η) / (1 - η) := h
                    _ = (Real.pi / 4) ^ η / (1 - η) * (3 * ε) ^ (1 - η) := by ring
              _ ≤ Clayer * 3 ^ (1 - η) * 4 ^ η * sMass⁻¹ * σ u := by
                  rw [hCl]; exact window_le_three hε h4η
          · have hu2e' : 2 * ε ≤ u := not_lt.mp hu2e
            have hpu : Real.pi / 2 - u < 2 * ε := by
              by_contra hcon
              exact absurd (le_min hu2e' (not_lt.mp hcon)) (not_le.mpr hnear)
            have hpt : ∀ θ ∈ Iθ, σ θ * sKer ε (θ - u) ≤
                (ε * sMass)⁻¹ * (σ θ *
                  Set.indicator (Set.Icc (Real.pi / 2 - 3 * ε) (Real.pi / 2))
                    (fun _ => (1 : ℝ)) θ) := by
              intro θ hθ
              have hθ1 : θ ≤ Real.pi / 2 := (show θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) from hθ).2
              have hσ : 0 ≤ σ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
              by_cases hge : Real.pi / 2 - 3 * ε ≤ θ
              · have hind : Set.indicator (Set.Icc (Real.pi / 2 - 3 * ε) (Real.pi / 2))
                    (fun _ => (1 : ℝ)) θ = 1 :=
                  Set.indicator_of_mem (by rw [Set.mem_Icc]; exact ⟨hge, hθ1⟩) _
                rw [hind, mul_one]
                calc σ θ * sKer ε (θ - u) ≤ σ θ * (ε * sMass)⁻¹ :=
                      mul_le_mul_of_nonneg_left (sKer_le_inv hε _) hσ
                  _ = (ε * sMass)⁻¹ * σ θ := by ring
              · have hz : sKer ε (θ - u) = 0 := sKer_eq_zero_of_le_abs hε (by
                  rw [abs_of_neg (by linarith [not_le.mp hge])]; linarith [not_le.mp hge])
                rw [hz, mul_zero]
                exact mul_nonneg hinv_nn
                  (mul_nonneg hσ (Set.indicator_nonneg (fun _ _ => zero_le_one) θ))
            have hmono := integral_mono_ae hshift₁'
              (integrableOn_sigma_indicator_mul (c := (ε * sMass)⁻¹) hinv_nn measurableSet_Icc)
              (ae_restrict_of_forall_mem measurableSet_Icc hpt)
            rw [integral_const_mul,
              indicator_right_setIntegral (a := 3 * ε) (by linarith) (by linarith [Real.pi_pos])]
              at hmono
            calc (∫ θ in Iθ, σ θ * sKer ε (θ - u))
                ≤ (ε * sMass)⁻¹ * (∫ θ in (Real.pi / 2 - 3 * ε)..(Real.pi / 2), σ θ) := hmono
              _ ≤ (ε * sMass)⁻¹ * (Clayer * (3 * ε) ^ (1 - η)) := by
                  refine mul_le_mul_of_nonneg_left ?_ hinv_nn
                  have h := integral_thEta_right_layer (a := 3 * ε) (by linarith) h3ε
                  rw [hCl]
                  calc ∫ θ in (Real.pi / 2 - 3 * ε)..(Real.pi / 2), σ θ
                      ≤ (Real.pi / 4) ^ η * (3 * ε) ^ (1 - η) / (1 - η) := h
                    _ = (Real.pi / 4) ^ η / (1 - η) * (3 * ε) ^ (1 - η) := by ring
              _ ≤ Clayer * 3 ^ (1 - η) * 4 ^ η * sMass⁻¹ * σ u := by
                  rw [hCl]; exact window_le_three hε h4η
        calc (∫ θ in Iθ, σ θ * sKer ε (θ - u))
            ≤ Clayer * 3 ^ (1 - η) * 4 ^ η * sMass⁻¹ * σ u := hstep
          _ = K₁ * σ u := by rw [← hK₁]
          _ ≤ max K₁ (Real.pi ^ η) * σ u :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hσu_nn
    -- the reflected kernel
    have hTleft : (∫ θ in Iθ, σ θ * sKer ε (θ + u)) ≤ K₂ * σ u := by
      by_cases hu_lt : u < ε
      · have hδ0 : 0 < ε - u := by linarith
        have hδπ : ε - u ≤ Real.pi / 2 := by linarith [Real.pi_pos]
        have hδ4 : ε - u ≤ Real.pi / 4 := by linarith [Real.pi_pos, hεbig]
        have hpt : ∀ θ ∈ Iθ, σ θ * sKer ε (θ + u) ≤
            (ε * sMass)⁻¹ * (σ θ *
              Set.indicator (Set.Icc 0 (ε - u)) (fun _ => (1 : ℝ)) θ) := by
          intro θ hθ
          have hθ0 : 0 ≤ θ := (show θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) from hθ).1
          have hσ : 0 ≤ σ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
          by_cases hle : θ ≤ ε - u
          · have hind : Set.indicator (Set.Icc (0 : ℝ) (ε - u)) (fun _ => (1 : ℝ)) θ = 1 :=
              Set.indicator_of_mem (by rw [Set.mem_Icc]; exact ⟨hθ0, hle⟩) _
            rw [hind, mul_one]
            calc σ θ * sKer ε (θ + u) ≤ σ θ * (ε * sMass)⁻¹ :=
                  mul_le_mul_of_nonneg_left (sKer_le_inv hε _) hσ
              _ = (ε * sMass)⁻¹ * σ θ := by ring
          · have hzu : ε < θ + u := by linarith [not_le.mp hle]
            have hz : sKer ε (θ + u) = 0 := sKer_eq_zero_of_le_abs hε (by
              rw [abs_of_pos (by linarith : (0 : ℝ) < θ + u)]; exact hzu.le)
            rw [hz, mul_zero]
            exact mul_nonneg hinv_nn
              (mul_nonneg hσ (Set.indicator_nonneg (fun _ _ => zero_le_one) θ))
        have hmono := integral_mono_ae hshift₂
          (integrableOn_sigma_indicator_mul (c := (ε * sMass)⁻¹) hinv_nn measurableSet_Icc)
          (ae_restrict_of_forall_mem measurableSet_Icc hpt)
        rw [integral_const_mul,
          indicator_left_setIntegral (b := ε - u) hδ0.le hδπ] at hmono
        have h2η : ε ^ (-η) ≤ 2 ^ η * σ u :=
          inv_rpow_le_two_of_le hε (sigma_ge_two_eps hu0 hu2 hε (Or.inl hu_lt))
        calc (∫ θ in Iθ, σ θ * sKer ε (θ + u))
            ≤ (ε * sMass)⁻¹ * (∫ θ in (0 : ℝ)..(ε - u), σ θ) := hmono
          _ ≤ (ε * sMass)⁻¹ * (Clayer * (ε - u) ^ (1 - η)) := by
              refine mul_le_mul_of_nonneg_left ?_ hinv_nn
              have h := integral_thEta_zero_a (a := ε - u) hδ0 hδ4
              rw [hCl]
              calc ∫ θ in (0 : ℝ)..(ε - u), σ θ
                  ≤ (Real.pi / 4) ^ η * (ε - u) ^ (1 - η) / (1 - η) := h
                _ = (Real.pi / 4) ^ η / (1 - η) * (ε - u) ^ (1 - η) := by ring
          _ ≤ Clayer * 2 ^ η * sMass⁻¹ * σ u := by
              rw [hCl]; exact window_le_two hε hδ0.le (by linarith) h2η
          _ = K₂ * σ u := by rw [← hK₂]
      · have hzero : (∫ θ in Iθ, σ θ * sKer ε (θ + u)) = 0 := by
          have h1 : (∫ θ in Iθ, σ θ * sKer ε (θ + u)) = ∫ θ in Iθ, (0 : ℝ) := by
            refine integral_congr_ae ?_
            filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
            have hθ0 : 0 ≤ θ := (show θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) from hθ).1
            have hzu : ε ≤ θ + u := by linarith [not_lt.mp hu_lt]
            rw [sKer_eq_zero_of_le_abs hε (by
              rw [abs_of_pos (by linarith : (0 : ℝ) < θ + u)]; exact hzu), mul_zero]
          rw [h1, integral_zero]
        rw [hzero]
        exact mul_nonneg hK₂_nn hσu_nn
    -- the third (right reflected) kernel
    have hTright : (∫ θ in Iθ, σ θ * sKer ε (θ + u - Real.pi)) ≤ K₂ * σ u := by
      by_cases hpu_lt : Real.pi / 2 - u < ε
      · have hδ0 : 0 < ε - (Real.pi / 2 - u) := by linarith
        have hδπ : ε - (Real.pi / 2 - u) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
        have hδ4 : ε - (Real.pi / 2 - u) ≤ Real.pi / 4 := by linarith [Real.pi_pos, hεbig]
        have hpt : ∀ θ ∈ Iθ, σ θ * sKer ε (θ + u - Real.pi) ≤
            (ε * sMass)⁻¹ * (σ θ *
              Set.indicator (Set.Icc (Real.pi / 2 - (ε - (Real.pi / 2 - u))) (Real.pi / 2))
                (fun _ => (1 : ℝ)) θ) := by
          intro θ hθ
          have hθ1 : θ ≤ Real.pi / 2 := (show θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) from hθ).2
          have hσ : 0 ≤ σ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
          by_cases hge : Real.pi / 2 - (ε - (Real.pi / 2 - u)) ≤ θ
          · have hind : Set.indicator (Set.Icc (Real.pi / 2 - (ε - (Real.pi / 2 - u)))
                  (Real.pi / 2)) (fun _ => (1 : ℝ)) θ = 1 :=
              Set.indicator_of_mem (by rw [Set.mem_Icc]; exact ⟨hge, hθ1⟩) _
            rw [hind, mul_one]
            calc σ θ * sKer ε (θ + u - Real.pi) ≤ σ θ * (ε * sMass)⁻¹ :=
                  mul_le_mul_of_nonneg_left (sKer_le_inv hε _) hσ
              _ = (ε * sMass)⁻¹ * σ θ := by ring
          · have hzu : θ + u - Real.pi < -ε := by linarith [not_le.mp hge]
            have hz : sKer ε (θ + u - Real.pi) = 0 := sKer_eq_zero_of_le_abs hε (by
              rw [abs_of_neg (by linarith)]; linarith)
            rw [hz, mul_zero]
            exact mul_nonneg hinv_nn
              (mul_nonneg hσ (Set.indicator_nonneg (fun _ _ => zero_le_one) θ))
        have hmono := integral_mono_ae hshift₃'
          (integrableOn_sigma_indicator_mul (c := (ε * sMass)⁻¹) hinv_nn measurableSet_Icc)
          (ae_restrict_of_forall_mem measurableSet_Icc hpt)
        rw [integral_const_mul,
          indicator_right_setIntegral (a := ε - (Real.pi / 2 - u)) hδ0.le hδπ] at hmono
        have h2η : ε ^ (-η) ≤ 2 ^ η * σ u :=
          inv_rpow_le_two_of_le hε (sigma_ge_two_eps hu0 hu2 hε (Or.inr hpu_lt))
        calc (∫ θ in Iθ, σ θ * sKer ε (θ + u - Real.pi))
            ≤ (ε * sMass)⁻¹ *
              (∫ θ in (Real.pi / 2 - (ε - (Real.pi / 2 - u)))..(Real.pi / 2), σ θ) := hmono
          _ ≤ (ε * sMass)⁻¹ * (Clayer * (ε - (Real.pi / 2 - u)) ^ (1 - η)) := by
              refine mul_le_mul_of_nonneg_left ?_ hinv_nn
              have h := integral_thEta_right_layer (a := ε - (Real.pi / 2 - u)) hδ0 hδ4
              rw [hCl]
              calc ∫ θ in (Real.pi / 2 - (ε - (Real.pi / 2 - u)))..(Real.pi / 2), σ θ
                  ≤ (Real.pi / 4) ^ η * (ε - (Real.pi / 2 - u)) ^ (1 - η) / (1 - η) := h
                _ = (Real.pi / 4) ^ η / (1 - η) * (ε - (Real.pi / 2 - u)) ^ (1 - η) := by ring
          _ ≤ Clayer * 2 ^ η * sMass⁻¹ * σ u := by
              rw [hCl]; exact window_le_two hε hδ0.le (by linarith) h2η
          _ = K₂ * σ u := by rw [← hK₂]
      · have hzero : (∫ θ in Iθ, σ θ * sKer ε (θ + u - Real.pi)) = 0 := by
          have h1 : (∫ θ in Iθ, σ θ * sKer ε (θ + u - Real.pi)) = ∫ θ in Iθ, (0 : ℝ) := by
            refine integral_congr_ae ?_
            filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
            have hθ1 : θ ≤ Real.pi / 2 := (show θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) from hθ).2
            have hzu : θ + u - Real.pi ≤ -ε := by linarith [not_lt.mp hpu_lt]
            rw [sKer_eq_zero_of_le_abs hε (by rw [abs_of_neg (by linarith)]; linarith),
              mul_zero]
          rw [h1, integral_zero]
        rw [hzero]
        exact mul_nonneg hK₂_nn hσu_nn
    -- assembly
    rw [hsplit]
    have hmax_le : max K₁ (Real.pi ^ η) ≤ K₁ + Real.pi ^ η := max_le (by linarith) (by linarith)
    have hfin : max K₁ (Real.pi ^ η) * σ u + K₂ * σ u + K₂ * σ u ≤ Kbig * σ u := by
      have h1 : max K₁ (Real.pi ^ η) * σ u ≤ (K₁ + Real.pi ^ η) * σ u :=
        mul_le_mul_of_nonneg_right hmax_le hσu_nn
      have h2 : (K₁ + Real.pi ^ η) * σ u + K₂ * σ u + K₂ * σ u
          ≤ (1 + (K₁ + Real.pi ^ η) + 2 * K₂ + K₃) * σ u := by
        nlinarith [hK₂_nn, hK₃_nn, hσu_nn]
      rw [hKbig]
      linarith
    linarith [hTmid, hTleft, hTright, hfin]

end Work.FTS.EllSol.K5cAux
