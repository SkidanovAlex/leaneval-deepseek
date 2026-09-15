import Submission.FUP.PSHToFourier6
import Submission.FUP.PSHToFourierHormander
import Submission.Commons.Analysis.Complex.analyticOnNhd_of_dbar_eq_zero
import Submission.Commons.Measure.EuclideanSpace.memLp_two_of_norm_le_exp_neg_smoothTransition_log_sq

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℂᵈ" => (Fin d → ℂ)

namespace Submission.FUP

open Commons.Analysis.Real in
/-- **Cohen's `prop:psh_to_bounded_fourier`**, reduced to Hörmander's `∂̄` theorem. -/
theorem psh_to_bounded_fourier_of_hormander_exact (hH : HormanderStatementExact (d := d)) :
    psh_to_bounded_fourier_statement (d := d) := by
  intro CLip ρ hCLip hρ
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0
    refine ⟨1, 1, 1, one_pos, one_pos, one_pos, ?_⟩
    intro u hupsh hunonpos huzero hulip hugrowth
    refine ⟨fun _ => 1, differentiable_const 1, ?_, ?_, ?_, ?_⟩
    · intro z
      have h1 : (1:ℝ) ≤ Real.exp (2 * ρ * ‖imVec z‖) := Real.one_le_exp (by positivity)
      simpa using h1
    · intro x hx; norm_num
    · intro x
      have hx2 : ‖x‖ ≤ 2 := by
        have hx0 : x = 0 := Subsingleton.elim _ _
        rw [hx0]; simp
      rw [huzero x hx2, Real.exp_zero]; norm_num
    · refine MemLp.of_bound aestronglyMeasurable_const 1 (Filter.Eventually.of_forall (fun x => ?_))
      simp
  · -- the main case `d ≥ 1`
    obtain ⟨u0, hu0psh, hu0nonpos, ⟨lam, hlam, hu0le⟩, hu0zero, hu0lip, hu0growth⟩ :=
      exists_u0 (d := d) hd
    obtain ⟨B₀, hB₀⟩ := exists_bound_fderiv_bumpC (d := d)
    set B : ℝ := max B₀ 1 with hBdef
    have hB : ∀ z : ℂᵈ, ‖fderiv ℝ (bumpC (d := d)) z‖ ≤ B :=
      fun z => le_trans (hB₀ z) (le_max_left _ _)
    have hBpos : 0 < B := by rw [hBdef]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
    obtain ⟨B1, hB1⟩ := exists_mul_log_le_mul_self_add (20 * (d : ℝ)) (ρ / 2)
      (by positivity) (by positivity)
    obtain ⟨B20, hB20⟩ := exists_log_sub_div_log_sq_bound (20 * (d : ℝ)) (ρ * lam)
      (by positivity) (by positivity)
    obtain ⟨B30, hB30⟩ := exists_log_sub_div_log_sq_bound (20 * (d : ℝ)) (ρ * lam / 2)
      (by positivity) (by positivity)
    -- the absorption constants
    have habs1 : ∀ t : ℝ, 0 ≤ t → 20 * (d : ℝ) * Real.log (1 + t) ≤ (ρ / 2) * t + B1 := hB1
    have habs2 : ∀ t : ℝ, 0 ≤ t → 20 * (d : ℝ) * Real.log (1 + t)
        - ρ * lam * (Real.smoothTransition (t / 5 - 1) * (t / (Real.log (2 + t)) ^ 2))
        ≤ max B20 (20 * (d : ℝ) * Real.log 11) := by
      intro t ht
      rcases le_or_gt t 10 with h10 | h10
      · have hχ : 0 ≤ Real.smoothTransition (t / 5 - 1) * (t / (Real.log (2 + t)) ^ 2) :=
          mul_nonneg (Real.smoothTransition.nonneg _) (div_nonneg ht (sq_nonneg _))
        have hlog : 20 * (d : ℝ) * Real.log (1 + t) ≤ 20 * (d : ℝ) * Real.log 11 := by
          have h11 : (1:ℝ) + t ≤ 11 := by linarith
          have := Real.log_le_log (by linarith) h11
          nlinarith [(Nat.cast_nonneg d : (0:ℝ) ≤ (d:ℝ))]
        have hnn : 0 ≤ ρ * lam * (Real.smoothTransition (t / 5 - 1) * (t / (Real.log (2 + t)) ^ 2)) :=
          mul_nonneg (mul_nonneg hρ.le hlam.le) hχ
        exact le_trans (by linarith : 20 * (d:ℝ) * Real.log (1+t)
          - ρ * lam * (Real.smoothTransition (t / 5 - 1) * (t / (Real.log (2 + t)) ^ 2))
          ≤ 20 * (d:ℝ) * Real.log 11) (le_max_right _ _)
      · have hχ1 : Real.smoothTransition (t / 5 - 1) = 1 :=
          Real.smoothTransition.one_of_one_le (by linarith)
        rw [hχ1, one_mul]
        exact le_trans (hB20 t ht) (le_max_left _ _)
    -- the exponent bound of the `L²`-weighted estimate
    have habs3 : ∀ t : ℝ, 0 ≤ t → 10 * (d : ℝ) * Real.log (1 + t)
        - (1 / 4) * ρ * lam * (Real.smoothTransition (t / 5 - 1) * (t / (Real.log (2 + t)) ^ 2))
        ≤ max (B30 / 2) (10 * (d : ℝ) * Real.log 11) := by
      intro t ht
      rcases le_or_gt t 10 with h10 | h10
      · have hχ : 0 ≤ Real.smoothTransition (t / 5 - 1) * (t / (Real.log (2 + t)) ^ 2) :=
          mul_nonneg (Real.smoothTransition.nonneg _) (div_nonneg ht (sq_nonneg _))
        have hlog : 10 * (d : ℝ) * Real.log (1 + t) ≤ 10 * (d : ℝ) * Real.log 11 := by
          have h11 : (1:ℝ) + t ≤ 11 := by linarith
          have := Real.log_le_log (by linarith) h11
          nlinarith [(Nat.cast_nonneg d : (0:ℝ) ≤ (d:ℝ))]
        have hnn : 0 ≤ (1/4) * ρ * lam * (Real.smoothTransition (t / 5 - 1)
            * (t / (Real.log (2 + t)) ^ 2)) :=
          mul_nonneg (by positivity) hχ
        exact le_trans (by linarith) (le_max_right _ _)
      · have hχ1 : Real.smoothTransition (t / 5 - 1) = 1 :=
          Real.smoothTransition.one_of_one_le (by linarith)
        rw [hχ1, one_mul]
        have h := hB30 t ht
        have : 10 * (d : ℝ) * Real.log (1 + t)
            - (1 / 4) * ρ * lam * (t / (Real.log (2 + t)) ^ 2) ≤ B30 / 2 := by
          linarith [div_le_div_of_nonneg_right h (by norm_num : (0:ℝ) ≤ 2)]
        exact le_trans this (le_max_left _ _)
    · -- the constants
      set Kg : ℝ := hormanderConst d CLip ρ B * Real.pi ^ d with hKg
      set KF : ℝ := 2 * Real.exp (Bann d CLip ρ) * Real.pi ^ d + 2 * Kg with hKF
      set A1 : ℝ := Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
        * Real.exp (ρ / 4 + (B1 + max B20 (20 * (d : ℝ) * Real.log 11)) / 2) with hA1
      set A2 : ℝ := 1 + Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹
        * Real.exp (Bsmall ρ CLip d) * Kg) with hA2
      set rmin : ℝ := min (1 / 8) (1 / (8 * Kc ρ d Kg * Real.exp (Cc ρ d / 2) + 1)) with hrmin
      set Ccst : ℝ := max (A2 * Real.exp (CLip * Real.sqrt d / 4))
        (Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
          * Real.exp ((max B20 (20 * (d : ℝ) * Real.log 11) + Bsmall2 ρ CLip d) / 2)) with hC
      set Cbig : ℝ := Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF)
        * Real.exp (Bsmall2 ρ CLip d / 2 + max (B30 / 2) (10 * (d : ℝ) * Real.log 11)) with hCbig
      have hKgpos : 0 < Kg := by
        rw [hKg, hormanderConst]
        have h1 : (0:ℝ) < (d : ℝ) * B ^ 2 * (8 * (Real.sqrt (1 + (d : ℝ))) ^ 3 / ρ) := by
          have hd0 : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
          have h2 : (0:ℝ) < 8 * (Real.sqrt (1 + (d : ℝ))) ^ 3 / ρ := by positivity
          have h3 : (0:ℝ) < B ^ 2 := by positivity
          exact mul_pos (mul_pos hd0 h3) h2
        exact mul_pos (mul_pos h1 (Real.exp_pos _))
          (pow_pos Real.pi_pos d)
      have hKcpos : 0 < Kc ρ d Kg := by
        rw [Kc]
        have h4d : (0:ℝ) < 4 * (d : ℝ) / Real.pi := by positivity
        exact mul_pos (mul_pos (pow_pos h4d d) (Real.exp_pos _)) hKgpos
      have hKFpos : 0 < KF := by
        rw [hKF]
        have : 0 < 2 * Real.exp (Bann d CLip ρ) * Real.pi ^ d := by positivity
        linarith
      have hA2pos : 0 < A2 := by
        rw [hA2]
        have : 0 ≤ Real.sqrt (((Real.pi * rr d ^ 2) ^ d)⁻¹ * Real.exp (Bsmall ρ CLip d) * Kg) :=
          Real.sqrt_nonneg _
        linarith
      have hA1pos : 0 < A1 := by
        rw [hA1]
        have hchain : 0 < ((Real.pi * rr d ^ 2) ^ d)⁻¹ * KF := by
          have hrp : 0 < rr d := rr_pos hd
          have h1 : 0 < (Real.pi * rr d ^ 2) ^ d := by positivity
          exact mul_pos (inv_pos.mpr h1) hKFpos
        exact mul_pos (Real.sqrt_pos.mpr hchain) (Real.exp_pos _)
      have hCpos : 0 < Ccst := by
        rw [hC]
        exact lt_of_lt_of_le (mul_pos hA2pos (Real.exp_pos _)) (le_max_left _ _)
      have hrminpos : 0 < rmin := by
        rw [hrmin]
        refine lt_min (by norm_num) ?_
        apply one_div_pos.mpr
        have h1 : 0 < 8 * Kc ρ d Kg * Real.exp (Cc ρ d / 2) :=
          mul_pos (mul_pos (by norm_num) hKcpos) (Real.exp_pos _)
        linarith
      refine ⟨rmin, max A1 A2, Ccst, hrminpos, ?_, hCpos, ?_⟩
      · rw [hA1, hA2]
        exact lt_of_lt_of_le (by linarith [hA1pos]) (le_max_left _ _)
      · intro u hupsh hunonpos huzero hulip hugrowth
        obtain ⟨F, g, hFdiff, hFeq, hgsm, hgpart, hgL2⟩ :=
          exists_F_of_hormander_exact (d := d) hH hd hCLip.le hρ hupsh hu0psh huzero hulip hugrowth
            hu0zero hu0lip hu0growth
        -- analyticity
        have hFana : AnalyticOnNhd ℂ F Set.univ := by
          refine Commons.Analysis.Complex.analyticOnNhd_of_dbar_eq_zero (d := d) isOpen_univ ?_ ?_
          · exact (Differentiable.restrictScalars ℝ hFdiff).differentiableOn
          · intro j z _
            have h1 : partialZbar j F z = 0 := by
              rw [show F = fun z => bumpC (d := d) z - g z from funext hFeq,
                partialZbar_sub j ((contDiff_bumpC (d := d)).differentiable (by norm_num) z)
                  ((hgsm.differentiable (by simp)) z)]
              have hz := congrFun (hgpart j) z
              simp only [dbarFun] at hz
              rw [hz, sub_self]
            have h2 : partialZbar j F z
                = (fderiv ℝ F z (Pi.single j 1)
                    + Complex.I * fderiv ℝ F z (Pi.single j Complex.I)) / 2 := rfl
            rw [h2] at h1
            rcases div_eq_zero_iff.mp h1 with h | h
            · exact h
            · norm_num at h
        have hgana : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂᵈ) (1 / 2)) := by
          refine Commons.Analysis.Complex.analyticOnNhd_of_dbar_eq_zero (d := d) isOpen_ball ?_ ?_
          · exact (hgsm.differentiable (by simp)).differentiableOn
          · intro j z hz
            have hz' : ‖z‖ < 1 / 2 := by
              simpa [Metric.mem_ball, dist_zero_right] using hz
            have h0 := dbarFun_bumpC_eq_zero_of_lt_half (d := d) hz'
            have hz2 := congrFun (hgpart j) z
            have h1 : partialZbar j g z = 0 := by rw [hz2, h0, Pi.zero_apply]
            have h2 : partialZbar j g z
                = (fderiv ℝ g z (Pi.single j 1)
                    + Complex.I * fderiv ℝ g z (Pi.single j Complex.I)) / 2 := rfl
            rw [h2] at h1
            rcases div_eq_zero_iff.mp h1 with h | h
            · exact h
            · norm_num at h
        -- the weighted L² bounds
        have hvol1 : volume (Metric.closedBall (0 : ℂᵈ) 1) = ENNReal.ofReal (Real.pi ^ d) := by
          have h := Commons.Analysis.Complex.polydisc_volume (0 : ℂᵈ) (by norm_num : (0:ℝ) < 1)
          rw [one_pow, mul_one] at h
          have hlt : volume (Metric.closedBall (0 : ℂᵈ) 1) ≠ ⊤ :=
            ne_of_lt (isCompact_closedBall (0 : ℂᵈ) 1).measure_lt_top
          rw [← ENNReal.ofReal_toReal hlt, h]
        have hMg : ∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))
            ≤ ENNReal.ofReal Kg := by
          have hη := lintegral_hormanderTest_le (d := d) hd hCLip.le hρ hB huzero hulip
            (fun z => (hugrowth z).1) hu0zero hu0lip (fun z => (hu0growth z).1)
          refine le_trans hgL2 (le_trans hη ?_)
          rw [hKg, hvol1, ← ENNReal.ofReal_mul (by rw [hormanderConst]; positivity)]
        have hMF : ∫⁻ z in U5, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(section5Phi ρ u u0 z)))
            ≤ ENNReal.ofReal KF := by
          have h := lintegral_F_U5_le (d := d) (L := ENNReal.ofReal Kg) hCLip.le hρ huzero hulip
            (fun z => (hugrowth z).1) hu0zero hu0lip (fun z => (hu0growth z).1) (fun z => hFeq z) hMg
          refine le_trans h ?_
          have hvol2 : volume (U5 ∩ Metric.closedBall (0 : ℂᵈ) 1) ≤ ENNReal.ofReal (Real.pi ^ d) := by
            rw [← hvol1]
            exact measure_mono (Set.inter_subset_right)
          have hvol2 : volume (U5 ∩ Metric.closedBall (0 : ℂᵈ) 1) ≤ ENNReal.ofReal (Real.pi ^ d) := by
            rw [← hvol1]
            exact measure_mono Set.inter_subset_right
          have key : (2:ℝ≥0∞) * (ENNReal.ofReal (Real.exp (Bann d CLip ρ))
                * volume (U5 ∩ Metric.closedBall (0 : ℂᵈ) 1)) + 2 * ENNReal.ofReal Kg
              ≤ ENNReal.ofReal KF := by
            have h1 : ENNReal.ofReal (Real.exp (Bann d CLip ρ))
                * volume (U5 ∩ Metric.closedBall (0 : ℂᵈ) 1)
                ≤ ENNReal.ofReal (Real.exp (Bann d CLip ρ) * Real.pi ^ d) := by
              refine le_trans (mul_le_mul_of_nonneg_left hvol2 bot_le) (le_of_eq ?_)
              rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
            have h2 : (2:ℝ≥0∞) * (ENNReal.ofReal (Real.exp (Bann d CLip ρ))
                  * volume (U5 ∩ Metric.closedBall (0 : ℂᵈ) 1))
                ≤ ENNReal.ofReal (2 * Real.exp (Bann d CLip ρ) * Real.pi ^ d) := by
              refine le_trans (mul_le_mul_of_nonneg_left h1 bot_le) (le_of_eq ?_)
              rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
              congr 1
              ring
            have h3 : 2 * ENNReal.ofReal Kg ≤ ENNReal.ofReal (2 * Kg) := by
              rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
            rw [hKF, ENNReal.ofReal_add (by positivity) (by positivity)]
            exact add_le_add h2 h3
          exact key
        -- the bounds on `F`
        have hbounds := norm_F_bounds (d := d) (ρ := ρ) (CLip := CLip) (lam := lam) (B1 := B1)
          (B2 := max B20 (20 * (d : ℝ) * Real.log 11)) (KF := KF) (Kg := Kg)
          (u := u) (u0 := u0) (F := F) (g := g) hd hρ hlam hCLip hunonpos huzero hulip hugrowth
          hu0nonpos hu0lip hu0growth hu0le habs1 habs2 hFana hgana (fun z => hFeq z) hMF hKFpos
          hMg hKgpos
        -- the auxiliary arithmetic for the lower bound
        have hCcpos : 0 < Cc ρ d := by
          rw [Cc]
          have hs : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
          positivity
        have hKr : Kc ρ d Kg * Real.exp (Cc ρ d / 2) * rmin ≤ 1 / 8 := by
          have hrm : rmin ≤ 1 / (8 * Kc ρ d Kg * Real.exp (Cc ρ d / 2) + 1) := by
            rw [hrmin]; exact min_le_right _ _
          have hKe : 0 ≤ Kc ρ d Kg * Real.exp (Cc ρ d / 2) :=
            mul_nonneg hKcpos.le (Real.exp_pos _).le
          have h4 : Kc ρ d Kg * Real.exp (Cc ρ d / 2) * rmin
              ≤ Kc ρ d Kg * Real.exp (Cc ρ d / 2)
                * (1 / (8 * Kc ρ d Kg * Real.exp (Cc ρ d / 2) + 1)) :=
            mul_le_mul_of_nonneg_left hrm hKe
          refine le_trans h4 ?_
          rw [mul_one_div,
            div_le_iff₀ (by linarith : (0 : ℝ) < 8 * Kc ρ d Kg * Real.exp (Cc ρ d / 2) + 1)]
          nlinarith [hKe]
        -- estimate (ii): the lower bound on `B(0,rmin)`
        have hpunct : ∀ x : ℝᵈ, 0 < ‖x‖ → ‖x‖ ≤ rmin → (1 / 2 : ℝ) ≤ ‖F (toCpx x)‖ := by
          intro x hx0 hxr
          have hy14 : ‖x‖ ≤ 1 / 4 := by
            have h1 : rmin ≤ 1 / 8 := by rw [hrmin]; exact min_le_left _ _
            linarith
          have hg : ‖g (toCpx x)‖ ≤ 1 / 2 := by
            have h1 := norm_g_sq_le_pow (d := d) (CLip := CLip) hρ hKgpos hd hunonpos hugrowth
              hu0nonpos hu0growth hgana hMg hx0 hy14
            have hr1 : ‖x‖ ≤ 1 := by linarith
            have hr2 : ‖x‖ ≤ 1 / 2 := by linarith
            have hpow : ‖x‖ ^ (18 * d) ≤ ‖x‖ := by
              have := pow_le_pow_of_le_one (norm_nonneg x) hr1 (by omega : 1 ≤ 18 * d)
              simpa using this
            have hexp : Real.exp (Cc ρ d * ‖x‖) ≤ Real.exp (Cc ρ d / 2) := by
              refine Real.exp_le_exp.mpr ?_
              nlinarith [hCcpos]
            have h2 : Kc ρ d Kg * ‖x‖ ^ (18 * d) * Real.exp (Cc ρ d * ‖x‖)
                ≤ Kc ρ d Kg * Real.exp (Cc ρ d / 2) * rmin := by
              have ha : Kc ρ d Kg * ‖x‖ ^ (18 * d) * Real.exp (Cc ρ d * ‖x‖)
                  ≤ Kc ρ d Kg * ‖x‖ * Real.exp (Cc ρ d / 2) := by
                calc Kc ρ d Kg * ‖x‖ ^ (18 * d) * Real.exp (Cc ρ d * ‖x‖)
                    = Kc ρ d Kg * ‖x‖ ^ (18 * d) * Real.exp (Cc ρ d * ‖x‖) := rfl
                  _ ≤ Kc ρ d Kg * ‖x‖ * Real.exp (Cc ρ d / 2) := by
                      refine mul_le_mul (mul_le_mul_of_nonneg_left hpow hKcpos.le) hexp
                        (Real.exp_pos _).le (by positivity)
                  _ = Kc ρ d Kg * ‖x‖ * Real.exp (Cc ρ d / 2) := rfl
              have hb : Kc ρ d Kg * ‖x‖ * Real.exp (Cc ρ d / 2)
                  ≤ Kc ρ d Kg * rmin * Real.exp (Cc ρ d / 2) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxr hKcpos.le)
                  (Real.exp_pos _).le
              linarith [ha, hb, hKr]
            have h3 : ‖g (toCpx x)‖ ^ 2 ≤ 1 / 4 := by linarith [h1, h2]
            nlinarith [norm_nonneg (g (toCpx x))]
          have hbump : bumpC (d := d) (toCpx x) = 1 :=
            bumpC_eq_one (le_trans (norm_toCpx_le x) (by linarith))
          rw [hFeq (toCpx x), hbump]
          have h2 : (1 : ℝ) - ‖g (toCpx x)‖ ≤ ‖(1 : ℂ) - g (toCpx x)‖ := by
            have h3 := abs_norm_sub_norm_le (1 : ℂ) (g (toCpx x))
            rw [norm_one] at h3
            linarith [le_abs_self ((1 : ℝ) - ‖g (toCpx x)‖)]
          linarith
        have hlow : ∀ x : ℝᵈ, ‖x‖ ≤ rmin → (1 / 2 : ℝ) ≤ ‖F (toCpx x)‖ := by
          intro x hx
          rcases eq_or_lt_of_le (norm_nonneg x) with h0 | h0
          · have hx0 : x = 0 := norm_eq_zero.mp h0.symm
            subst hx0
            have h0c : toCpx (0 : ℝᵈ) = 0 := by funext i; simp [toCpx]
            rw [h0c]
            exact le_norm_of_forall_near_zero (d := d) hd hFdiff.continuous.continuousAt
              hrminpos (fun y hy hyr => hpunct y hy hyr)
          · exact hpunct x h0 hx
        -- the decay estimate and the `L²` bound
        set D : ℝ := max (A2 * Real.exp ((ρ * lam / 4) * (5 + Real.sqrt d))) Cbig with hD
        have hDpos : 0 < D := by
          rw [hD]
          exact lt_of_lt_of_le (mul_pos hA2pos (Real.exp_pos _)) (le_max_left _ _)
        have hdecay : ∀ x : ℝᵈ, ‖F (toCpx x)‖ ≤ D * Real.exp (-((ρ * lam / 4) *
            (Real.smoothTransition (‖x‖ / 5 - 1) * (‖x‖ / (Real.log (2 + ‖x‖)) ^ 2)))) := by
          refine norm_F_decay (d := d) (D := D) hd hρ hlam hCLip.le ?_ ?_ hunonpos hulip hugrowth
            hu0nonpos hu0lip hu0growth hu0le habs3 hFana hgana (fun z => hFeq z) hMF hKFpos hMg
            hKgpos
          · rw [hD, ← hA2]
            exact le_max_left _ _
          · rw [hD, ← hCbig]
            exact le_max_right _ _
        have hmemLp : MemLp (fun x : ℝᵈ => F (toCpx x)) 2 (volume : Measure ℝᵈ) :=
          Commons.Measure.EuclideanSpace.memLp_two_of_norm_le_exp_neg_smoothTransition_log_sq
            d hDpos.le (by positivity : 0 < ρ * lam / 4)
            (hFdiff.continuous.comp continuous_toCpx).aestronglyMeasurable hdecay
        refine ⟨F, hFdiff, ?_, hlow, ?_, hmemLp⟩
        · intro z
          rw [hA1, hA2]
          exact hbounds.1 z
        · intro x
          rw [hC, hA2]
          exact hbounds.2 x

end Submission.FUP
