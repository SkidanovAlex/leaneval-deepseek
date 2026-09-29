import Mathlib
import Submission.Work.Cert.Spec
import Submission.Work.Cert.ball_ops
import Submission.Work.Cert.ACSlit.Shadow
import Submission.Work.Cert.ACSlit.ballMem_sQ_Qp
import Submission.Work.Cert.ACSlit.ballMem_su_fp
import Submission.Work.Cert.ACSlit.slitStage_M2c_sound
import Submission.Work.Cert.ACSlit.slitStage_M2e_sound
import Submission.Work.APsi.slit_facts
import Submission.Work.ANum3.taylor_disc_le
import Submission.Work.ANum2.slit_second_deriv_bound


/-!
# `SlitStageSound` (v3): soundness of one rotated slit stage of the Theorem-A arc certificate.

`Work.Cert.slitStage` evaluates the stage value `f(c) = rot t · slit r c` and the derivative
`f'(c)` by rigorous ball arithmetic at the centre `c`, and outputs the disc
`D(u, |f'(c)|ρ + M₂ρ²/2 + rad f(c))` with `M₂ = min(M2e, M2c)` bounding `sup_D ‖f''‖`.
This file assembles the soundness theorem from
* `ACSlit.Shadow` (named pieces of the checker, the bridge `slitStage_eq`, `slitStage_ok_spec`),
* `ACSlit.ballMem_sQ_Qp`, `ACSlit.ballMem_su_fp` (ball semantics of the chain),
* `ACSlit.slitStage_M2c_sound` (Cauchy branch) and `ACSlit.slitStage_M2e_sound` (explicit branch),
* `ball_ops` (soundness of `badd/bsub/bmul/binv/bsqrt`),
* `Work.ANum3.taylor_disc_le` (second-order Taylor estimate on a disc).
-/
namespace Work.Cert
open Complex Submission.CDTPlan
open Work.Cert.ACSlit
open Work.Cert.ACBall

theorem sokB_conj (A B2 E C1 G8 A2 ror roi : ℤ) (st : St) (w : SlitW)
    (h : sokB A B2 E C1 G8 A2 ror roi st w = true) :
    bsqrtOK (sQ A B2 E C1 G8 A2 ror roi st w) w.sr = true ∧
      binvOK (sden A B2 E C1 G8 A2 ror roi st w) w.L1 = true ∧
      binvOK (ss A B2 E C1 G8 A2 ror roi st w) w.Ls = true ∧
      binvOK (sC A B2 E C1 G8 A2 ror roi st w) w.cL = true := by
  have h' := h
  simp only [sokB, Bool.and_eq_true] at h'
  exact ⟨h'.1.1.1, h'.1.1.2, h'.1.2, h'.2⟩

set_option maxHeartbeats 1000000 in
theorem slitStage_sound3 : SlitStageSound := by
  intro r t A B2 E C1 G8 A2 ror roi st w hr0 hr1 hA hB2 hE hC1 hG8 hA2 hrot hok z hz
  obtain ⟨hstok, hokB, hokM, hokW, hwhi, hM2INF, hrho, hrho2nn⟩ :=
    slitStage_ok_spec A B2 E C1 G8 A2 ror roi st w hok
  rw [slitStage_cr, slitStage_ci, slitStage_rho]
  set ρ : ℝ := (st.rho : ℝ) / (S : ℝ) with hρdef
  -- ## unpacking the flags
  have hokM' := hokM
  simp only [sokM, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hokM'
  obtain ⟨hD0, hfpsq, hcU0, hcUsq, hqU0, hqUsq, hqL0, hqLsq, hqpU0, hqpUsq, hm1U0, hm1Usq⟩ := hokM'
  have hokB' : binvOK (sC A B2 E C1 G8 A2 ror roi st w) w.cL = true :=
    (sokB_conj A B2 E C1 G8 A2 ror roi st w hokB).2.2.2
  -- ## real-valued facts
  have hcU : ‖ACSlit.cIn st‖ ≤ (w.cU : ℝ) / (S : ℝ) :=
    norm_cx_le_of_sq_le st.cr st.ci w.cU hcU0 hcUsq
  have hρnn : 0 ≤ ρ := by
    rw [hρdef]; exact div_nonneg (by exact_mod_cast hrho) S_posR.le
  have hsum_lt : ‖ACSlit.cIn st‖ + (st.rho : ℝ) / (S : ℝ) < 1 := by
    have h1 : (w.cU : ℝ) / (S : ℝ) + (st.rho : ℝ) / (S : ℝ) < 1 := by
      rw [← add_div, div_lt_one S_posR]
      exact_mod_cast (by have h := hwhi; simp only [swhi] at h; omega : w.cU + st.rho < S)
    linarith
  have hclt : ‖ACSlit.cIn st‖ < 1 := by linarith
  have hdisc : ‖ACSlit.cIn st‖ + ρ < 1 := by rw [hρdef]; linarith
  have hc0 : ACSlit.cIn st ≠ 0 := by
    have hmem : BallMem (sC A B2 E C1 G8 A2 ror roi st w) (ACSlit.cIn st) := by
      rw [BallMem]; simp [sC, ACSlit.cIn]
    exact (ball_ops.2.1 (sC A B2 E C1 G8 A2 ror roi st w) w.cL (ACSlit.cIn st) hokB' hmem).1
  -- ## the ball chain
  obtain ⟨hQmem, hQpmem⟩ := ballMem_sQ_Qp A B2 E C1 G8 A2 ror roi st w hA hB2 hA2
  obtain ⟨hsu, hsfp⟩ :=
    ballMem_su_fp A B2 E C1 G8 A2 ror roi st w hr0 hr1 hA hB2 hE hC1 hG8 hA2 hrot hokB hc0 hclt
  -- ## the derivative bound at the centre
  have hDnn : (0 : ℝ) ≤ (w.D : ℝ) := by exact_mod_cast hD0
  have hfpr : (0 : ℝ) ≤ ((sfp A B2 E C1 G8 A2 ror roi st w).r : ℝ) := by
    exact_mod_cast nonneg_radius hsfp
  have hfpC : ‖cx (sfp A B2 E C1 G8 A2 ror roi st w).x (sfp A B2 E C1 G8 A2 ror roi st w).y‖
      ≤ (w.D : ℝ) / (S : ℝ) :=
    norm_cx_le_of_sq_le _ _ _ hD0 hfpsq
  have hderiv : ‖deriv (slit r) (ACSlit.cIn st)‖
      ≤ (((w.D + (sfp A B2 E C1 G8 A2 ror roi st w).r : ℤ)) : ℝ) / (S : ℝ) := by
    have hg : ‖deriv (slit r) (ACSlit.cIn st)‖ = ‖rot t * deriv (slit r) (ACSlit.cIn st)‖ := by
      rw [norm_mul, Work.APsi.norm_rot, one_mul]
    rw [hg]
    have hsplit : (rot t * deriv (slit r) (ACSlit.cIn st))
        = (rot t * deriv (slit r) (ACSlit.cIn st)
            - cx (sfp A B2 E C1 G8 A2 ror roi st w).x (sfp A B2 E C1 G8 A2 ror roi st w).y)
          + cx (sfp A B2 E C1 G8 A2 ror roi st w).x (sfp A B2 E C1 G8 A2 ror roi st w).y := by ring
    calc ‖rot t * deriv (slit r) (ACSlit.cIn st)‖
        ≤ ‖rot t * deriv (slit r) (ACSlit.cIn st)
            - cx (sfp A B2 E C1 G8 A2 ror roi st w).x (sfp A B2 E C1 G8 A2 ror roi st w).y‖
          + ‖cx (sfp A B2 E C1 G8 A2 ror roi st w).x (sfp A B2 E C1 G8 A2 ror roi st w).y‖ := by
          conv_lhs => rw [hsplit]
          exact norm_add_le _ _
      _ ≤ ((sfp A B2 E C1 G8 A2 ror roi st w).r : ℝ) / (S : ℝ) + (w.D : ℝ) / (S : ℝ) :=
          add_le_add hsfp hfpC
      _ = (((w.D + (sfp A B2 E C1 G8 A2 ror roi st w).r : ℤ)) : ℝ) / (S : ℝ) := by
          push_cast; ring
  -- ## the second-derivative bound
  have hM2bound : ∀ u : ℂ, ‖u - ACSlit.cIn st‖ ≤ ρ →
      ‖deriv (deriv (slit r)) u‖ ≤ ((sM2 A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) / (S : ℝ) := by
    intro u hu
    by_cases h : sM2e A B2 E C1 G8 A2 ror roi st w ≤ sM2c A B2 E C1 G8 A2 ror roi st w
    · have hM2eq : sM2 A B2 E C1 G8 A2 ror roi st w = sM2e A B2 E C1 G8 A2 ror roi st w := by
        show imin (sM2e A B2 E C1 G8 A2 ror roi st w) (sM2c A B2 E C1 G8 A2 ror roi st w) = _
        simp only [imin]; rw [if_pos h]
      have hM2e_lt : sM2e A B2 E C1 G8 A2 ror roi st w < INF := by
        rw [hM2eq] at hM2INF; exact hM2INF
      by_cases hcond : (suseE A B2 E C1 G8 A2 ror roi st w
          && decide (0 < sdd A B2 E C1 G8 A2 ror roi st w)) = true
      · rw [Bool.and_eq_true] at hcond
        obtain ⟨huse, hdd'⟩ := hcond
        have hdd : 0 < sdd A B2 E C1 G8 A2 ror roi st w := by simpa using hdd'
        have hchild := slitStage_M2e_sound A B2 E C1 G8 A2 ror roi st w hr0 hr1 hA hB2 hE hC1 hG8 hA2
          hokB hokM hokW hwhi hrho huse hdd hQmem hQpmem hu
        rw [hM2eq]; exact hchild
      · exfalso
        have hM2e_def : sM2e A B2 E C1 G8 A2 ror roi st w = INF := by
          simp only [sM2e]; rw [if_neg hcond]
        rw [hM2e_def] at hM2e_lt
        exact absurd hM2e_lt (lt_irrefl INF)
    · have hM2eq : sM2 A B2 E C1 G8 A2 ror roi st w = sM2c A B2 E C1 G8 A2 ror roi st w := by
        show imin (sM2e A B2 E C1 G8 A2 ror roi st w) (sM2c A B2 E C1 G8 A2 ror roi st w) = _
        simp only [imin]; rw [if_neg h]
      have hM2c_lt : sM2c A B2 E C1 G8 A2 ror roi st w < INF := by
        rw [hM2eq] at hM2INF; exact hM2INF
      by_cases hcond : (decide (0 < sd A B2 E C1 G8 A2 ror roi st w)
          && decide (0 < sdsq A B2 E C1 G8 A2 ror roi st w)) = true
      · rw [Bool.and_eq_true] at hcond
        obtain ⟨hd', hdsq'⟩ := hcond
        have hd : 0 < sd A B2 E C1 G8 A2 ror roi st w := by simpa using hd'
        have hdsq : 0 < sdsq A B2 E C1 G8 A2 ror roi st w := by simpa using hdsq'
        have hchild := slitStage_M2c_sound A B2 E C1 G8 A2 ror roi st w hr0 hr1 hokM hwhi hrho
          hd hdsq hu
        rw [hM2eq]; exact hchild
      · exfalso
        have hM2c_def : sM2c A B2 E C1 G8 A2 ror roi st w = INF := by
          simp only [sM2c]; rw [if_neg hcond]
        rw [hM2c_def] at hM2c_lt
        exact absurd hM2c_lt (lt_irrefl INF)
  -- ## Taylor
  have hCnn : (0 : ℝ) ≤ ((sM2 A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) / (S : ℝ) :=
    le_trans (norm_nonneg _)
      (hM2bound (ACSlit.cIn st) (by simp only [sub_self, norm_zero]; exact hρnn))
  have hMnn : (0 : ℝ) ≤ (((w.D + (sfp A B2 E C1 G8 A2 ror roi st w).r : ℤ)) : ℝ) / (S : ℝ) := by
    have he : (((w.D + (sfp A B2 E C1 G8 A2 ror roi st w).r : ℤ)) : ℝ)
        = (w.D : ℝ) + ((sfp A B2 E C1 G8 A2 ror roi st w).r : ℝ) := by push_cast; ring
    rw [he, add_div]
    exact add_nonneg (div_nonneg hDnn S_posR.le) (div_nonneg hfpr S_posR.le)
  have hf : ∀ u : ℂ, ‖u - ACSlit.cIn st‖ ≤ ρ → DifferentiableAt ℂ (slit r) u := by
    intro u hu
    have hu1 : ‖u‖ < 1 := by
      have h1 : ‖u‖ ≤ ‖u - ACSlit.cIn st‖ + ‖ACSlit.cIn st‖ := by
        calc ‖u‖ = ‖(u - ACSlit.cIn st) + ACSlit.cIn st‖ := by ring_nf
          _ ≤ ‖u - ACSlit.cIn st‖ + ‖ACSlit.cIn st‖ := norm_add_le _ _
      linarith [hu, hdisc]
    exact (Work.APsi.differentiableOn_slit r hr0 hr1).differentiableAt
      (Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; exact hu1))
  have hf' : ∀ u : ℂ, ‖u - ACSlit.cIn st‖ ≤ ρ → DifferentiableAt ℂ (deriv (slit r)) u := by
    intro u hu
    have hu1 : ‖u‖ < 1 := by
      have h1 : ‖u‖ ≤ ‖u - ACSlit.cIn st‖ + ‖ACSlit.cIn st‖ := by
        calc ‖u‖ = ‖(u - ACSlit.cIn st) + ACSlit.cIn st‖ := by ring_nf
          _ ≤ ‖u - ACSlit.cIn st‖ + ‖ACSlit.cIn st‖ := norm_add_le _ _
      linarith [hu, hdisc]
    exact ((Work.APsi.differentiableOn_slit r hr0 hr1).deriv Metric.isOpen_ball).differentiableAt
      (Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; exact hu1))
  have hTaylor := Work.ANum3.taylor_disc_le (f := slit r) (c := ACSlit.cIn st) (ρ := ρ)
    (M := (((w.D + (sfp A B2 E C1 G8 A2 ror roi st w).r : ℤ)) : ℝ) / (S : ℝ))
    (C := ((sM2 A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) / (S : ℝ))
    hρnn hMnn hCnn hf hf' hderiv hM2bound
  have hz' : ‖z - ACSlit.cIn st‖ ≤ ρ := by rw [hρdef]; exact hz
  have hT := hTaylor z hz'
  -- ## the final estimate
  have htri : ‖rot t * slit r z - cx (su A B2 E C1 G8 A2 ror roi st w).x
        (su A B2 E C1 G8 A2 ror roi st w).y‖
      ≤ ‖slit r z - slit r (ACSlit.cIn st)‖
        + ‖rot t * slit r (ACSlit.cIn st) - cx (su A B2 E C1 G8 A2 ror roi st w).x
            (su A B2 E C1 G8 A2 ror roi st w).y‖ := by
    have he : rot t * slit r z - cx (su A B2 E C1 G8 A2 ror roi st w).x
          (su A B2 E C1 G8 A2 ror roi st w).y
        = rot t * (slit r z - slit r (ACSlit.cIn st))
          + (rot t * slit r (ACSlit.cIn st) - cx (su A B2 E C1 G8 A2 ror roi st w).x
              (su A B2 E C1 G8 A2 ror roi st w).y) := by ring
    rw [he]
    calc ‖rot t * (slit r z - slit r (ACSlit.cIn st))
          + (rot t * slit r (ACSlit.cIn st) - cx (su A B2 E C1 G8 A2 ror roi st w).x
              (su A B2 E C1 G8 A2 ror roi st w).y)‖
        ≤ ‖rot t * (slit r z - slit r (ACSlit.cIn st))‖
          + ‖rot t * slit r (ACSlit.cIn st) - cx (su A B2 E C1 G8 A2 ror roi st w).x
              (su A B2 E C1 G8 A2 ror roi st w).y‖ := norm_add_le _ _
      _ = ‖slit r z - slit r (ACSlit.cIn st)‖
          + ‖rot t * slit r (ACSlit.cIn st) - cx (su A B2 E C1 G8 A2 ror roi st w).x
              (su A B2 E C1 G8 A2 ror roi st w).y‖ := by
          rw [norm_mul, Work.APsi.norm_rot, one_mul]
  have hnum : ((((w.D + (sfp A B2 E C1 G8 A2 ror roi st w).r : ℤ)) : ℝ) / (S : ℝ)) * ρ
      + ((((sM2 A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (S : ℝ)) * ρ ^ 2 / 2
      + (((su A B2 E C1 G8 A2 ror roi st w).r : ℤ) : ℝ) / (S : ℝ)
      ≤ (((srho2 A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (S : ℝ) := by
    rw [le_div_iff₀ S_posR]
    have hS := S_posR
    have hM2nn : (0 : ℝ) ≤ ((sM2 A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) := by
      have h := (le_div_iff₀ hS).mp hCnn
      simpa using h
    have hX : (((((w.D + (sfp A B2 E C1 G8 A2 ror roi st w).r : ℤ)) : ℝ) / (S : ℝ)) * ρ
        + ((((sM2 A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (S : ℝ)) * ρ ^ 2 / 2
        + (((su A B2 E C1 G8 A2 ror roi st w).r : ℤ) : ℝ) / (S : ℝ)) * (S : ℝ)
        = ((st.rho : ℤ) : ℝ) * (((w.D + (sfp A B2 E C1 G8 A2 ror roi st w).r : ℤ)) : ℝ) / (S : ℝ)
          + (((sM2 A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) * ((st.rho : ℤ) : ℝ) ^ 2
              / (2 * (S : ℝ) ^ 2)
          + (((su A B2 E C1 G8 A2 ror roi st w).r : ℤ) : ℝ) := by
      rw [hρdef]; field_simp
    rw [hX, srho2]
    push_cast
    have h1 := mu_ge st.rho (w.D + (sfp A B2 E C1 G8 A2 ror roi st w).r)
    push_cast at h1
    have h2 : ((sM2 A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) * ((st.rho : ℤ) : ℝ) ^ 2
          / (2 * (S : ℝ) ^ 2)
        ≤ ((chalf (mu (mu st.rho st.rho) (sM2 A B2 E C1 G8 A2 ror roi st w)) : ℤ) : ℝ) := by
      have h22 := mu_ge st.rho st.rho
      have h23 := mu_ge (mu st.rho st.rho) (sM2 A B2 E C1 G8 A2 ror roi st w)
      have hch := chalf_ge (mu (mu st.rho st.rho) (sM2 A B2 E C1 G8 A2 ror roi st w))
      have hr2 : (0 : ℝ) ≤ ((st.rho : ℤ) : ℝ) := by exact_mod_cast hrho
      have hstep1 : ((sM2 A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) * ((st.rho : ℤ) : ℝ) ^ 2
            / (2 * (S : ℝ) ^ 2)
          = (((sM2 A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) / (S : ℝ))
              * ((((st.rho : ℤ) : ℝ) ^ 2) / (S : ℝ)) / 2 := by
        field_simp
      rw [hstep1]
      have hstep2 : ((st.rho : ℤ) : ℝ) ^ 2 / (S : ℝ) ≤ ((mu st.rho st.rho : ℤ) : ℝ) := by
        have he : ((st.rho : ℤ) : ℝ) ^ 2 / (S : ℝ)
            = ((st.rho : ℤ) : ℝ) * ((st.rho : ℤ) : ℝ) / (S : ℝ) := by ring
        rw [he]; exact h22
      have hstep3 : (((sM2 A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) / (S : ℝ))
            * (((st.rho : ℤ) : ℝ) ^ 2 / (S : ℝ)) / 2
          ≤ (((sM2 A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) / (S : ℝ))
              * ((mu st.rho st.rho : ℤ) : ℝ) / 2 := by
        gcongr
      have hstep4 : (((sM2 A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) / (S : ℝ))
            * ((mu st.rho st.rho : ℤ) : ℝ) / 2
          ≤ ((mu (mu st.rho st.rho) (sM2 A B2 E C1 G8 A2 ror roi st w) : ℤ) : ℝ) / 2 := by
        have he : (((sM2 A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) / (S : ℝ))
              * ((mu st.rho st.rho : ℤ) : ℝ)
            = ((mu st.rho st.rho : ℤ) : ℝ) * ((sM2 A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ)
              / (S : ℝ) := by ring
        rw [he]
        exact div_le_div_of_nonneg_right h23 (by norm_num)
      linarith [hstep3, hstep4, hch]
    have h3 : (((su A B2 E C1 G8 A2 ror roi st w).r : ℤ) : ℝ)
        ≤ (((su A B2 E C1 G8 A2 ror roi st w).r : ℤ) : ℝ) + 1 := by linarith
    linarith [h1, h2, h3]
  have hbound : ‖slit r z - slit r (ACSlit.cIn st)‖
      + ‖rot t * slit r (ACSlit.cIn st) - cx (su A B2 E C1 G8 A2 ror roi st w).x
          (su A B2 E C1 G8 A2 ror roi st w).y‖
      ≤ ((((w.D + (sfp A B2 E C1 G8 A2 ror roi st w).r : ℤ)) : ℝ) / (S : ℝ)) * ρ
        + ((((sM2 A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (S : ℝ)) * ρ ^ 2 / 2
        + (((su A B2 E C1 G8 A2 ror roi st w).r : ℤ) : ℝ) / (S : ℝ) := by
    have h2 : ‖rot t * slit r (ACSlit.cIn st) - cx (su A B2 E C1 G8 A2 ror roi st w).x
        (su A B2 E C1 G8 A2 ror roi st w).y‖
        ≤ (((su A B2 E C1 G8 A2 ror roi st w).r : ℤ) : ℝ) / (S : ℝ) := hsu
    linarith [hT, h2]
  linarith [htri, hbound, hnum]

end Work.Cert
