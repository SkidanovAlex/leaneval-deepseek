import Mathlib
import Submission.Work.Cert.ACBall.LuneChain
import Submission.Work.Cert.ACBall.LuneAnalytic
import Submission.Work.Cert.ACBall.luneStage_M2_sound
import Submission.Work.ANum3.taylor_disc_le

/-! Guidance from the project lead (the requester): see `Submission/Work/Cert/Spec.lean` for the
contract `LuneStageSound` and `Submission/Work/Cert/Defs.lean` for the checker `luneStage` (v2, ball
arithmetic at the point `z_c = −c`).

The proof: `ok` exposes `okB` (`bsqrtOK R sr`, `binvOK s Ls`), `okM` (`D² ≥ |v'|²`, the witnesses
`zU`, `RU`, `RL`, `rpU`) and `okW` (the `M2e` side conditions); `ball_ops` (via `ACBall.LuneChain`)
gives `lv ∋ lune (36/5)(−c)` and `lvp ∋ lune' (−c)` up to their ball radii, `ACBall.luneStage_M2_sound`
bounds `lune''` on the whole input disc by `lM2/S`, and the second-order Taylor estimate
(`taylor_disc_le`) plus `mu_ge`/`chalf_ge` finish. -/

namespace Work.Cert

open Complex Submission.CDTPlan

/-! ## Destructuring the `ok` flag -/

theorem lokB_spec (st : St) (w : LuneW) (h : ACBall.lokB st w = true) :
    bsqrtOK (ACBall.lR st) w.sr = true ∧ binvOK (ACBall.ls st w) w.Ls = true := by
  simp only [ACBall.lokB, Bool.and_eq_true] at h
  exact ⟨h.1, h.2⟩

theorem lokM_spec (st : St) (w : LuneW) (h : ACBall.lokM st w = true) :
    0 ≤ w.D ∧ (ACBall.lvp st w).x * (ACBall.lvp st w).x
        + (ACBall.lvp st w).y * (ACBall.lvp st w).y ≤ w.D * w.D ∧
      0 ≤ w.zU ∧ st.cr * st.cr + st.ci * st.ci ≤ w.zU * w.zU ∧
      0 ≤ w.RU ∧ (ACBall.lR st).x * (ACBall.lR st).x + (ACBall.lR st).y * (ACBall.lR st).y
        ≤ w.RU * w.RU ∧
      0 ≤ w.RL ∧ w.RL * w.RL ≤ (ACBall.lR st).x * (ACBall.lR st).x
        + (ACBall.lR st).y * (ACBall.lR st).y ∧
      0 ≤ w.rpU ∧ (ACBall.lRp st).x * (ACBall.lRp st).x + (ACBall.lRp st).y * (ACBall.lRp st).y
        ≤ w.rpU * w.rpU := by
  simp only [ACBall.lokM, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> tauto

/-! ## The main theorem -/

set_option maxHeartbeats 1000000 in
theorem luneStage_sound : LuneStageSound := by
  intro st w hok z hz
  obtain ⟨hstok, hokB, hokM, hokW, hzU, hM2INF, hrho, hrho2nn⟩ := ACBall.luneStage_ok_spec st w hok
  rw [ACBall.luneStage_cr, ACBall.luneStage_ci, ACBall.luneStage_rho]
  obtain ⟨hbOK, hLsk⟩ := lokB_spec st w hokB
  obtain ⟨hD0, hvpD, hzU0, hcU, hRU0, hRUsq, hRL0, hRLsq, hrpU0, hrpUsq⟩ := lokM_spec st w hokM
  -- the input centre and disc
  set rho : ℝ := ((st.rho : ℤ) : ℝ) / (S : ℝ) with hρdef
  have hρnn : 0 ≤ rho := by
    rw [hρdef]
    exact div_nonneg (by exact_mod_cast hrho) (le_of_lt ACBall.S_posR)
  have hcUbound : ‖ACBall.cIn st‖ ≤ ((w.zU : ℤ) : ℝ) / (S : ℝ) :=
    ACBall.norm_cx_le_of_sq_le st.cr st.ci w.zU hzU0 hcU
  have hzUlt : ((w.zU : ℤ) : ℝ) / (S : ℝ) < 1 := by
    rw [div_lt_one ACBall.S_posR]
    exact_mod_cast (by omega : w.zU < S)
  have hcIn_lt : ‖ACBall.cIn st‖ < 1 := lt_of_le_of_lt hcUbound hzUlt
  have hzdisc : ‖z - ACBall.cIn st‖ ≤ rho := by rw [hρdef]; exact hz
  -- points of the disc stay in the unit disc
  have hmem1 : ∀ u : ℂ, ‖u - (-(ACBall.cIn st))‖ ≤ rho → ‖u‖ < 1 := by
    intro u hu
    have h1 : ‖u‖ ≤ ‖u - (-(ACBall.cIn st))‖ + ‖ACBall.cIn st‖ := by
      calc ‖u‖ = ‖(u - (-(ACBall.cIn st))) + (-(ACBall.cIn st))‖ := by ring_nf
        _ ≤ ‖u - (-(ACBall.cIn st))‖ + ‖(-(ACBall.cIn st))‖ := norm_add_le _ _
        _ = ‖u - (-(ACBall.cIn st))‖ + ‖ACBall.cIn st‖ := by rw [norm_neg]
    have h2 : ((w.zU : ℤ) : ℝ) / (S : ℝ) + rho < 1 := by
      rw [hρdef, ← add_div]
      rw [div_lt_one ACBall.S_posR]
      exact_mod_cast (by omega : w.zU + st.rho < S)
    linarith
  -- the ball chain
  have hbs : ACBall.BallMem (ACBall.ls st w)
      ((Work.APsi.luneR (36 / 5) (-(ACBall.cIn st))) ^ (1 / 2 : ℂ)) :=
    ACBall.ballMem_ls st w hbOK
  have hbv : ACBall.BallMem (ACBall.lv st w) (lune (36 / 5) (-(ACBall.cIn st))) :=
    ACBall.ballMem_lv st w hbs
  have hbinv : ACBall.BallMem (ACBall.linvs st w)
      (((Work.APsi.luneR (36 / 5) (-(ACBall.cIn st))) ^ (1 / 2 : ℂ))⁻¹) :=
    ACBall.ballMem_linvs st w hLsk hbs
  have hbRp := ACBall.ballMem_lRp st
  have hbvp : ACBall.BallMem (ACBall.lvp st w) (deriv (lune (36 / 5)) (-(ACBall.cIn st))) :=
    ACBall.ballMem_lvp st w hcIn_lt hbRp hbinv
  have hvpr : (0 : ℤ) ≤ (ACBall.lvp st w).r := ACBall.nonneg_radius hbvp
  -- the derivative bound at the centre
  have hvpval : ‖cx (ACBall.lvp st w).x (ACBall.lvp st w).y‖ ≤ ((w.D : ℤ) : ℝ) / (S : ℝ) :=
    ACBall.norm_cx_le_of_sq_le _ _ _ hD0 hvpD
  have hderiv : ‖deriv (lune (36 / 5)) (-(ACBall.cIn st))‖
      ≤ ((w.D + (ACBall.lvp st w).r : ℤ) : ℝ) / (S : ℝ) := by
    have h3 : ‖deriv (lune (36 / 5)) (-(ACBall.cIn st))‖
        ≤ ‖deriv (lune (36 / 5)) (-(ACBall.cIn st)) - cx (ACBall.lvp st w).x (ACBall.lvp st w).y‖
          + ‖cx (ACBall.lvp st w).x (ACBall.lvp st w).y‖ := by
      calc ‖deriv (lune (36 / 5)) (-(ACBall.cIn st))‖
          = ‖(deriv (lune (36 / 5)) (-(ACBall.cIn st)) - cx (ACBall.lvp st w).x (ACBall.lvp st w).y)
              + cx (ACBall.lvp st w).x (ACBall.lvp st w).y‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have h4 : ‖deriv (lune (36 / 5)) (-(ACBall.cIn st)) - cx (ACBall.lvp st w).x (ACBall.lvp st w).y‖
        ≤ (((ACBall.lvp st w).r : ℤ) : ℝ) / (S : ℝ) := hbvp
    push_cast
    rw [add_div]
    linarith
  have hMnn : (0 : ℝ) ≤ ((w.D + (ACBall.lvp st w).r : ℤ) : ℝ) / (S : ℝ) := by
    have h1 : (0 : ℝ) ≤ ((w.D : ℤ) : ℝ) := by exact_mod_cast hD0
    have h2 : (0 : ℝ) ≤ (((ACBall.lvp st w).r : ℤ) : ℝ) := by exact_mod_cast hvpr
    have h3 : (0 : ℝ) ≤ (((w.D : ℤ) : ℝ) + (((ACBall.lvp st w).r : ℤ) : ℝ)) := by linarith
    rw [show (((w.D + (ACBall.lvp st w).r : ℤ) : ℝ)) = ((w.D : ℤ) : ℝ)
      + (((ACBall.lvp st w).r : ℤ) : ℝ) by push_cast; ring]
    exact div_nonneg h3 (le_of_lt ACBall.S_posR)
  -- the second-derivative bound on the whole disc
  have hM2bound : ∀ u : ℂ, ‖u - (-(ACBall.cIn st))‖ ≤ ((st.rho : ℤ) : ℝ) / (S : ℝ) →
      ‖deriv (deriv (lune (36 / 5))) u‖ ≤ ((ACBall.lM2 st w : ℤ) : ℝ) / (S : ℝ) :=
    fun u hu => ACBall.luneStage_M2_sound st w hokM hokW hzU hM2INF hrho hu
  have hCnn : (0 : ℝ) ≤ ((ACBall.lM2 st w : ℤ) : ℝ) / (S : ℝ) := by
    have h0 : ‖(-(ACBall.cIn st)) - (-(ACBall.cIn st))‖ ≤ ((st.rho : ℤ) : ℝ) / (S : ℝ) := by
      rw [sub_self, norm_zero]
      rw [← hρdef]
      exact hρnn
    exact le_trans (norm_nonneg _) (hM2bound _ h0)
  -- second-order Taylor estimate on the input disc
  have hf : ∀ u : ℂ, ‖u - (-(ACBall.cIn st))‖ ≤ rho →
      DifferentiableAt ℂ (lune (36 / 5)) u := by
    intro u hu
    refine (Work.APsi.lune_differentiableOn_ball (36 / 5) (by norm_num)).differentiableAt ?_
    exact Metric.isOpen_ball.mem_nhds (by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hmem1 u hu)
  have hf' : ∀ u : ℂ, ‖u - (-(ACBall.cIn st))‖ ≤ rho →
      DifferentiableAt ℂ (deriv (lune (36 / 5))) u := by
    intro u hu
    refine (ACBall.deriv_lune_differentiableOn).differentiableAt ?_
    exact Metric.isOpen_ball.mem_nhds (by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hmem1 u hu)
  have hTaylor := Work.ANum3.taylor_disc_le (f := lune (36 / 5)) (c := -(ACBall.cIn st))
    (ρ := rho) (M := ((w.D + (ACBall.lvp st w).r : ℤ) : ℝ) / (S : ℝ))
    (C := ((ACBall.lM2 st w : ℤ) : ℝ) / (S : ℝ)) hρnn hMnn hCnn hf hf' hderiv hM2bound
  have hT := hTaylor (-z) (by
    rw [show -z - (-(ACBall.cIn st)) = -(z - ACBall.cIn st) by ring, norm_neg]
    exact hzdisc)
  have htri : ‖lune (36 / 5) (-z) - cx (ACBall.lv st w).x (ACBall.lv st w).y‖
      ≤ ‖lune (36 / 5) (-z) - lune (36 / 5) (-(ACBall.cIn st))‖
        + ‖lune (36 / 5) (-(ACBall.cIn st)) - cx (ACBall.lv st w).x (ACBall.lv st w).y‖ := by
    calc ‖lune (36 / 5) (-z) - cx (ACBall.lv st w).x (ACBall.lv st w).y‖
        = ‖(lune (36 / 5) (-z) - lune (36 / 5) (-(ACBall.cIn st)))
            + (lune (36 / 5) (-(ACBall.cIn st)) - cx (ACBall.lv st w).x (ACBall.lv st w).y)‖ := by
          ring_nf
      _ ≤ _ := norm_add_le _ _
  have hbv' : ‖lune (36 / 5) (-(ACBall.cIn st)) - cx (ACBall.lv st w).x (ACBall.lv st w).y‖
      ≤ (((ACBall.lv st w).r : ℤ) : ℝ) / (S : ℝ) := hbv
  -- the numeric comparison
  have hnum : (((w.D + (ACBall.lvp st w).r : ℤ) : ℝ) / (S : ℝ)) * rho
        + (((ACBall.lM2 st w : ℤ) : ℝ) / (S : ℝ)) * rho ^ 2 / 2
        + (((ACBall.lv st w).r : ℤ) : ℝ) / (S : ℝ)
      ≤ ((ACBall.lrho2 st w : ℤ) : ℝ) / (S : ℝ) := by
    rw [le_div_iff₀ ACBall.S_posR]
    have hS := ACBall.S_posR
    have hM2nn : (0 : ℝ) ≤ ((ACBall.lM2 st w : ℤ) : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hCnn (le_of_lt hS)
      rw [zero_mul, div_mul_cancel₀ _ (ne_of_gt hS)] at h
      exact h
    have hX : ((((w.D + (ACBall.lvp st w).r : ℤ) : ℝ) / (S : ℝ)) * rho
          + (((ACBall.lM2 st w : ℤ) : ℝ) / (S : ℝ)) * rho ^ 2 / 2
          + (((ACBall.lv st w).r : ℤ) : ℝ) / (S : ℝ)) * (S : ℝ)
        = ((w.D + (ACBall.lvp st w).r : ℤ) : ℝ) * ((st.rho : ℤ) : ℝ) / (S : ℝ)
          + ((ACBall.lM2 st w : ℤ) : ℝ) * ((st.rho : ℤ) : ℝ) ^ 2 / (2 * (S : ℝ) ^ 2)
          + (((ACBall.lv st w).r : ℤ) : ℝ) := by
      rw [hρdef]
      field_simp
      try ring
    rw [hX, ACBall.lrho2]
    push_cast
    have h1 : (((w.D : ℤ) : ℝ) + (((ACBall.lvp st w).r : ℤ) : ℝ)) * ((st.rho : ℤ) : ℝ) / (S : ℝ)
        ≤ ((mu st.rho (w.D + (ACBall.lvp st w).r) : ℤ) : ℝ) := by
      have h := ACBall.mu_ge st.rho (w.D + (ACBall.lvp st w).r)
      have h' : ((st.rho : ℤ) : ℝ) * (((w.D : ℤ) : ℝ) + (((ACBall.lvp st w).r : ℤ) : ℝ)) / (S : ℝ)
          ≤ ((mu st.rho (w.D + (ACBall.lvp st w).r) : ℤ) : ℝ) := by
        push_cast at h ⊢
        exact h
      rw [mul_comm] at h'
      exact h'
    have h2 : ((ACBall.lM2 st w : ℤ) : ℝ) * ((st.rho : ℤ) : ℝ) ^ 2 / (2 * (S : ℝ) ^ 2)
        ≤ ((chalf (mu (mu st.rho st.rho) (ACBall.lM2 st w)) : ℤ) : ℝ) := by
      have h22 := ACBall.mu_ge st.rho st.rho
      have h23 := ACBall.mu_ge (mu st.rho st.rho) (ACBall.lM2 st w)
      have hch := ACBall.chalf_ge (mu (mu st.rho st.rho) (ACBall.lM2 st w))
      have hr2 : (0 : ℝ) ≤ ((st.rho : ℤ) : ℝ) := by exact_mod_cast hrho
      have hstep1 : ((ACBall.lM2 st w : ℤ) : ℝ) * ((st.rho : ℤ) : ℝ) ^ 2 / (2 * (S : ℝ) ^ 2)
          = (((ACBall.lM2 st w : ℤ) : ℝ) / (S : ℝ)) * (((st.rho : ℤ) : ℝ) ^ 2 / (S : ℝ)) / 2 := by
        field_simp
        try ring
      rw [hstep1]
      have hstep2 : ((st.rho : ℤ) : ℝ) ^ 2 / (S : ℝ) ≤ ((mu st.rho st.rho : ℤ) : ℝ) := by
        have : ((st.rho : ℤ) : ℝ) ^ 2 / (S : ℝ)
            = ((st.rho : ℤ) : ℝ) * ((st.rho : ℤ) : ℝ) / (S : ℝ) := by ring
        rw [this]; exact h22
      have hstep3 : (((ACBall.lM2 st w : ℤ) : ℝ) / (S : ℝ)) * (((st.rho : ℤ) : ℝ) ^ 2 / (S : ℝ)) / 2
          ≤ (((ACBall.lM2 st w : ℤ) : ℝ) / (S : ℝ)) * ((mu st.rho st.rho : ℤ) : ℝ) / 2 := by
        gcongr
      have hstep4 : (((ACBall.lM2 st w : ℤ) : ℝ) / (S : ℝ)) * ((mu st.rho st.rho : ℤ) : ℝ) / 2
          ≤ ((mu (mu st.rho st.rho) (ACBall.lM2 st w) : ℤ) : ℝ) / 2 := by
        have he : (((ACBall.lM2 st w : ℤ) : ℝ) / (S : ℝ)) * ((mu st.rho st.rho : ℤ) : ℝ)
            = ((mu st.rho st.rho : ℤ) : ℝ) * ((ACBall.lM2 st w : ℤ) : ℝ) / (S : ℝ) := by ring
        rw [he]
        exact div_le_div_of_nonneg_right h23 (by norm_num)
      linarith [hstep3, hstep4, hch]
    have h3 : (((ACBall.lv st w).r : ℤ) : ℝ) ≤ (((ACBall.lv st w).r : ℤ) : ℝ) + 1 := by linarith
    linarith [h1, h2, h3]
  calc ‖lune (36 / 5) (-z) - cx (ACBall.lv st w).x (ACBall.lv st w).y‖
      ≤ ‖lune (36 / 5) (-z) - lune (36 / 5) (-(ACBall.cIn st))‖
        + ‖lune (36 / 5) (-(ACBall.cIn st)) - cx (ACBall.lv st w).x (ACBall.lv st w).y‖ := htri
    _ ≤ ((((w.D + (ACBall.lvp st w).r : ℤ) : ℝ) / (S : ℝ)) * rho
          + (((ACBall.lM2 st w : ℤ) : ℝ) / (S : ℝ)) * rho ^ 2 / 2)
        + (((ACBall.lv st w).r : ℤ) : ℝ) / (S : ℝ) := by linarith [hT, hbv']
    _ ≤ ((ACBall.lrho2 st w : ℤ) : ℝ) / (S : ℝ) := hnum

end Work.Cert
