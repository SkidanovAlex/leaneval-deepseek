import Mathlib
import Submission.Work.Cert.ACSlit.Shadow
import Submission.Work.Cert.ACSlit.sM2c_ge_cauchy
import Submission.Work.APsi.slit_facts
import Submission.Work.Cert.ACBall.LuneAnalytic

namespace Work.Cert.ACSlit

open Work.Cert Complex Submission.CDTPlan

/-! ## The Cauchy estimate for the slit map -/

/-- Cauchy's estimate for the second derivative of the slit map on a disc inside `𝔻`: if `0 < d`
and `d ≤ 1 - ‖z‖` then `‖slit''(z)‖ ≤ 2/d²`. This is the exact analogue of
`Work.Cert.ACBall.lune_deriv2_le_cauchy`, using `‖slit r‖ ≤ 1` on `𝔻`
(`Work.APsi.slit_norm_le_one`) together with `Work.APsi.differentiableOn_slit` /
`Work.APsi.continuousOn_slit`. -/
theorem slit_deriv2_le_cauchy {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {z : ℂ} {d : ℝ}
    (hd : 0 < d) (h : d ≤ 1 - ‖z‖) :
    ‖deriv (deriv (Submission.CDTPlan.slit r)) z‖ ≤ 2 / d ^ 2 := by
  have htri : ∀ w : ℂ, ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
    intro w
    calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
  have hb1 : Metric.ball z d ⊆ Metric.ball (0 : ℂ) 1 := by
    intro w hw
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero] at hw ⊢
    linarith [htri w]
  have hcbd : Metric.closedBall z d ⊆ Metric.closedBall (0 : ℂ) 1 := by
    intro w hw
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hw ⊢
    linarith [htri w]
  have hcl : closure (Metric.ball z d) ⊆ Metric.closedBall (0 : ℂ) 1 :=
    fun w hw => hcbd (closure_minimal (fun x hx => Metric.ball_subset_closedBall hx)
      Metric.isClosed_closedBall hw)
  have hbdd : ∀ w ∈ Metric.sphere z d, ‖Submission.CDTPlan.slit r w‖ ≤ 1 := by
    intro w hw
    refine Work.APsi.slit_norm_le_one r hr0 hr1 w ?_
    exact (by simpa [dist_eq_norm] using
      Metric.mem_closedBall.mp (hcbd (Metric.sphere_subset_closedBall hw)))
  have hDC : DiffContOnCl ℂ (Submission.CDTPlan.slit r) (Metric.ball z d) :=
    ⟨(Work.APsi.differentiableOn_slit r hr0 hr1).mono hb1,
      (Work.APsi.continuousOn_slit r hr0 hr1).mono hcl⟩
  have hkey : ‖iteratedDeriv 2 (Submission.CDTPlan.slit r) z‖ ≤ 2 / d ^ 2 := by
    have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      (f := Submission.CDTPlan.slit r) (c := z) (R := d) (C := 1) 2 hd hDC hbdd
    simpa using hh
  have hiter : iteratedDeriv 2 (Submission.CDTPlan.slit r) z
      = deriv (deriv (Submission.CDTPlan.slit r)) z := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rwa [hiter] at hkey

/-! ## The `M2c` bound -/

/-- The Cauchy branch of the second-derivative bound of `Work.Cert.slitStage`: if `0 < sd` and
`0 < sdsq` then `sM2c = ⌈2S²/sdsq⌉` bounds `S·sup_D‖slit''‖` on the input disc. Only `0 < r < 1`,
`hokM` (gives `‖c‖ ≤ cU/S`), `hwhi` (`cU + ρ + 1 < S`, i.e. the disc is inside `𝔻`), `hrho`, `hd`, `hdsq`
are needed. Proof: `‖slit r‖ ≤ 1` on `𝔻` (`Work.APsi.slit_norm_le_one`) + Cauchy's estimate
(`norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`, exactly as in
`Work.Cert.ACBall.lune_deriv2_le_cauchy` in `Submission.Work.Cert.ACBall.LuneAnalytic`; use
`Work.APsi.differentiableOn_slit` and `Work.APsi.continuousOn_slit`), with `d := sd/S ≤ 1 − ‖u‖`,
then `md_le`/`dvu_ge` and `ACBall.norm_cx_le_of_sq_le`. Namespace: `Work.Cert.ACSlit`. -/
theorem slitStage_M2c_sound (A B2 E C1 G8 A2 ror roi : ℤ) (st : Work.Cert.St) (w : Work.Cert.SlitW)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hokM : Work.Cert.ACSlit.sokM A B2 E C1 G8 A2 ror roi st w = true)
    (hwhi : Work.Cert.ACSlit.swhi A B2 E C1 G8 A2 ror roi st w < Work.Cert.S)
    (hrho : 0 ≤ st.rho)
    (hd : 0 < Work.Cert.ACSlit.sd A B2 E C1 G8 A2 ror roi st w)
    (hdsq : 0 < Work.Cert.ACSlit.sdsq A B2 E C1 G8 A2 ror roi st w)
    {u : ℂ} (hu : ‖u - Work.Cert.ACSlit.cIn st‖ ≤ (st.rho : ℝ) / (Work.Cert.S : ℝ)) :
    ‖deriv (deriv (Submission.CDTPlan.slit r)) u‖
      ≤ ((Work.Cert.ACSlit.sM2c A B2 E C1 G8 A2 ror roi st w : ℤ) : ℝ) / (Work.Cert.S : ℝ) := by
  -- `hrho` records that the input radius `ρ = st.rho` is nonnegative
  have hrhoR : (0 : ℝ) ≤ (st.rho : ℝ) := by exact_mod_cast hrho
  -- `hwhi` says exactly that `sd > 0`
  have hsdi : Work.Cert.ACSlit.sd A B2 E C1 G8 A2 ror roi st w
      = Work.Cert.S - w.cU - st.rho - 1 := rfl
  have hsd_pos : 0 < Work.Cert.ACSlit.sd A B2 E C1 G8 A2 ror roi st w := by
    have hwhi' : w.cU + st.rho + 1 < Work.Cert.S := by
      simpa only [Work.Cert.ACSlit.swhi] using hwhi
    simp only [Work.Cert.ACSlit.sd]
    omega
  -- the `okM` flag, split into its conjuncts
  have hAll := hokM
  simp only [Work.Cert.ACSlit.sokM, Bool.and_eq_true, decide_eq_true_eq] at hAll
  have hcU0 : 0 ≤ w.cU := by tauto
  have hcr : st.cr * st.cr + st.ci * st.ci ≤ w.cU * w.cU := by tauto
  -- `‖c‖ ≤ cU/S`
  have hcU : ‖Work.Cert.ACSlit.cIn st‖ ≤ (w.cU : ℝ) / (Work.Cert.S : ℝ) :=
    Work.Cert.ACBall.norm_cx_le_of_sq_le st.cr st.ci w.cU hcU0 hcr
  -- `‖u‖ ≤ (cU + ρ)/S` from `hu` and the triangle inequality
  have hu1 : ‖u‖ ≤ ((w.cU : ℝ) + (st.rho : ℝ)) / (Work.Cert.S : ℝ) := by
    have h1 : ‖u‖ ≤ ‖u - Work.Cert.ACSlit.cIn st‖ + ‖Work.Cert.ACSlit.cIn st‖ := by
      calc ‖u‖ = ‖(u - Work.Cert.ACSlit.cIn st) + Work.Cert.ACSlit.cIn st‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖u - Work.Cert.ACSlit.cIn st‖ + ‖Work.Cert.ACSlit.cIn st‖ := norm_add_le _ _
    have h2 : ‖u - Work.Cert.ACSlit.cIn st‖ + ‖Work.Cert.ACSlit.cIn st‖
        ≤ ((w.cU : ℝ) + (st.rho : ℝ)) / (Work.Cert.S : ℝ) := by
      rw [add_div]
      linarith [hu, hcU, hrhoR]
    linarith
  -- the disc `ball u (sd/S)` lies in the unit disc
  have hsd_eq : (Work.Cert.ACSlit.sd A B2 E C1 G8 A2 ror roi st w : ℝ)
      = (Work.Cert.S : ℝ) - (w.cU : ℝ) - (st.rho : ℝ) - 1 := by
    rw [hsdi]; push_cast; ring
  have hS := Work.Cert.ACBall.S_posR
  have hd_le : (Work.Cert.ACSlit.sd A B2 E C1 G8 A2 ror roi st w : ℝ) / (Work.Cert.S : ℝ)
      ≤ 1 - ‖u‖ := by
    rw [hsd_eq]
    have h1 : 1 - ‖u‖ ≥ 1 - ((w.cU : ℝ) + (st.rho : ℝ)) / (Work.Cert.S : ℝ) := by linarith
    have h2 : (1 : ℝ) - ((w.cU : ℝ) + (st.rho : ℝ)) / (Work.Cert.S : ℝ)
        = ((Work.Cert.S : ℝ) - (w.cU : ℝ) - (st.rho : ℝ)) / (Work.Cert.S : ℝ) := by
      field_simp; ring
    rw [h2] at h1
    have h3 : ((Work.Cert.S : ℝ) - (w.cU : ℝ) - (st.rho : ℝ) - 1) / (Work.Cert.S : ℝ)
        ≤ ((Work.Cert.S : ℝ) - (w.cU : ℝ) - (st.rho : ℝ)) / (Work.Cert.S : ℝ) := by
      apply div_le_div_of_nonneg_right _ hS.le
      linarith
    linarith
  have hdr : (0 : ℝ) < (Work.Cert.ACSlit.sd A B2 E C1 G8 A2 ror roi st w : ℝ) := by
    exact_mod_cast hd
  have hd_div : (0 : ℝ) < (Work.Cert.ACSlit.sd A B2 E C1 G8 A2 ror roi st w : ℝ)
      / (Work.Cert.S : ℝ) := div_pos hdr hS
  -- Cauchy's estimate at centre `u`, radius `sd/S`
  have hcauchy := slit_deriv2_le_cauchy (r := r) hr0 hr1 (z := u)
    (d := (Work.Cert.ACSlit.sd A B2 E C1 G8 A2 ror roi st w : ℝ) / (Work.Cert.S : ℝ))
    hd_div hd_le
  have heq : 2 / ((Work.Cert.ACSlit.sd A B2 E C1 G8 A2 ror roi st w : ℝ)
        / (Work.Cert.S : ℝ)) ^ 2
      = 2 * (Work.Cert.S : ℝ) ^ 2
        / ((Work.Cert.ACSlit.sd A B2 E C1 G8 A2 ror roi st w : ℝ)) ^ 2 := by
    field_simp
  -- the integer rounding comparison `2S²/sd² ≤ sM2c/S`
  have hnum := sM2c_ge_cauchy A B2 E C1 G8 A2 ror roi st w hsd_pos hdsq
  linarith [hcauchy, hnum, heq]

end Work.Cert.ACSlit
