import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.PARIMPL2.Lavaurs.wout_model

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue2

/-- On the outgoing geometric window the repelling model coordinate is still below `-R`, up to
the logarithm size of the chart coordinate: this is the elementary "loss" of the `log (-w)` term
of `approxCoordRep` over the window. -/
theorem approxCoordRep_woutG_le {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    {R H : ℝ} (hR : 2 ≤ R) (hRH : 8 * (H + 1) ≤ R) {z : ℂ}
    (hz : z ∈ Work.PARIMPL2.WoutG P R H) :
    (Work.PARIMPL2.approxCoordRep (P.κ c₀) (Work.PARIMPL2.w0 P z)).re
      ≤ -R + ‖P.κ c₀‖ * (Real.log 2 + Real.log R + Real.pi) := by
  have hRpos : 0 < R := by linarith
  have hHnn : 0 ≤ H := le_trans (abs_nonneg _) hz.2.2
  obtain ⟨-, -, hlow, hup⟩ := Work.PARIMPL2.Lavaurs.woutG_w0_bounds hRpos hHnn hz
  have hre : (Work.PARIMPL2.w0 P z).re ≤ -R := hz.2.1.2
  -- the chart coordinate is bounded by `2R` in modulus
  have hwle : ‖Work.PARIMPL2.w0 P z‖ ≤ 2 * R := by
    have hHle : H ≤ R / 8 - 1 := by linarith
    have h2 : R + H + 2 ≤ 2 * R := by linarith
    linarith
  have hwpos : 0 < ‖Work.PARIMPL2.w0 P z‖ := by linarith
  have hlogw : Real.log ‖Work.PARIMPL2.w0 P z‖ ≤ Real.log 2 + Real.log R := by
    have h : Real.log ‖Work.PARIMPL2.w0 P z‖ ≤ Real.log (2 * R) := Real.log_le_log hwpos hwle
    rwa [Real.log_mul (by norm_num) (ne_of_gt hRpos)] at h
  -- hence the logarithm of `-w` is bounded by `log 2 + log R + π`
  have hlog : ‖Complex.log (-(Work.PARIMPL2.w0 P z))‖
      ≤ Real.log 2 + Real.log R + Real.pi := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (Complex.log (-(Work.PARIMPL2.w0 P z)))
    rw [Complex.log_re, Complex.log_im] at h1
    have h2 : |Real.log ‖-(Work.PARIMPL2.w0 P z)‖| ≤ Real.log 2 + Real.log R := by
      rw [norm_neg]
      have hge1 : (1 : ℝ) ≤ ‖Work.PARIMPL2.w0 P z‖ := by linarith
      rw [abs_of_nonneg (Real.log_nonneg hge1)]
      exact hlogw
    have h3 : |(-(Work.PARIMPL2.w0 P z)).arg| ≤ Real.pi :=
      abs_le.mpr ⟨le_of_lt (Complex.neg_pi_lt_arg _), Complex.arg_le_pi _⟩
    linarith
  have hkey : -(P.κ c₀ * Complex.log (-(Work.PARIMPL2.w0 P z))).re
      ≤ ‖P.κ c₀‖ * (Real.log 2 + Real.log R + Real.pi) := by
    have h1 : -(P.κ c₀ * Complex.log (-(Work.PARIMPL2.w0 P z))).re
        ≤ ‖P.κ c₀ * Complex.log (-(Work.PARIMPL2.w0 P z))‖ := by
      have h2 : -(P.κ c₀ * Complex.log (-(Work.PARIMPL2.w0 P z))).re
          ≤ |(P.κ c₀ * Complex.log (-(Work.PARIMPL2.w0 P z))).re| := neg_le_abs _
      linarith [h2, Complex.abs_re_le_norm (P.κ c₀ * Complex.log (-(Work.PARIMPL2.w0 P z)))]
    rw [norm_mul] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_left hlog (norm_nonneg _))
  simp only [Work.PARIMPL2.approxCoordRep, Complex.sub_re]
  linarith

end Work.FlowerGlue2
