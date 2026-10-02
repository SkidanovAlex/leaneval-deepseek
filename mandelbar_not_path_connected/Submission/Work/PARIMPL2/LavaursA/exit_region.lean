import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.LavaursA

/-- The modulus of the principal logarithm: `‖log z‖ ≤ |log ‖z‖| + |arg z| ≤ |log ‖z‖| + π`. -/
theorem norm_log_le_log_norm_add_pi (z : ℂ) :
    ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi := by
  calc ‖Complex.log z‖
      ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |Real.log ‖z‖| + |z.arg| := by rw [Complex.log_re, Complex.log_im]
    _ ≤ |Real.log ‖z‖| + Real.pi := by
        have := Complex.abs_arg_le_pi z
        linarith

/-- **The outgoing-region estimates.**  Let `κ = P.κ c₀` and `Rep κ w = w − κ log(−w)` be the
repelling model coordinate (`Work.PARIMPL2.approxCoordRep`).  Suppose `‖w‖ ≥ 1` (true for the exit
point `q'` of the transit, whose `c₀`-chart coordinate `w0 q'` is `≈ ±R` by the chart-location
estimate), and suppose `Rep κ w` is close to the real number `−R` in the sense that its norm is
`≤ R + 2 + H + ε`, its real part lies in `[−R − 2 − ε, −R + ε]` and its imaginary part is bounded by
`H + ε`.  Then the chart coordinate `w` itself is pinned:
`|Re w + R| ≤ 2 + ε + ‖κ‖(log M + π)` and `|Im w| ≤ H + ε + ‖κ‖(log M + π)`, where `M` is any
explicit bound for the solution of `t ≤ (R + 2 + H + ε + ‖κ‖π) + ‖κ‖ log t` (supplied by
`bound_le_add_mul_log_explicit`). -/
theorem exit_region {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    {R H ε M : ℝ} (hR : 0 < R) (hH : 0 ≤ H) (hε : 0 ≤ ε) (hM1 : 1 ≤ M)
    {w : ℂ} (hwn : 1 ≤ ‖w‖)
    (hM : ∀ t : ℝ, 0 < t →
      t ≤ (R + 2 + H + ε + ‖P.κ c₀‖ * Real.pi) + ‖P.κ c₀‖ * Real.log t → t ≤ M)
    (hbound : ‖Work.PARIMPL2.approxCoordRep (P.κ c₀) w‖ ≤ R + 2 + H + ε)
    (hre : -R - 2 - ε ≤ (Work.PARIMPL2.approxCoordRep (P.κ c₀) w).re)
    (hre2 : (Work.PARIMPL2.approxCoordRep (P.κ c₀) w).re ≤ -R + ε)
    (him : |(Work.PARIMPL2.approxCoordRep (P.κ c₀) w).im| ≤ H + ε) :
    |w.re + R| ≤ 2 + ε + ‖P.κ c₀‖ * (Real.log M + Real.pi) ∧
      |w.im| ≤ H + ε + ‖P.κ c₀‖ * (Real.log M + Real.pi) := by
  set κ : ℂ := P.κ c₀ with hκ
  set u : ℂ := Work.PARIMPL2.approxCoordRep κ w with hu
  -- `w` is recovered from `u` by adding the correction `κ log (−w)`.
  have hkey : w = u + κ * Complex.log (-w) := by
    rw [hu, hκ, Work.PARIMPL2.approxCoordRep]; ring
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le zero_lt_one hwn
  -- the side conditions of the statement, recorded as explicit facts
  have hRle : 0 ≤ R := hR.le
  have hHε : 0 ≤ H + ε := add_nonneg hH hε
  have h2ε : 0 ≤ 2 + ε := by linarith [hε]
  -- the modulus of `log (−w)` in terms of `log ‖w‖`
  have hlog_le : ‖Complex.log (-w)‖ ≤ Real.log ‖w‖ + Real.pi := by
    have h1 := norm_log_le_log_norm_add_pi (-w)
    rw [norm_neg] at h1
    have h2 : |Real.log ‖w‖| = Real.log ‖w‖ := abs_of_nonneg (Real.log_nonneg hwn)
    rw [h2] at h1
    linarith
  -- `‖w‖` satisfies the self-referential inequality defining `M`
  have hnorm_le : ‖w‖ ≤ (R + 2 + H + ε + ‖κ‖ * Real.pi) + ‖κ‖ * Real.log ‖w‖ := by
    have h1 : ‖w‖ ≤ ‖u‖ + ‖κ‖ * ‖Complex.log (-w)‖ := by
      calc ‖w‖ = ‖u + κ * Complex.log (-w)‖ := congrArg norm hkey
        _ ≤ ‖u‖ + ‖κ * Complex.log (-w)‖ := norm_add_le _ _
        _ = ‖u‖ + ‖κ‖ * ‖Complex.log (-w)‖ := by rw [norm_mul]
    have h2 : ‖κ‖ * ‖Complex.log (-w)‖ ≤ ‖κ‖ * (Real.log ‖w‖ + Real.pi) :=
      mul_le_mul_of_nonneg_left hlog_le (norm_nonneg _)
    have h3 : ‖u‖ ≤ R + 2 + H + ε := hbound
    have h4 : ‖κ‖ * (Real.log ‖w‖ + Real.pi)
        = (‖κ‖ * Real.pi) + ‖κ‖ * Real.log ‖w‖ := by ring
    linarith [h1, h2, h3, h4.le, h4.ge]
  have hwM : ‖w‖ ≤ M := hM ‖w‖ hwpos hnorm_le
  have hlogw_le : Real.log ‖w‖ ≤ Real.log M := Real.log_le_log hwpos hwM
  have hlogM : ‖Complex.log (-w)‖ ≤ Real.log M + Real.pi := by linarith
  have hlogM_nonneg : 0 ≤ Real.log M + Real.pi := by
    have : 0 ≤ Real.log M := Real.log_nonneg hM1
    linarith [Real.pi_pos]
  have hcorr : ‖κ‖ * ‖Complex.log (-w)‖ ≤ ‖κ‖ * (Real.log M + Real.pi) :=
    mul_le_mul_of_nonneg_left hlogM (norm_nonneg _)
  constructor
  · have hre_u : |u.re + R| ≤ 2 + ε := by
      rw [abs_le]; constructor <;> linarith [hre, hre2, hRle, hε]
    have hwr : w.re = u.re + (κ * Complex.log (-w)).re := by
      have := congrArg Complex.re hkey
      rwa [Complex.add_re] at this
    have h1 : w.re + R = (u.re + R) + (κ * Complex.log (-w)).re := by
      rw [hwr]; ring
    rw [h1]
    calc |(u.re + R) + (κ * Complex.log (-w)).re|
        ≤ |u.re + R| + |(κ * Complex.log (-w)).re| := abs_add_le _ _
      _ ≤ (2 + ε) + ‖κ‖ * (Real.log M + Real.pi) := by
          have h2 : |(κ * Complex.log (-w)).re| ≤ ‖κ‖ * (Real.log M + Real.pi) := by
            calc |(κ * Complex.log (-w)).re|
                ≤ ‖κ * Complex.log (-w)‖ := Complex.abs_re_le_norm _
              _ = ‖κ‖ * ‖Complex.log (-w)‖ := norm_mul _ _
              _ ≤ ‖κ‖ * (Real.log M + Real.pi) := hcorr
          linarith [hre_u, h2]
  · have hwi : w.im = u.im + (κ * Complex.log (-w)).im := by
      have := congrArg Complex.im hkey
      rwa [Complex.add_im] at this
    rw [hwi]
    calc |u.im + (κ * Complex.log (-w)).im|
        ≤ |u.im| + |(κ * Complex.log (-w)).im| := abs_add_le _ _
      _ ≤ (H + ε) + ‖κ‖ * (Real.log M + Real.pi) := by
          have h2 : |(κ * Complex.log (-w)).im| ≤ ‖κ‖ * (Real.log M + Real.pi) := by
            calc |(κ * Complex.log (-w)).im|
                ≤ ‖κ * Complex.log (-w)‖ := Complex.abs_im_le_norm _
              _ = ‖κ‖ * ‖Complex.log (-w)‖ := norm_mul _ _
              _ ≤ ‖κ‖ * (Real.log M + Real.pi) := hcorr
          linarith [him, h2, hHε]

end Work.PARIMPL2.LavaursA
