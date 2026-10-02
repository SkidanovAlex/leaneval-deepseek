import Mathlib
import Submission.Work.PARIMPL.Basic
import Submission.Work.Implosion.Approx
import Submission.Work.PARIMPL2.Direct.norm_modelDisp_add_rational_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 1000000

namespace Work.PARIMPL2.Direct

open Complex

/-!
# The real and imaginary bounds on the model displacement `Φ = modelDisp (iλ) h u`

This is the location-free half of the step estimate (E2) of
`NOTES_LEAD_transit_exit_direct_S2.md`: on an arbitrary point `u` whose Écalle point
`ζ = ecalPt (iλ) u` is small in the sense `‖ζ‖ ≤ 4/R` (and `< r`, so that the `ParBounds` germ
bounds apply), one has

  `-2 ≤ Re Φ ≤ -1/3`,   `|Im Φ| ≤ 2`.

Nothing but the size of `ζ` enters: `Φ = -h(ζ)/(1+ζ·h(ζ)) + O(λ²)` (`norm_modelDisp_add_rational_le`)
and `h(ζ)` is `τ` up to `g ≤ 3/8`, so `Re Φ ≈ -1`.

The proof uses a sharper companion of `div_one_add_mul_bounds`: in the regime
`t = ‖ζ‖ ≤ 1/32`, `g ≤ 3/8` the real part of `H/(1+ζH)` is at least `2/5` (not merely `1/10`),
which is what the bound `Re Φ ≤ -1/3` needs.
-/

/-- The rational expression `H/(1+ζ·H)` in the small-`ζ` regime `‖ζ‖ ≤ t ≤ 1/32`,
`‖H - τ‖ ≤ g ≤ 3/8` (with `‖τ‖ = 1`, `‖τ - 1‖ ≤ 1/8`).

Sharper than `div_one_add_mul_bounds` (which gives the lower bound `1/10`): here
`t ≤ 1/32` gives the error term `‖H/(1+ζH) - H‖ ≤ 121/1960`, whence `Re (H/(1+ζH)) ≥ 2/5`. -/
theorem div_one_add_mul_small_bounds (τ H ζ : ℂ) (t g : ℝ)
    (hτ : ‖τ‖ = 1) (hτ1 : ‖τ - 1‖ ≤ 1 / 8) (hHτ : ‖H - τ‖ ≤ g) (hζ : ‖ζ‖ ≤ t)
    (ht0 : 0 ≤ t) (hg0 : 0 ≤ g) (ht : t ≤ 1 / 32) (hg : g ≤ 3 / 8) :
    2 / 5 ≤ (H / (1 + ζ * H)).re ∧ (H / (1 + ζ * H)).re ≤ 12 / 7 ∧
      |(H / (1 + ζ * H)).im| ≤ 19 / 20 := by
  -- ## Elementary facts about `τ`
  have hτre_le : τ.re ≤ 1 := by
    have := Complex.re_le_norm τ
    rw [hτ] at this
    linarith
  have hτre_ge : 7 / 8 ≤ τ.re := by
    have h := Complex.abs_re_le_norm (τ - 1)
    rw [Complex.sub_re, Complex.one_re] at h
    have h2 : |τ.re - 1| ≤ 1 / 8 := le_trans h hτ1
    rw [abs_le] at h2
    linarith [h2.1]
  have hτim : |τ.im| ≤ 1 / 8 := by
    have h := Complex.abs_im_le_norm (τ - 1)
    rw [Complex.sub_im, Complex.one_im, sub_zero] at h
    linarith [hτ1]
  -- ## Real/imaginary control on `H`
  have hHre_le : H.re ≤ 1 + g := by
    have h := Complex.re_le_norm (H - τ)
    rw [Complex.sub_re] at h
    have : H.re - τ.re ≤ g := le_trans h hHτ
    linarith [hτre_le]
  have hHre_ge : 7 / 8 - g ≤ H.re := by
    have h := Complex.abs_re_le_norm (H - τ)
    rw [Complex.sub_re] at h
    have h2 : |H.re - τ.re| ≤ g := le_trans h hHτ
    rw [abs_le] at h2
    linarith [h2.1, hτre_ge]
  have hHim : |H.im| ≤ 1 / 8 + g := by
    have h := Complex.abs_im_le_norm (H - τ)
    rw [Complex.sub_im] at h
    have h2 : |H.im - τ.im| ≤ g := le_trans h hHτ
    have hsplit : H.im = τ.im + (H.im - τ.im) := by ring
    rw [hsplit]
    have := abs_add_le τ.im (H.im - τ.im)
    linarith [hτim, h2, this]
  have hHnorm : ‖H‖ ≤ 1 + g := by
    have hτ' : τ + (H - τ) = H := by ring
    calc ‖H‖ = ‖τ + (H - τ)‖ := by rw [hτ']
      _ ≤ ‖τ‖ + ‖H - τ‖ := norm_add_le _ _
      _ ≤ 1 + g := by rw [hτ]; linarith
  have h1g : 1 + g ≤ 11 / 8 := by linarith
  -- ## The product `ζ * H` is small and the denominator is bounded away from zero
  have hzH : ‖ζ * H‖ ≤ 11 / 256 := by
    rw [Complex.norm_mul]
    calc ‖ζ‖ * ‖H‖ ≤ t * (1 + g) := mul_le_mul hζ hHnorm (norm_nonneg H) ht0
      _ ≤ (1 / 32) * (11 / 8) := mul_le_mul ht h1g (by linarith) (by norm_num)
      _ = 11 / 256 := by norm_num
  have hDnorm : 245 / 256 ≤ ‖1 + ζ * H‖ := by
    have h := norm_sub_le (1 + ζ * H) (ζ * H)
    rw [add_sub_cancel_right, norm_one] at h
    linarith
  have hDne : (1 + ζ * H) ≠ 0 := by
    intro hzero
    have : ‖1 + ζ * H‖ = 0 := by rw [hzero, norm_zero]
    linarith
  -- ## The algebraic identity `H/D - H = -ζH²/D`
  have hsub : H / (1 + ζ * H) - H = -(ζ * H ^ 2 / (1 + ζ * H)) := by
    have hD' : (1 + H * ζ) ≠ 0 := by simpa [mul_comm] using hDne
    field_simp [hD']
    ring
  have hnorm_sub : ‖H / (1 + ζ * H) - H‖ = ‖ζ * H ^ 2 / (1 + ζ * H)‖ := by
    rw [hsub, norm_neg]
  -- ## The error term `‖ζH²/D‖ ≤ 121/1960`
  have hEd : ‖ζ * H ^ 2 / (1 + ζ * H)‖ ≤ 121 / 1960 := by
    rw [Complex.norm_div, Complex.norm_mul, Complex.norm_pow]
    have hnum : ‖ζ‖ * ‖H‖ ^ 2 ≤ t * (1 + g) ^ 2 := by
      have hsq : ‖H‖ ^ 2 ≤ (1 + g) ^ 2 := by nlinarith [hHnorm, norm_nonneg H, hg0]
      exact mul_le_mul hζ hsq (sq_nonneg _) ht0
    have hnum2 : t * (1 + g) ^ 2 ≤ 121 / 2048 := by
      have h1g2 : (1 + g) ^ 2 ≤ (11 / 8) ^ 2 := by nlinarith [h1g, hg0]
      calc t * (1 + g) ^ 2 ≤ (1 / 32) * (11 / 8) ^ 2 :=
            mul_le_mul ht h1g2 (sq_nonneg _) (by norm_num)
        _ = 121 / 2048 := by norm_num
    have hstep1 : ‖ζ‖ * ‖H‖ ^ 2 / ‖1 + ζ * H‖ ≤ t * (1 + g) ^ 2 / ‖1 + ζ * H‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg _)
    have hstep2 : t * (1 + g) ^ 2 / ‖1 + ζ * H‖ ≤ t * (1 + g) ^ 2 / (245 / 256) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hDnorm
    have hstep3 : t * (1 + g) ^ 2 / (245 / 256) ≤ 121 / 1960 := by
      calc t * (1 + g) ^ 2 / (245 / 256) ≤ (121 / 2048) / (245 / 256) :=
            div_le_div_of_nonneg_right hnum2 (by norm_num)
        _ = 121 / 1960 := by norm_num
    linarith [hstep1, hstep2, hstep3]
  -- ## Real part, upper bound
  have hb_up : (H / (1 + ζ * H) - H).re ≤ 121 / 1960 := by
    calc (H / (1 + ζ * H) - H).re
        ≤ ‖H / (1 + ζ * H) - H‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
      _ = ‖ζ * H ^ 2 / (1 + ζ * H)‖ := hnorm_sub
      _ ≤ 121 / 1960 := hEd
  have hre_top : (H / (1 + ζ * H)).re ≤ 12 / 7 := by
    have hsplit : H / (1 + ζ * H) = H + (H / (1 + ζ * H) - H) := by ring
    have : (H / (1 + ζ * H)).re ≤ H.re + 121 / 1960 := by
      rw [hsplit, Complex.add_re]
      linarith [hb_up]
    linarith [this, hHre_le, hg]
  -- ## Real part, lower bound
  have hb_low : -(121 / 1960) ≤ (H / (1 + ζ * H) - H).re := by
    calc -(121 / 1960) ≤ -‖H / (1 + ζ * H) - H‖ := by
          rw [hnorm_sub]; linarith [hEd]
      _ ≤ -|(H / (1 + ζ * H) - H).re| := neg_le_neg (Complex.abs_re_le_norm _)
      _ ≤ (H / (1 + ζ * H) - H).re := neg_abs_le _
  have hre_bot : 2 / 5 ≤ (H / (1 + ζ * H)).re := by
    have hsplit : H / (1 + ζ * H) = H + (H / (1 + ζ * H) - H) := by ring
    have h2 : (7 / 8 - g) - 121 / 1960 ≤ (H / (1 + ζ * H)).re := by
      rw [hsplit, Complex.add_re]
      linarith [hb_low, hHre_ge]
    linarith [h2, hg]
  -- ## Imaginary part
  have hb_im : |(H / (1 + ζ * H) - H).im| ≤ 121 / 1960 := by
    calc |(H / (1 + ζ * H) - H).im| ≤ ‖H / (1 + ζ * H) - H‖ := Complex.abs_im_le_norm _
      _ = ‖ζ * H ^ 2 / (1 + ζ * H)‖ := hnorm_sub
      _ ≤ 121 / 1960 := hEd
  have him : |(H / (1 + ζ * H)).im| ≤ 19 / 20 := by
    have hsplit : H / (1 + ζ * H) = H + (H / (1 + ζ * H) - H) := by ring
    rw [hsplit, Complex.add_im]
    calc |H.im + (H / (1 + ζ * H) - H).im|
        ≤ |H.im| + |(H / (1 + ζ * H) - H).im| := abs_add_le _ _
      _ ≤ (1 / 8 + g) + 121 / 1960 := by linarith [hHim, hb_im]
      _ ≤ 19 / 20 := by linarith
  exact ⟨hre_bot, hre_top, him⟩

/-- **The real and imaginary bounds on the model displacement.**  For `a = iλ`, `λR² ≤ 1`,
`R ≥ 128` and a point `u` whose Écalle point `ζ(u)` is small (`‖ζ(u)‖ ≤ 4/R`, `‖ζ(u)‖ < r`) and
satisfies the germ bounds `ParBounds`, the displacement of the Écalle coordinate over one
iterate satisfies `-2 ≤ Re Φ ≤ -1/3` and `|Im Φ| ≤ 2`. -/
theorem modelDisp_re_im_bounds (lam R B : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1) (hB0 : 0 ≤ B)
    (h : ℂ → ℂ) (τ h1 : ℂ) (A r : ℝ) (hA : 0 ≤ A)
    (hb : Work.PARIMPL.ParBounds h τ h1 A r) (hh1 : ‖h1‖ ≤ B) (hτ1 : ‖τ - 1‖ ≤ 1 / 8)
    (hAr : 4 * B / R + 16 * A / R ^ 2 ≤ 3 / 8)
    (u : ℂ) (hζn : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ≤ 4 / R)
    (hζr : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ < r) :
    (-2 : ℝ) ≤ (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).re ∧
      (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).re ≤ -(1 / 3) ∧
      |(Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).im| ≤ 2 := by
  have hRpos : (0 : ℝ) < R := by linarith
  have h128R2 : (128 : ℝ) ≤ R ^ 2 := by nlinarith [hR]
  have hlam_le : lam ≤ 1 / 128 := by
    have h1 : lam * 128 ≤ lam * R ^ 2 := mul_le_mul_of_nonneg_left h128R2 (le_of_lt hlam)
    have h2 : lam * 128 ≤ 1 := by linarith [hlamR, h1]
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 128)]
    linarith
  have hlam8 : lam ≤ 1 / 8 := by linarith
  have h100 : 100 * lam ^ 2 ≤ 1 / 100 := by nlinarith [hlam_le, hlam]
  -- ## The abbreviations
  set ζ : ℂ := Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u with hζdef
  set H : ℂ := h ζ with hHdef
  set t : ℝ := ‖ζ‖ with htdef
  set g : ℝ := B * t + A * t ^ 2 with hgdef
  set Φ : ℂ := Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u with hΦdef
  set Q : ℂ := H / (1 + ζ * H) with hQdef
  -- ## Facts about `t` and `g`
  have ht0 : 0 ≤ t := by rw [htdef]; exact norm_nonneg ζ
  have ht32 : t ≤ 1 / 32 := by
    have h1 : (4 : ℝ) / R ≤ 1 / 32 := by
      rw [div_le_div_iff₀ hRpos (by norm_num : (0 : ℝ) < 32)]
      linarith
    linarith [hζn, h1]
  have hg0 : 0 ≤ g := by rw [hgdef]; positivity
  have hg38 : g ≤ 3 / 8 := by
    have hBt : B * t ≤ 4 * B / R := by
      have h1 : B * t ≤ B * (4 / R) := mul_le_mul_of_nonneg_left hζn hB0
      calc B * t ≤ B * (4 / R) := h1
        _ = 4 * B / R := by ring
    have hAt : A * t ^ 2 ≤ 16 * A / R ^ 2 := by
      have ht2 : t ^ 2 ≤ (4 / R) ^ 2 := pow_le_pow_left₀ ht0 hζn 2
      calc A * t ^ 2 ≤ A * (4 / R) ^ 2 := mul_le_mul_of_nonneg_left ht2 hA
        _ = 16 * A / R ^ 2 := by ring
    rw [hgdef]
    linarith [hBt, hAt, hAr]
  -- ## The `ParBounds` facts
  obtain ⟨hr0, hτnorm, hgerm, hHle, hHge, hτ12⟩ := hb
  have hz_lt_r : ‖ζ‖ < r := by rw [← htdef]; exact hζr
  have hH2 : ‖H‖ ≤ 2 := by
    rw [hHdef]
    exact hHle ζ hz_lt_r
  have hHτ : ‖H - τ‖ ≤ g := by
    have hg' : ‖H - τ - h1 * ζ‖ ≤ A * ‖ζ‖ ^ 2 := by
      rw [hHdef]
      exact hgerm ζ hz_lt_r
    have htri : ‖H - τ‖ ≤ ‖H - τ - h1 * ζ‖ + ‖h1 * ζ‖ := by
      have hh := norm_add_le (H - τ - h1 * ζ) (h1 * ζ)
      have heq : (H - τ - h1 * ζ) + h1 * ζ = H - τ := by ring
      rwa [heq] at hh
    have hmm : ‖h1 * ζ‖ ≤ B * t := by
      rw [norm_mul, ← htdef]
      exact mul_le_mul hh1 le_rfl (norm_nonneg ζ) hB0
    have hsq : A * ‖ζ‖ ^ 2 = A * t ^ 2 := by rw [← htdef]
    rw [hgdef]
    linarith [htri, hg', hmm, hsq]
  -- ## The two key estimates
  have hQb := div_one_add_mul_small_bounds τ H ζ t g hτnorm hτ1 hHτ
    (le_of_eq htdef.symm) ht0 hg0 ht32 hg38
  obtain ⟨hQbot, hQtop, hQim⟩ := hQb
  have hrat : ‖Φ + Q‖ ≤ 100 * lam ^ 2 := by
    have h := norm_modelDisp_add_rational_le lam hlam hlam8 h u
      (by rw [← hζdef]; rw [← htdef]; linarith [hζn, hRpos])
      (by rw [← hζdef, ← hHdef]; exact hH2)
    rw [hΦdef, hQdef, hHdef, hζdef]
    exact h
  -- ## Conclusion
  have hΦQ_re : Φ.re = (Φ + Q).re - Q.re := by rw [Complex.add_re]; ring
  have hΦQ_im : Φ.im = (Φ + Q).im - Q.im := by rw [Complex.add_im]; ring
  refine ⟨?_, ?_, ?_⟩
  · have h1 : -‖Φ + Q‖ ≤ (Φ + Q).re := by
      have := (abs_le.mp (Complex.abs_re_le_norm (Φ + Q))).1
      linarith
    rw [hΦQ_re]
    linarith [h1, hrat, h100, hQtop]
  · have h1 : (Φ + Q).re ≤ ‖Φ + Q‖ := Complex.re_le_norm _
    rw [hΦQ_re]
    linarith [h1, hrat, h100, hQbot]
  · have h1 : |(Φ + Q).im| ≤ ‖Φ + Q‖ := Complex.abs_im_le_norm _
    have h3 : |Φ.im| ≤ |(Φ + Q).im| + |Q.im| := by
      rw [hΦQ_im]
      have h4 : |(Φ + Q).im - Q.im| ≤ |(Φ + Q).im| + |Q.im| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le (Φ + Q).im (-Q.im)
      exact h4
    linarith [h3, h1, hrat, h100, hQim]

end Work.PARIMPL2.Direct
