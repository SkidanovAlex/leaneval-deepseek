import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.Implosion.Approx
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL2.Direct.norm_modelDisp_add_rational_le
import Submission.Work.PARIMPL2.Direct.modelDisp_re_le_signed

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.PARIMPL2.Direct

open Complex

/-!
# The lower bound on the real part of the model displacement

For the rotated local normal form `f(ζ) = ζ + (ζ² − a²)h(ζ)` with `a = iλ`, `τ = h(0)` of
modulus one and `h(ζ) = τ + h₁ζ + O(ζ²)` with `‖h₁‖ ≤ B`, `‖h(ζ) − τ − h₁ζ‖ ≤ A‖ζ‖²`, at a
point whose Écalle point `ζ = ecalPt (iλ) u` is small (`‖ζ‖ ≤ 4/R`, `R ≥ 128`), the real part
of the displacement `Φ = modelDisp (iλ) h u` satisfies

  `Re Φ ≥ -1 - 35λ² - (B+2)‖ζ‖ - (A+35)‖ζ‖²`.

The proof has two ingredients:

* the *tight* rational approximation `‖Φ + h(ζ)/(1+ζh(ζ))‖ ≤ 9λ²`
  (`norm_modelDisp_add_rational_le_tight`);
* the sharp bound `Re (h(ζ)/(1+ζh(ζ))) ≤ 1 + (B+2)‖ζ‖ + (A+35)‖ζ‖²`
  (`re_div_one_add_mul_le` below), which keeps the linear coefficient `B+2`: the rational
  correction `−ζh(ζ)²/(1+ζh(ζ))` is only `≤ 2‖ζ‖ + 35‖ζ‖²`, the `2` being the
  `(1+g)²/(1−t(1+g)) ≤ 2` bound in the regime `t ≤ 1/32`, `g ≤ 3/8`.
-/

/-- **Sharp upper bound for the rational expression `H/(1+ζH)`.**

Let `‖τ‖ ≤ 1`, `‖H − τ‖ ≤ B t + A t²`, `‖ζ‖ ≤ t`, with `t ≤ 1/32`, `B, A ≥ 0` and
`B t + A t² ≤ 3/8` (so that `g := B t + A t²` plays the role of `‖H − τ‖`).  Then

  `Re (H/(1+ζH)) ≤ 1 + (B+2)t + (A+35)t²`.

The estimate is `Re H ≤ 1 + g` combined with `H/(1+ζH) = H − ζH²/(1+ζH)`; the correction
has modulus at most `t(1+g)²/(1 − t(1+g)) ≤ 2t`, using `1 + g ≤ 11/8`, `t(1+g) ≤ 11/256`
and `(1+g)²/(1−t(1+g)) ≤ (121/64)/(245/256) = 484/245 ≤ 2`. -/
theorem re_div_one_add_mul_le (τ H ζ : ℂ) (B A t : ℝ) (hτ : ‖τ‖ ≤ 1)
    (hHτ : ‖H - τ‖ ≤ B * t + A * t ^ 2) (hζ : ‖ζ‖ ≤ t) (ht0 : 0 ≤ t)
    (ht : t ≤ 1 / 32) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hg : B * t + A * t ^ 2 ≤ 3 / 8) :
    (H / (1 + ζ * H)).re ≤ 1 + (B + 2) * t + (A + 35) * t ^ 2 := by
  have hg0 : 0 ≤ B * t + A * t ^ 2 :=
    add_nonneg (mul_nonneg hB ht0) (mul_nonneg hA (sq_nonneg t))
  -- `‖H‖ ≤ 1 + g`
  have hHn : ‖H‖ ≤ 1 + (B * t + A * t ^ 2) := by
    have hsplit : H = τ + (H - τ) := by ring
    calc ‖H‖ = ‖τ + (H - τ)‖ := by congr 1
      _ ≤ ‖τ‖ + ‖H - τ‖ := norm_add_le _ _
      _ ≤ 1 + (B * t + A * t ^ 2) := by linarith
  have hHn0 : 0 ≤ 1 + (B * t + A * t ^ 2) := by linarith
  have h1g : 1 + (B * t + A * t ^ 2) ≤ 11 / 8 := by linarith
  -- `‖ζH‖ ≤ 11/256`
  have hzH : ‖ζ * H‖ ≤ 11 / 256 := by
    rw [norm_mul]
    calc ‖ζ‖ * ‖H‖ ≤ t * (1 + (B * t + A * t ^ 2)) :=
          mul_le_mul hζ hHn (norm_nonneg H) ht0
      _ ≤ (1 / 32) * (11 / 8) := mul_le_mul ht h1g (by linarith) (by norm_num)
      _ = 11 / 256 := by norm_num
  -- the denominator is `≥ 245/256`, hence nonzero
  have hD : (245 : ℝ) / 256 ≤ ‖1 + ζ * H‖ := by
    have h := norm_sub_le (1 + ζ * H) (ζ * H)
    rw [add_sub_cancel_right, norm_one] at h
    linarith
  have hDpos : 0 < ‖1 + ζ * H‖ := by linarith
  have hDne : 1 + ζ * H ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hDpos
    exact lt_irrefl 0 hDpos
  -- the exact identity `H/(1+ζH) = H − ζH²/(1+ζH)`
  have hsum : H / (1 + ζ * H) + ζ * H ^ 2 / (1 + ζ * H) = H := by
    rw [← add_div]
    rw [show H + ζ * H ^ 2 = H * (1 + ζ * H) by ring]
    exact mul_div_cancel_right₀ H hDne
  have hHdiv : H / (1 + ζ * H) = H - ζ * H ^ 2 / (1 + ζ * H) := by
    rw [eq_sub_iff_add_eq]
    exact hsum
  -- the correction is at most `2t + 35t²`
  have hnorm : ‖ζ * H ^ 2 / (1 + ζ * H)‖ ≤ 2 * t + 35 * t ^ 2 := by
    rw [norm_div, norm_mul, norm_pow]
    have hnum : ‖ζ‖ * ‖H‖ ^ 2 ≤ t * (1 + (B * t + A * t ^ 2)) ^ 2 := by
      have h2 : ‖H‖ ^ 2 ≤ (1 + (B * t + A * t ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg H) hHn 2
      exact mul_le_mul hζ h2 (sq_nonneg _) ht0
    have hsq : (1 + (B * t + A * t ^ 2)) ^ 2 ≤ 121 / 64 := by
      nlinarith [h1g, hg0]
    calc ‖ζ‖ * ‖H‖ ^ 2 / ‖1 + ζ * H‖
        ≤ t * (1 + (B * t + A * t ^ 2)) ^ 2 / ‖1 + ζ * H‖ :=
          div_le_div_of_nonneg_right hnum hDpos.le
      _ ≤ t * (1 + (B * t + A * t ^ 2)) ^ 2 / (245 / 256) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hD
      _ ≤ 2 * t + 35 * t ^ 2 := by
          have hstep : t * (1 + (B * t + A * t ^ 2)) ^ 2 / (245 / 256)
              ≤ t * (121 / 64) / (245 / 256) := by
            apply div_le_div_of_nonneg_right _ (by norm_num)
            exact mul_le_mul_of_nonneg_left hsq ht0
          have hfinal : t * (121 / 64) / (245 / 256) ≤ 2 * t + 35 * t ^ 2 := by
            rw [show t * (121 / 64) / (245 / 256) = t * (484 / 245) by ring]
            nlinarith [ht0, sq_nonneg t]
          linarith
  -- real part of the difference
  have heq : H / (1 + ζ * H) - τ = (H - τ) - ζ * H ^ 2 / (1 + ζ * H) := by
    rw [hHdiv]
    ring
  have h1 : ((H - τ) - ζ * H ^ 2 / (1 + ζ * H)).re
      ≤ ‖H - τ‖ + ‖ζ * H ^ 2 / (1 + ζ * H)‖ := by
    have hsub := Complex.sub_re (H - τ) (ζ * H ^ 2 / (1 + ζ * H))
    have hx : (H - τ).re ≤ ‖H - τ‖ := Complex.re_le_norm _
    have hy : -(ζ * H ^ 2 / (1 + ζ * H)).re ≤ ‖ζ * H ^ 2 / (1 + ζ * H)‖ :=
      le_trans (neg_le_abs _) (Complex.abs_re_le_norm _)
    linarith
  have h2 : ‖H - τ‖ + ‖ζ * H ^ 2 / (1 + ζ * H)‖
      ≤ (B * t + A * t ^ 2) + (2 * t + 35 * t ^ 2) := add_le_add hHτ hnorm
  have hRe : (H / (1 + ζ * H) - τ).re ≤ (B + 2) * t + A * t ^ 2 + 35 * t ^ 2 := by
    rw [heq]
    nlinarith [h1, h2]
  have hτre : τ.re ≤ 1 := by
    have h := Complex.re_le_norm τ
    linarith
  have hsub := Complex.sub_re (H / (1 + ζ * H)) τ
  nlinarith [hRe, hτre, hsub]

/-- **The real part of the model displacement is bounded below by `-1 - O(λ² + ‖ζ‖)`.**

For `a = iλ` with `λR² ≤ 1`, `R ≥ 128`, a germ `h` with `ParBounds h τ h₁ A r`,
`‖h₁‖ ≤ B`, `‖τ − 1‖ ≤ 1/8` and `4B/R + 16A/R² ≤ 3/8`, and a point `u` whose Écalle point
`ζ(u) = ecalPt (iλ) u` is small (`‖ζ(u)‖ ≤ 4/R`, `‖ζ(u)‖ < r`),

  `Re Φ ≥ -1 - 35λ² - (B+2)‖ζ(u)‖ - (A+35)‖ζ(u)‖²`,  where `Φ = modelDisp (iλ) h u`. -/
theorem modelDisp_re_ge (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (h : ℂ → ℂ) (τ h1 : ℂ) (A r B : ℝ) (hA : 0 ≤ A) (hr : 0 < r)
    (hb : Work.PARIMPL.ParBounds h τ h1 A r) (hh1 : ‖h1‖ ≤ B) (hτ1 : ‖τ - 1‖ ≤ 1 / 8)
    (hAr : 4 * B / R + 16 * A / R ^ 2 ≤ 3 / 8)
    (hτpi : (Real.pi / lam) * ‖τ - 1‖ ≤ 1 / (8 * R)) (hrr : 16 ≤ R * r)
    (u : ℂ) (hzn : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ≤ 4 / R)
    (hzr : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ < r) :
    -1 - 35 * lam ^ 2 - (B + 2) * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖
      - (A + 35) * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ^ 2
      ≤ (Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).re := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hB0 : 0 ≤ B := le_trans (norm_nonneg h1) hh1
  set a : ℂ := (lam : ℂ) * Complex.I with ha
  set ζ : ℂ := Work.Implosion.ecalPt a u with hζa
  set H : ℂ := h ζ with hHa
  set t : ℝ := ‖ζ‖ with htdef
  set Φ : ℂ := Work.Implosion.modelDisp a h u with hΦ
  set Q : ℂ := H / (1 + ζ * H) with hQ
  have hζn : ‖ζ‖ ≤ 4 / R := by rw [hζa, ha]; exact hzn
  have hζr : ‖ζ‖ < r := by rw [hζa, ha]; exact hzr
  have ht0 : 0 ≤ t := by rw [htdef]; exact norm_nonneg ζ
  -- `t ≤ 1/32`
  have ht32 : t ≤ 1 / 32 := by
    have h1 : (4 : ℝ) / R ≤ 1 / 32 := by
      rw [div_le_div_iff₀ hRpos (by norm_num : (0 : ℝ) < 32)]
      linarith
    rw [htdef]
    linarith
  -- `lam ≤ 1/32`
  have hlam32 : lam ≤ 1 / 32 := by
    have hR2 : (1024 : ℝ) ≤ R ^ 2 := by nlinarith [hR]
    have h1 : lam * 1024 ≤ lam * R ^ 2 := mul_le_mul_of_nonneg_left hR2 hlam.le
    have h2 : lam * 1024 ≤ 1 := by linarith [hlamR, h1]
    linarith
  -- the germ bounds
  have hHτ : ‖H - τ‖ ≤ B * t + A * t ^ 2 := by
    have hgerm : ‖H - τ - h1 * ζ‖ ≤ A * ‖ζ‖ ^ 2 := by
      rw [hHa]
      exact hb.2.2.1 ζ hζr
    have htri : ‖H - τ‖ ≤ ‖H - τ - h1 * ζ‖ + ‖h1 * ζ‖ := by
      have hh := norm_add_le (H - τ - h1 * ζ) (h1 * ζ)
      have heq : (H - τ - h1 * ζ) + h1 * ζ = H - τ := by ring
      rwa [heq] at hh
    have hmm : ‖h1 * ζ‖ ≤ B * t := by
      rw [norm_mul, htdef]
      exact mul_le_mul hh1 le_rfl (norm_nonneg ζ) hB0
    have hsq : A * ‖ζ‖ ^ 2 = A * t ^ 2 := by rw [htdef]
    linarith [htri, hgerm, hmm, hsq]
  have hg38 : B * t + A * t ^ 2 ≤ 3 / 8 := by
    have hBt : B * t ≤ 4 * B / R := by
      calc B * t = B * ‖ζ‖ := by rw [htdef]
        _ ≤ B * (4 / R) := mul_le_mul_of_nonneg_left hζn hB0
        _ = 4 * B / R := by ring
    have hAt : A * t ^ 2 ≤ 16 * A / R ^ 2 := by
      have ht2 : t ^ 2 ≤ (4 / R) ^ 2 := by
        rw [htdef]
        exact pow_le_pow_left₀ (norm_nonneg ζ) hζn 2
      calc A * t ^ 2 ≤ A * (4 / R) ^ 2 := mul_le_mul_of_nonneg_left ht2 hA
        _ = 16 * A / R ^ 2 := by ring
    linarith [hBt, hAt, hAr]
  have hH2 : ‖H‖ ≤ 2 := by
    rw [hHa]
    exact hb.2.2.2.1 ζ hζr
  -- the tight rational approximation of the displacement
  have hΦQ : ‖Φ + Q‖ ≤ 9 * lam ^ 2 := by
    have hh := norm_modelDisp_add_rational_le_tight lam hlam hlam32 h u
      (by simpa only [hζa, ha, htdef] using ht32)
      (by simpa only [hHa, hζa, ha] using hH2)
    simpa only [hΦ, hQ, hζa, hHa, ha] using hh
  -- the rational expression is bounded by `1 + (B+2)t + (A+35)t²`
  have hQre : Q.re ≤ 1 + (B + 2) * t + (A + 35) * t ^ 2 := by
    rw [hQ]
    exact re_div_one_add_mul_le τ H ζ B A t (le_of_eq hb.2.1) hHτ (le_of_eq htdef.symm)
      ht0 ht32 hB0 hA hg38
  -- assemble
  have hΦre : Φ.re = (Φ + Q).re - Q.re := by
    rw [Complex.add_re]
    ring
  have hlow : -‖Φ + Q‖ ≤ (Φ + Q).re := by
    have h := (abs_le.mp (Complex.abs_re_le_norm (Φ + Q))).1
    linarith
  have hbound : Φ.re ≥ -1 - 35 * lam ^ 2 - (B + 2) * t - (A + 35) * t ^ 2 := by
    rw [hΦre]
    nlinarith [hlow, hΦQ, hQre, sq_nonneg lam]
  simpa only [ha, hΦ, hζa, htdef] using hbound

end Work.PARIMPL2.Direct
