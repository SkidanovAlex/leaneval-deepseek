import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.Implosion.Approx
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL2.Direct.norm_modelDisp_add_rational_le

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

/-- Arithmetic endgame of `disp_im_split`: with `ρ ≤ 4/R`, `R ≥ 128` and the germ
constraint `4B/R + 16A/R² ≤ 3/8`, the quadratic remainder `u + v` (`u = Bρ`,
`v = Aρ²`) satisfies the advertised bound. -/
private lemma arith_disp_im (A B R ρ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 128 ≤ R)
    (hρ0 : 0 ≤ ρ) (hρR : ρ ≤ 4 / R) (hAr : 4 * B / R + 16 * A / R ^ 2 ≤ 3 / 8) :
    (16 / 15) * ρ * (2 * (B * ρ) + 2 * (A * ρ ^ 2) + ρ + (B * ρ + A * ρ ^ 2) ^ 2
        + ρ * (B * ρ + A * ρ ^ 2))
      ≤ (9 / 4) * A * ρ ^ 3 + (33 / 10) * B * ρ ^ 2 + (11 / 5) * ρ ^ 2
          + (3 / R) * A * ρ ^ 2 := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hR2pos : (0 : ℝ) < R ^ 2 := by positivity
  set u : ℝ := B * ρ with hu
  set v : ℝ := A * ρ ^ 2 with hv
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have hρR' : ρ * R ≤ 4 := by
    rw [le_div_iff₀ hRpos] at hρR
    linarith
  have hu_le : u ≤ 4 * B / R := by
    rw [hu, le_div_iff₀ hRpos]
    nlinarith [hρR', hB, hρ0]
  have hv_le : v ≤ 16 * A / R ^ 2 := by
    have hρ2 : ρ ^ 2 ≤ 16 / R ^ 2 := by
      rw [le_div_iff₀ hR2pos]
      have hρRR : (0 : ℝ) ≤ ρ * R := mul_nonneg hρ0 hRpos.le
      have h1 : (ρ * R) ^ 2 ≤ 16 := by nlinarith [hρR']
      rwa [mul_pow] at h1
    calc v = A * ρ ^ 2 := hv
      _ ≤ A * (16 / R ^ 2) := mul_le_mul_of_nonneg_left hρ2 hA
      _ = 16 * A / R ^ 2 := by ring
  have huv : u + v ≤ 3 / 8 := by linarith
  have hρ32 : ρ ≤ 1 / 32 := by
    have h1 : (4 : ℝ) / R ≤ 4 / 128 := by
      rw [div_le_div_iff₀ hRpos (by norm_num : (0:ℝ) < 128)]; linarith
    linarith
  have hkey1 : (u + v) ^ 2 ≤ (3 / 8) * (u + v) := by nlinarith [huv, hu0, hv0]
  have hkey2 : ρ * (u + v) ≤ (1 / 32) * (u + v) := by nlinarith [hρ32, hu0, hv0]
  have hkey3 : (77 / 30) * v * ρ ≤ (9 / 4) * v * ρ + (3 / R) * v := by
    have hvρR : v * (ρ * R) ≤ 4 * v := by nlinarith [hρR', hv0]
    have : (19 / 60) * v * ρ ≤ (3 / R) * v := by
      rw [show (3 / R) * v = 3 * v / R by ring, le_div_iff₀ hRpos]
      nlinarith [hvρR, hv0]
    linarith
  have hexp : (16 / 15) * ρ * (2 * u + 2 * v + ρ + (3 / 8) * (u + v) + (1 / 32) * (u + v))
      = (77 / 30) * u * ρ + (77 / 30) * v * ρ + (16 / 15) * ρ ^ 2 := by ring
  calc (16 / 15) * ρ * (2 * (B * ρ) + 2 * (A * ρ ^ 2) + ρ + (B * ρ + A * ρ ^ 2) ^ 2
        + ρ * (B * ρ + A * ρ ^ 2))
      = (16 / 15) * ρ * (2 * u + 2 * v + ρ + (u + v) ^ 2 + ρ * (u + v)) := by rw [hu, hv]
    _ ≤ (16 / 15) * ρ * (2 * u + 2 * v + ρ + (3 / 8) * (u + v) + (1 / 32) * (u + v)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [hkey1, hkey2]
    _ = (77 / 30) * u * ρ + (77 / 30) * v * ρ + (16 / 15) * ρ ^ 2 := hexp
    _ ≤ (9 / 4) * v * ρ + (33 / 10) * u * ρ + (11 / 5) * ρ ^ 2 + (3 / R) * v := by
        have h1 : (77 / 30) * u * ρ ≤ (33 / 10) * u * ρ := by nlinarith [hu0, hρ0]
        have h3 : (16 / 15) * ρ ^ 2 ≤ (11 / 5) * ρ ^ 2 := by nlinarith [hρ0]
        linarith [h1, hkey3, h3]
    _ = (9 / 4) * A * ρ ^ 3 + (33 / 10) * B * ρ ^ 2 + (11 / 5) * ρ ^ 2
          + (3 / R) * A * ρ ^ 2 := by rw [hu, hv]; ring

/-!
# The split imaginary part of the model displacement

With `a = i·λ`, `ζ = ecalPt a u`, `H = h ζ`, `Φ = modelDisp a h u`, the left-hand side of
`disp_im_split` is exactly the imaginary part of the single complex number

  `Φ + H − τ²ζ`

(expand `((h₁ − τ²)ζ).im` and `(H − τ − h₁ζ).im`; the explicit `τ.im` cancels).  The proof
splits off the *exact* second-order part by the algebraic identity

  `Φ + H − τ²ζ = (Φ + H/(1 + ζH)) + ζ(H² − τ²(1 + ζH))/(1 + ζH)`,

estimates the first summand by `‖Φ + H/(1+ζH)‖ ≤ 100λ²` (`norm_modelDisp_add_rational_le`,
the exact second-order expansion of the displacement in the `λ`-direction), and the second
summand — the quadratic remainder of the germ, with `δ = H − τ`, `‖δ‖ ≤ ‖h₁‖ρ + Aρ²`,
`‖H + τ‖ ≤ 2 + ‖δ‖`, `‖H‖ ≤ 1 + ‖δ‖` and `‖1 + ζH‖ ≥ 15/16` — by the arithmetic endgame
`arith_disp_im` above.  No `λ²`-term of the germ remainder is needed: the germ remainder
sits *inside* the absolute value, where it combines with the exact expansion.
-/

/-- **The per-step imaginary error, in the split form consumed by the orbit drift.** -/
theorem disp_im_split (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (h : ℂ → ℂ) (τ h1 : ℂ) (A r B : ℝ) (hA : 0 ≤ A) (hr : 0 < r)
    (hb : Work.PARIMPL.ParBounds h τ h1 A r) (hh1 : ‖h1‖ ≤ B) (hτ1 : ‖τ - 1‖ ≤ 1 / 8)
    (hAr : 4 * B / R + 16 * A / R ^ 2 ≤ 3 / 8) (hrr : 16 ≤ R * r)
    (u : ℂ) (hz : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ≤ 4 / R)
    (hzr : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ < r) :
    |(Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).im + τ.im
        + (h1 - τ ^ 2).im * (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u).re
        + (h1 - τ ^ 2).re * (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u).im
        + (h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u) - τ
            - h1 * Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u).im|
      ≤ 100 * lam ^ 2 + (9 / 4) * A * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ^ 3
        + (33 / 10) * ‖h1‖ * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ^ 2
        + (11 / 5) * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ^ 2
        + (3 / R) * A * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ^ 2 := by
  have hRpos : (0 : ℝ) < R := by linarith
  set a : ℂ := (lam : ℂ) * Complex.I with ha
  set ζ : ℂ := Work.Implosion.ecalPt a u with hζ
  set H : ℂ := h ζ with hH
  set Φ : ℂ := Work.Implosion.modelDisp a h u with hΦ
  have hζ' : Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u = ζ := rfl
  have hH' : h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u) = H := rfl
  have hΦ' : Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u = Φ := rfl
  have hρ : ‖ζ‖ ≤ 4 / R := hz
  have hρ0 : 0 ≤ ‖ζ‖ := norm_nonneg ζ
  have hζr : ‖ζ‖ < r := hzr
  have hH2 : ‖H‖ ≤ 2 := hb.2.2.2.1 ζ hζr
  have hε : ‖H - τ - h1 * ζ‖ ≤ A * ‖ζ‖ ^ 2 := hb.2.2.1 ζ hζr
  have hτn : ‖τ‖ = 1 := hb.2.1
  -- numerical size of `lam` and of `ζ`
  have hlam_le : lam ≤ 1 / 8 := by
    have h1 : lam ≤ 1 / R ^ 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < R ^ 2)]; linarith
    have h2 : (1 : ℝ) / R ^ 2 ≤ 1 / 8 := by
      apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8); nlinarith
    linarith
  have hρ32 : ‖ζ‖ ≤ 1 / 32 := by
    have h1 : (4 : ℝ) / R ≤ 4 / 128 := by
      rw [div_le_div_iff₀ hRpos (by norm_num : (0 : ℝ) < 128)]; linarith
    linarith
  have hρ14 : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ≤ 1 / 4 := by
    rw [hζ']; linarith
  -- the exact second-order estimate on the displacement
  have hfirst : ‖Φ + H / (1 + ζ * H)‖ ≤ 100 * lam ^ 2 := by
    have h := norm_modelDisp_add_rational_le lam hlam hlam_le h u hρ14 (by rw [hH']; exact hH2)
    simpa [hΦ, hζ, hH, ha] using h
  -- `1 + ζH` is invertible, with `‖(1+ζH)⁻¹‖ ≤ 16/15`
  have hζH : ‖ζ * H‖ ≤ 1 / 16 := by
    rw [norm_mul]
    calc ‖ζ‖ * ‖H‖ ≤ (1 / 32) * 2 :=
          mul_le_mul hρ32 hH2 (norm_nonneg H) (by norm_num)
      _ = 1 / 16 := by norm_num
  have hc_ge : (15 : ℝ) / 16 ≤ ‖1 + ζ * H‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (-(ζ * H))
    rw [norm_neg, norm_one, sub_neg_eq_add] at h
    linarith
  have hcpos : (0 : ℝ) < ‖1 + ζ * H‖ := by linarith
  have hinv : (‖1 + ζ * H‖)⁻¹ ≤ 16 / 15 := by
    have h := (inv_le_inv₀ hcpos (by norm_num : (0 : ℝ) < 15 / 16)).mpr hc_ge
    rwa [show ((15 : ℝ) / 16)⁻¹ = 16 / 15 by norm_num] at h
  -- sizes of the quadratic error terms
  set uu : ℝ := ‖h1‖ * ‖ζ‖ with huu
  set vv : ℝ := A * ‖ζ‖ ^ 2 with hvv
  have hu0 : 0 ≤ uu := by rw [huu]; positivity
  have hv0 : 0 ≤ vv := by rw [hvv]; positivity
  have hδ : ‖H - τ‖ ≤ uu + vv := by
    have hEq : H - τ = (H - τ - h1 * ζ) + h1 * ζ := by ring
    calc ‖H - τ‖ = ‖(H - τ - h1 * ζ) + h1 * ζ‖ := congrArg Norm.norm hEq
      _ ≤ ‖H - τ - h1 * ζ‖ + ‖h1 * ζ‖ := norm_add_le _ _
      _ ≤ A * ‖ζ‖ ^ 2 + ‖h1‖ * ‖ζ‖ := by
          rw [norm_mul]; exact add_le_add hε le_rfl
      _ = uu + vv := by rw [huu, hvv]; ring
  have hN : ‖H ^ 2 - τ ^ 2 * (1 + ζ * H)‖
      ≤ 2 * (uu + vv) + (uu + vv) ^ 2 + ‖ζ‖ * (1 + (uu + vv)) := by
    have hHplus' : ‖H + τ‖ ≤ ‖H - τ‖ + 2 := by
      have hEq : H + τ = (H - τ) + 2 * τ := by ring
      calc ‖H + τ‖ = ‖(H - τ) + 2 * τ‖ := congrArg Norm.norm hEq
        _ ≤ ‖H - τ‖ + ‖2 * τ‖ := norm_add_le _ _
        _ = ‖H - τ‖ + 2 := by rw [norm_mul, hτn]; norm_num
    have hHplus : ‖H + τ‖ ≤ 2 + ‖H - τ‖ := by linarith
    have hHle : ‖H‖ ≤ 1 + ‖H - τ‖ := by
      have hEq : H = τ + (H - τ) := by ring
      calc ‖H‖ = ‖τ + (H - τ)‖ := congrArg Norm.norm hEq
        _ ≤ ‖τ‖ + ‖H - τ‖ := norm_add_le _ _
        _ = 1 + ‖H - τ‖ := by rw [hτn]
    have hstep : ‖H ^ 2 - τ ^ 2 * (1 + ζ * H)‖
        ≤ ‖H - τ‖ * (2 + ‖H - τ‖) + ‖ζ‖ * (1 + ‖H - τ‖) := by
      have hId : H ^ 2 - τ ^ 2 * (1 + ζ * H) = (H - τ) * (H + τ) - τ ^ 2 * (ζ * H) := by
        ring
      have h1 : ‖(H - τ) * (H + τ)‖ ≤ ‖H - τ‖ * (2 + ‖H - τ‖) :=
        calc ‖(H - τ) * (H + τ)‖ = ‖H - τ‖ * ‖H + τ‖ := norm_mul _ _
          _ ≤ ‖H - τ‖ * (2 + ‖H - τ‖) := mul_le_mul_of_nonneg_left hHplus (norm_nonneg _)
      have h2 : ‖τ ^ 2 * (ζ * H)‖ ≤ 1 * (‖ζ‖ * ‖H‖) := by
        rw [norm_mul, norm_pow, hτn, norm_mul]
        norm_num
      have h3 : ‖ζ‖ * ‖H‖ ≤ ‖ζ‖ * (1 + ‖H - τ‖) :=
        mul_le_mul_of_nonneg_left hHle (norm_nonneg ζ)
      calc ‖H ^ 2 - τ ^ 2 * (1 + ζ * H)‖ = ‖(H - τ) * (H + τ) - τ ^ 2 * (ζ * H)‖ :=
            congrArg Norm.norm hId
        _ ≤ ‖(H - τ) * (H + τ)‖ + ‖τ ^ 2 * (ζ * H)‖ := norm_sub_le _ _
        _ ≤ ‖H - τ‖ * (2 + ‖H - τ‖) + ‖ζ‖ * (1 + ‖H - τ‖) := by linarith
    have hd0 : 0 ≤ ‖H - τ‖ := norm_nonneg _
    have huv0 : 0 ≤ uu + vv := by linarith
    nlinarith [hstep, hδ, hd0, hu0, hv0, hρ0]
  -- the second-order remainder, after division by `1 + ζH`
  have hsecond : ‖ζ * (H ^ 2 - τ ^ 2 * (1 + ζ * H)) / (1 + ζ * H)‖
      ≤ (16 / 15) * (‖ζ‖ * (2 * (uu + vv) + (uu + vv) ^ 2 + ‖ζ‖ * (1 + (uu + vv)))) := by
    rw [norm_div, norm_mul, div_eq_mul_inv]
    have h1 : ‖ζ‖ * ‖H ^ 2 - τ ^ 2 * (1 + ζ * H)‖
        ≤ ‖ζ‖ * (2 * (uu + vv) + (uu + vv) ^ 2 + ‖ζ‖ * (1 + (uu + vv))) :=
      mul_le_mul_of_nonneg_left hN (norm_nonneg ζ)
    have h2 := mul_le_mul h1 hinv (by positivity) (by positivity)
    calc ‖ζ‖ * ‖H ^ 2 - τ ^ 2 * (1 + ζ * H)‖ * (‖1 + ζ * H‖)⁻¹
        ≤ (‖ζ‖ * (2 * (uu + vv) + (uu + vv) ^ 2 + ‖ζ‖ * (1 + (uu + vv))))
            * (16 / 15) := h2
      _ = (16 / 15) * (‖ζ‖ * (2 * (uu + vv) + (uu + vv) ^ 2 + ‖ζ‖ * (1 + (uu + vv)))) := by
            ring
  -- the exact decomposition of `Φ + H - τ²ζ`
  have hcne : (1 + ζ * H) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hc_ge; norm_num at hc_ge
  have hident : Φ + H - τ ^ 2 * ζ
      = (Φ + H / (1 + ζ * H)) + ζ * (H ^ 2 - τ ^ 2 * (1 + ζ * H)) / (1 + ζ * H) := by
    have hcombine : (Φ + H / (1 + ζ * H)) + ζ * (H ^ 2 - τ ^ 2 * (1 + ζ * H)) / (1 + ζ * H)
        = Φ + (H + ζ * (H ^ 2 - τ ^ 2 * (1 + ζ * H))) / (1 + ζ * H) := by
      rw [add_assoc, ← add_div]
    have hnum : H + ζ * (H ^ 2 - τ ^ 2 * (1 + ζ * H)) = H * (1 + ζ * H) - τ ^ 2 * ζ * (1 + ζ * H) :=
      by ring
    rw [hcombine, hnum, sub_div, mul_div_cancel_right₀ _ hcne, mul_div_cancel_right₀ _ hcne]
    ring
  -- the imaginary part identity
  have him : (Φ).im + τ.im + (h1 - τ ^ 2).im * ζ.re + (h1 - τ ^ 2).re * ζ.im
      + (H - τ - h1 * ζ).im = (Φ + H - τ ^ 2 * ζ).im := by
    have h : Φ + H - τ ^ 2 * ζ = Φ + τ + (h1 - τ ^ 2) * ζ + (H - τ - h1 * ζ) := by ring
    rw [h]
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im]
    ring
  -- the arithmetic endgame
  have hAr' : 4 * ‖h1‖ / R + 16 * A / R ^ 2 ≤ 3 / 8 := by
    have h4 : 4 * ‖h1‖ / R ≤ 4 * B / R :=
      div_le_div_of_nonneg_right (by linarith [hh1]) hRpos.le
    linarith
  have harith := arith_disp_im A ‖h1‖ R ‖ζ‖ hA (norm_nonneg h1) hR hρ0 hρ hAr'
  have harith' : (16 / 15) * (‖ζ‖ * (2 * (uu + vv) + (uu + vv) ^ 2 + ‖ζ‖ * (1 + (uu + vv))))
      ≤ (9 / 4) * A * ‖ζ‖ ^ 3 + (33 / 10) * ‖h1‖ * ‖ζ‖ ^ 2 + (11 / 5) * ‖ζ‖ ^ 2
        + (3 / R) * A * ‖ζ‖ ^ 2 := by
    simp only [huu, hvv] at harith ⊢
    linarith [harith]
  calc |(Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h u).im + τ.im
        + (h1 - τ ^ 2).im * (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u).re
        + (h1 - τ ^ 2).re * (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u).im
        + (h (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u) - τ
            - h1 * Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u).im|
      = |(Φ + H - τ ^ 2 * ζ).im| := by
        rw [hΦ', hH', hζ']
        exact congrArg (fun t : ℝ => |t|) him
    _ ≤ ‖Φ + H - τ ^ 2 * ζ‖ := Complex.abs_im_le_norm _
    _ = ‖(Φ + H / (1 + ζ * H)) + ζ * (H ^ 2 - τ ^ 2 * (1 + ζ * H)) / (1 + ζ * H)‖ := by
        rw [hident]
    _ ≤ ‖Φ + H / (1 + ζ * H)‖ + ‖ζ * (H ^ 2 - τ ^ 2 * (1 + ζ * H)) / (1 + ζ * H)‖ :=
        norm_add_le _ _
    _ ≤ 100 * lam ^ 2
        + (16 / 15) * (‖ζ‖ * (2 * (uu + vv) + (uu + vv) ^ 2 + ‖ζ‖ * (1 + (uu + vv)))) :=
        add_le_add hfirst hsecond
    _ ≤ 100 * lam ^ 2 + (9 / 4) * A * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ^ 3
        + (33 / 10) * ‖h1‖ * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ^ 2
        + (11 / 5) * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ^ 2
        + (3 / R) * A * ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ^ 2 := by
        rw [hζ']
        linarith [harith']

end Work.PARIMPL2.Direct
