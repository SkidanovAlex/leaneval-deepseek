import Mathlib
import Submission.Work.FlowerGlue2.rep_norm_transfer_stolz
import Submission.Work.FlowerGlue2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue2.repNorm_of_diag_inverse`

The repelling normalisation `RepNorm` for the transfer form `Ψ w = d.z₁ + P.s c₀ * (-1 / V w)`,
obtained from the **diagonal** inverse hypothesis on `V`
(`Work.FlowerGlue2.exists_rep_inverse_diag`) rather than the strong half-plane one
(`Work.FlowerGlue2.exists_rep_inverse_stolz`).  The estimate is the estimate section of
`Work.FlowerGlue2.rep_norm_transfer_stolz`, with `sh = 0` and the single inverse call replaced by
the diagonal one at `R₁ := R/2 - 2`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

open Filter Set Metric
open scoped Topology

namespace Work.FlowerGlue2

open Work.PARIMPL (ParNormal)

noncomputable section

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- Elementary bounds of the `c₀`-chart coordinate on the outgoing geometric window:
on `WoutG P R H` (with `H ≥ 0`) one has `R ≤ ‖w0 P z‖ ≤ R + H + 2`. -/
private lemma w0_bounds_diag {P : Work.PARIMPL.ParNormal d}
    {R H : ℝ} (hR : 0 < R) (hH : 0 ≤ H) {z : ℂ} (hz : z ∈ WoutG P R H) :
    R ≤ ‖w0 P z‖ ∧ ‖w0 P z‖ ≤ R + H + 2 := by
  obtain ⟨hz1, hre, him⟩ := hz
  obtain ⟨hre1, hre2⟩ := hre
  have habs : |(w0 P z).re| ≤ R + 2 := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  refine ⟨?_, ?_⟩
  · calc R ≤ -(w0 P z).re := by linarith
      _ ≤ |(w0 P z).re| := neg_le_abs _
      _ ≤ ‖w0 P z‖ := Complex.abs_re_le_norm _
  · have hsq : ‖w0 P z‖ ^ 2 ≤ (R + H + 2) ^ 2 := by
      have h1 : (w0 P z).re ^ 2 ≤ (R + 2) ^ 2 := by
        have hb := abs_le.mp habs
        nlinarith [hb.1, hb.2, hR]
      have h2 : (w0 P z).im ^ 2 ≤ H ^ 2 := by
        have hb := abs_le.mp him
        nlinarith [hb.1, hb.2, hH]
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith [hre2, h1, h2, hR, hH]
    nlinarith [hsq, norm_nonneg (w0 P z), hre2, him, abs_nonneg (w0 P z).im, hR, hH]

/-
## The repelling normalisation `RepNorm` for the transfer form, from the **diagonal** inverse

`Work.FlowerGlue2.rep_norm_transfer_stolz` proves
`Work.PARIMPL2.Lavaurs.RepNorm P Ψ` for the transfer form
`Ψ w = d.z₁ + P.s c₀ * (-1 / V (w + sh))`, from an inverse hypothesis on `V` of the
*undesirably strong* shape `∀ w, w.re < -R₀ → … → ∃ v, v.re < -R₀ ∧ V v = w ∧ …`: the preimage
of a point at depth `-Re w = R₀ + ε` is provably only at depth
`≈ -R₀ - ε - Re(1-a) log R₀`, which is *not* `< -R₀` when `Re (1-a) < 0`.

This statement replaces it by the diagonal shape delivered by
`Work.FlowerGlue2.exists_rep_inverse_diag`: the preimage is required only when `-Re w` is at
least `2R₁` (twice the depth wanted for the preimage) and at least the absolute threshold `R₀`,
with `R₀ - 3 ≤ R₁`.  In `RepNorm` one takes `R₁ := R/2 - 2` for a window point of depth
`-Re w ∈ [R, R+2]`: the hypotheses become `R - 4 ≤ -Re w` (true) and `R₀, 2R₀ - 2 ≤ R` (true for
`R` beyond the new threshold `N`), and the conclusion `v.re < -R₁ - 2 = -R/2` is exactly the
depth required of the level.

The proof is the estimate section of `Work.FlowerGlue2.rep_norm_transfer_stolz` with `sh := 0`, the
single call to the old inverse hypothesis replaced by the diagonal one at `R₁ := R/2 - 2`, the
thresholds `N := max (2R₀) (max (16/7) 4)`, the model constant `sr := -(1 - P.h1 c₀) * (π i)` and
`K := K₀ (1 + log 2)`; the error conversion
`(1 + log ‖w0 P z‖)/‖w0 P z‖ ≤ (1 + log 2)(1 + H)(1 + log R)/R` (using
`‖w0 P z‖ ≤ R + H + 2 ≤ 2R` and `H ≤ R/8`) is verbatim that of the existing proof, as is the
identity `approxCoordRep κ w + sr = w - κ Λ w` for `κ = P.κ c₀ = 1 - P.h1 c₀` (which uses
`hτ : P.h c₀ 0 = 1`); the step `Ψ v = z` for `v` with `V v = w0 P z` uses
`Work.FlowerGlue2.chart_recovery` (`z = d.z₁ - P.s c₀ / w0 P z`).
-/
theorem repNorm_of_diag_inverse {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (P : Work.PARIMPL.ParNormal d) (hτ : P.h c₀ 0 = 1)
    {V : ℂ → ℂ} {R₀ K₀ : ℝ} (hR₀ : 0 < R₀) (hK₀ : 0 < K₀)
    (hVinv : ∀ R₁ : ℝ, ∀ w : ℂ, R₀ - 3 ≤ R₁ → 2 * R₁ ≤ -w.re → R₀ ≤ -w.re →
      |w.im| < -w.re + 1 →
      ∃ v : ℂ, v.re < -R₁ - 2 ∧ V v = w ∧
        ‖v - (w - (1 - P.h1 c₀) * Work.FatouCoord.Petal.Lambda w)‖
          ≤ K₀ * (1 + Real.log ‖w‖) / ‖w‖) :
    Work.PARIMPL2.Lavaurs.RepNorm P (fun w => d.z₁ + P.s c₀ * (-1 / V w)) := by
  have hs : P.s c₀ ≠ 0 := P.s_ne c₀ (mem_ball_self P.hρ₀)
  have hκ : P.κ c₀ = 1 - P.h1 c₀ := by
    have h := (P.κ_eq c₀ (mem_ball_self P.hρ₀)).2
    rw [hτ] at h
    simpa using h
  show ∃ sr : ℂ, ∃ N K : ℝ, 0 < N ∧ 0 ≤ K ∧
      ∀ R ≥ N, ∀ H : ℝ, R ≥ 8 * (H + 1) → ∀ z ∈ WoutG P R H,
        ∃ u : ℂ, u.re < -(R / 2) ∧ (fun w => d.z₁ + P.s c₀ * (-1 / V w)) u = z ∧
          ‖u - (approxCoordRep (P.κ c₀) (w0 P z) + sr)‖
            ≤ K * (1 + H) * (1 + Real.log R) / R
  refine ⟨-(1 - P.h1 c₀) * ((Real.pi : ℂ) * Complex.I),
    max (2 * R₀) (max (16 / 7) 4), K₀ * (1 + Real.log 2), ?_, ?_, ?_⟩
  · have h1 : (16:ℝ)/7 ≤ max (2 * R₀) (max (16/7) 4) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    linarith
  · have h2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith [hK₀.le, h2]
  · intro R hR H hRH z hz
    have hNR₀ : 2 * R₀ ≤ R := le_trans (le_max_left _ _) hR
    have hN167 : (16:ℝ)/7 ≤ R :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hR)
    have hN4 : (4:ℝ) ≤ R :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hR)
    have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hN167
    have hHnn : 0 ≤ H := le_trans (abs_nonneg _) hz.2.2
    have hHle : H ≤ R / 8 := by linarith
    have hwre : (w0 P z).re ≤ -R := hz.2.1.2
    have hwstolz : |(w0 P z).im| < -(w0 P z).re + 1 := by
      have h1 : |(w0 P z).im| ≤ H := hz.2.2
      have h2 : R / 8 < R + 1 := by linarith
      linarith
    have hR₀₃ : R₀ - 3 ≤ R / 2 - 2 := by linarith
    have h2R₁ : 2 * (R / 2 - 2) ≤ -(w0 P z).re := by linarith
    have hR₀le : R₀ ≤ -(w0 P z).re := by linarith
    obtain ⟨v, hv1, hv2, hv3⟩ := hVinv (R / 2 - 2) (w0 P z) hR₀₃ h2R₁ hR₀le hwstolz
    have hwb := w0_bounds_diag hRpos hHnn hz
    have hRnorm : R ≤ ‖w0 P z‖ := hwb.1
    have hnormupper : ‖w0 P z‖ ≤ R + H + 2 := hwb.2
    have h2R : ‖w0 P z‖ ≤ 2 * R := by linarith
    have hnormpos : 0 < ‖w0 P z‖ := lt_of_lt_of_le hRpos hRnorm
    have hnormterm : K₀ * (1 + Real.log ‖w0 P z‖) / ‖w0 P z‖
        ≤ K₀ * (1 + Real.log (2 * R)) / R := by
      have hlog_le : Real.log ‖w0 P z‖ ≤ Real.log (2 * R) := Real.log_le_log hnormpos h2R
      have hlog_nn : 0 ≤ Real.log ‖w0 P z‖ := Real.log_nonneg (by linarith)
      have hnum_nn : 0 ≤ 1 + Real.log ‖w0 P z‖ := by linarith
      have hnum_le : 1 + Real.log ‖w0 P z‖ ≤ 1 + Real.log (2 * R) := by linarith
      have hcnn : 0 ≤ 1 + Real.log (2 * R) := by
        have := Real.log_nonneg (show (1:ℝ) ≤ 2 * R by linarith)
        linarith
      have hdiv : (1 + Real.log ‖w0 P z‖) / ‖w0 P z‖ ≤ (1 + Real.log (2 * R)) / R :=
        div_le_div₀ hcnn hnum_le hRpos hRnorm
      calc K₀ * (1 + Real.log ‖w0 P z‖) / ‖w0 P z‖
          = K₀ * ((1 + Real.log ‖w0 P z‖) / ‖w0 P z‖) := by ring
        _ ≤ K₀ * ((1 + Real.log (2 * R)) / R) := mul_le_mul_of_nonneg_left hdiv hK₀.le
        _ = K₀ * (1 + Real.log (2 * R)) / R := by ring
    have hReu : v.re < -(R / 2) := by
      have h : -(R / 2 - 2) - 2 = -(R / 2) := by ring
      linarith
    refine ⟨v, hReu, ?_, ?_⟩
    · show d.z₁ + P.s c₀ * (-1 / V v) = z
      rw [hv2]
      have hzd : z - d.z₁ ≠ 0 := sub_ne_zero.mpr hz.1
      rw [w0_apply]
      field_simp
      ring
    · have hkey : v - (approxCoordRep (P.κ c₀) (w0 P z)
            + (-(1 - P.h1 c₀) * ((Real.pi : ℂ) * Complex.I)))
          = v - (w0 P z - (1 - P.h1 c₀) * Work.FatouCoord.Petal.Lambda (w0 P z)) := by
        rw [approxCoordRep_apply, Work.FatouCoord.Petal.Lambda_apply, hκ]
        ring
      rw [hkey]
      calc ‖v - (w0 P z - (1 - P.h1 c₀) * Work.FatouCoord.Petal.Lambda (w0 P z))‖
          ≤ K₀ * (1 + Real.log ‖w0 P z‖) / ‖w0 P z‖ := hv3
        _ ≤ K₀ * (1 + Real.log (2 * R)) / R := hnormterm
        _ ≤ K₀ * (1 + Real.log 2) * (1 + H) * (1 + Real.log R) / R := by
            have hR1 : 1 ≤ R := by linarith
            have hlogR_nn : 0 ≤ Real.log R := Real.log_nonneg hR1
            have hlog2_nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
            have hsplit : Real.log (2 * R) = Real.log 2 + Real.log R :=
              Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hRpos)
            have hnum1 : 1 + Real.log (2 * R) ≤ (1 + Real.log 2) * (1 + Real.log R) := by
              rw [hsplit]
              nlinarith [hlog2_nn, hlogR_nn, mul_nonneg hlog2_nn hlogR_nn]
            have hnum2 : (1 + Real.log 2) * (1 + Real.log R)
                ≤ (1 + Real.log 2) * (1 + H) * (1 + Real.log R) := by
              nlinarith [hlog2_nn, hlogR_nn, hHnn]
            have hA : K₀ * (1 + Real.log (2 * R)) / R
                ≤ K₀ * ((1 + Real.log 2) * (1 + Real.log R)) / R :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum1 hK₀.le) hRpos.le
            have hB : K₀ * ((1 + Real.log 2) * (1 + Real.log R)) / R
                ≤ K₀ * ((1 + Real.log 2) * (1 + H) * (1 + Real.log R)) / R :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum2 hK₀.le) hRpos.le
            simpa only [mul_assoc] using le_trans hA hB

end

end Work.FlowerGlue2
