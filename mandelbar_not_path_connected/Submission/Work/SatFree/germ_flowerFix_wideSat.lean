import Mathlib
import Submission.Work.SatFree.Defs
import Submission.Work.SatFree.fatouCoordW_saturates_log
import Submission.Work.SatFree.backward_orbit
import Submission.Work.SatFree.backward_orbit_ge
import Submission.Work.SatFree.gU_sgauge_loss
import Submission.Work.SatFree.germ_flowerFix_wideSat_core
import Submission.Work.GATE2.PL.germ_parabolicFlowerFix_saturating

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.SatFree

noncomputable section

open Work.FatouCoord
open Work.FatouCoord.Flower

/-- Auxiliary: `Real.log x ≤ 2 * Real.sqrt x` for `x > 0`. -/
theorem log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h1 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  have h2 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h3 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos h2
  have h4 : Real.log x = 2 * Real.log (Real.sqrt x) := by linarith
  rw [h4]
  have h5 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  linarith

theorem SatHalfPlane_of_core {f gU h : ℂ → ℂ} {a : ℂ} {r A A' G₀ ρ : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') (hρ : 0 < ρ) (hρr : ρ ≤ r)
    (hgl : ∀ z : ℂ, ‖z‖ < ρ → ‖gU z - star z‖ ≤ G₀ * ‖z‖ ^ 2)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix f gU 0) (Ms Mh : ℝ) (s : ℂ)
    (hwide : ∀ u : ℂ, u ≠ 0 → Ms < Work.FatouCoord.Flower.sgauge (-1 / u) → u ∈ fl.Pa)
    (hφa_Pg : ∀ z ∈ Work.FatouCoordFix.HPlanePetal Mh,
        fl.φa z = Work.FatouCoord.fatouCoord f (1 - a) z + s) :
    SatHalfPlane gU fl.Pa fl.φa := by
  have hbρ : Work.FatouCoord.ParabolicBounds f h a ρ A A' :=
    Work.FatouCoordFix.FlowerFix.gpf_bounds_mono hb hρ hρr
  -- replace `Ms` and `Mh` by positive versions
  set Ms' : ℝ := max Ms 1 with hMs'def
  have hMs'pos : 0 < Ms' := lt_of_lt_of_le one_pos (le_max_right Ms 1)
  have hMs'ge : Ms ≤ Ms' := le_max_left Ms 1
  have hwide' : ∀ u : ℂ, u ≠ 0 → Ms' < Work.FatouCoord.Flower.sgauge (-1 / u) → u ∈ fl.Pa :=
    fun u hu h => hwide u hu (lt_of_le_of_lt hMs'ge h)
  set Mh' : ℝ := max Mh 0 with hMh'def
  have hMh'nn : 0 ≤ Mh' := le_max_right Mh 0
  have hφa_Pg' : ∀ z ∈ Work.FatouCoordFix.HPlanePetal Mh',
      fl.φa z = Work.FatouCoord.fatouCoord f (1 - a) z + s := by
    intro z hz
    apply hφa_Pg z
    simp only [Work.FatouCoordFix.mem_HPlanePetal] at hz ⊢
    exact ⟨hz.1, lt_of_le_of_lt (le_max_left Mh 0) hz.2⟩
  obtain ⟨X₁, K₁, hK₁, hS1⟩ := fatouCoordW_saturates_log (f := f) (h := h) (a := a) hbρ Mh'
  obtain ⟨M₀, Cb, hCb, hbwd⟩ := backward_orbit_ge (f := f) (h := h) (a := a) hbρ
  obtain ⟨Mg, Cg, hCg, hgloss⟩ := gU_sgauge_loss (gU := gU) (G₀ := G₀) (ρ := ρ) hρ hgl
  -- the landing threshold
  set M1 : ℝ := max Ms' (max Mg (Ms' + Cg)) with hM1def
  have hM1_Ms : Ms' ≤ M1 := by rw [hM1def]; exact le_max_left _ _
  have hM1_Mg : Mg ≤ M1 := by
    rw [hM1def]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hM1_sCg : Ms' + Cg ≤ M1 := by
    rw [hM1def]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  set Ml : ℝ := max (max M1 M₀) 1 + 2 with hMldef
  have hMl_M1 : M1 + 2 ≤ Ml := by
    rw [hMldef]; linarith [le_max_left (max M1 M₀) 1, le_max_left M1 M₀]
  have hMl_pos : 0 < Ml := by rw [hMldef]; linarith [le_max_right (max M1 M₀) 1]
  have hMl_Ms : Ms' < Ml := by linarith [hM1_Ms, hMl_M1]
  have hMl_Mg : Mg < Ml := by linarith [hM1_Mg, hMl_M1]
  have hMl_sCg : Ms' + Cg < Ml := by linarith [hM1_sCg, hMl_M1]
  have hMl_M₀ : M₀ ≤ Ml := by
    rw [hMldef]; linarith [le_max_left (max M1 M₀) 1, le_max_right M1 M₀]
  -- ## constants
  set K₂ : ℝ := K₁ + 1 with hK₂def
  have hK₂nn : 0 ≤ K₂ := by rw [hK₂def]; linarith
  set ss : ℝ := s.re + ‖s‖ with hssdef
  set D₁ : ℝ := Real.log (2 + 2 * K₂ + ‖s‖) with hD₁def
  have hD₁nn : 0 ≤ D₁ := by
    rw [hD₁def]
    apply Real.log_nonneg
    have h := norm_nonneg s
    linarith [hK₂nn]
  set Acoef : ℝ := (Cb - 1) * K₂ + 2 * K₁ with hAdef
  have hAcoef_nn : 0 ≤ Acoef := by
    rw [hAdef]
    have h1 : 0 ≤ Cb - 1 := by linarith
    have h2 : 0 ≤ (Cb - 1) * K₂ := mul_nonneg h1 hK₂nn
    linarith
  set Bcoef : ℝ := (Cb - 1) * K₂ + (Cb - 1) + ss + 2 * X₁ + 2 * K₁ * (D₁ + Real.pi) + Ml
    with hBdef
  set Ee : ℝ := max (Bcoef + 2) 0 with hEdef
  have hEe_nn : 0 ≤ Ee := le_max_right _ _
  have hEe_ge : Bcoef + 2 ≤ Ee := le_max_left _ _
  set Y₀ : ℝ := 2 * Acoef + Real.sqrt Ee + 1 with hYdef
  have hY_nn : 0 ≤ Y₀ := by
    rw [hYdef]; have h := Real.sqrt_nonneg Ee; linarith [hAcoef_nn]
  have hY_ge_2A : 2 * Acoef ≤ Y₀ := by
    rw [hYdef]; have h := Real.sqrt_nonneg Ee; linarith
  have hY_key : Ee ≤ Y₀ ^ 2 - 2 * Acoef * Y₀ := by
    have hse : 0 ≤ Real.sqrt Ee := Real.sqrt_nonneg Ee
    have hsq : Real.sqrt Ee ^ 2 = Ee := Real.sq_sqrt hEe_nn
    rw [hYdef]
    nlinarith [hse, hsq, hAcoef_nn]
  set X₂ : ℝ := Y₀ ^ 2 - 2 with hX₂def
  have hX₂_sqrt : Real.sqrt (2 + X₂) = Y₀ := by
    rw [hX₂def]
    have h2X : 2 + (Y₀ ^ 2 - 2) = Y₀ ^ 2 := by ring
    rw [h2X, Real.sqrt_sq_eq_abs, abs_of_nonneg hY_nn]
  set Xsat : ℝ := max (X₁ + K₁ * (D₁ + Real.pi) - K₁ - 1 + s.re + 1) (max X₂ 0)
    with hXsatdef
  refine ⟨Xsat, ?_⟩
  intro τ hτ
  have hXsat_a : X₁ + K₁ * (D₁ + Real.pi) - K₁ - 1 + s.re + 1 ≤ Xsat := by
    rw [hXsatdef]; exact le_max_left _ _
  have hXsat_b : X₂ ≤ Xsat := by
    rw [hXsatdef]; exact le_trans (le_max_left X₂ 0) (le_max_right _ _)
  have hXsat_nn : 0 ≤ Xsat := by
    rw [hXsatdef]; exact le_trans (le_max_right X₂ 0) (le_max_right _ _)
  have hτre_pos : 0 < τ.re := lt_of_le_of_lt hXsat_nn hτ
  set L : ℝ := ‖τ‖ with hLdef
  have hX₂_le_L : X₂ ≤ L := by
    rw [hLdef]
    exact le_trans hXsat_b (le_trans hτ.le (Complex.re_le_norm τ))
  set Ll : ℝ := Real.log (2 + L) with hLldef
  have hLl_nn : 0 ≤ Ll := by
    rw [hLldef]; apply Real.log_nonneg; rw [hLdef]; linarith [norm_nonneg τ]
  set m : ℕ := Nat.ceil (K₂ * (Ll + 1)) with hmdef
  have hm_ge : K₂ * (Ll + 1) ≤ (m : ℝ) := by rw [hmdef]; exact Nat.le_ceil _
  have hm_le : (m : ℝ) ≤ K₂ * (Ll + 1) + 1 := by
    rw [hmdef]; exact le_of_lt (Nat.ceil_lt_add_one (mul_nonneg hK₂nn (by linarith)))
  set τ' : ℂ := τ + (m : ℂ) - s with hτ'def
  have hτ're : τ'.re = τ.re + (m : ℝ) - s.re := by
    rw [hτ'def]; simp [Complex.add_re, Complex.sub_re, Complex.natCast_re]
  have hτ'im : τ'.im = τ.im - s.im := by
    rw [hτ'def]; simp [Complex.add_im, Complex.sub_im, Complex.natCast_im]
  -- the log bound
  have hlogA : Real.log (1 + ‖τ'‖) ≤ Ll + D₁ := by
    have h1 : ‖τ'‖ ≤ L + (m : ℝ) + ‖s‖ := by
      rw [hτ'def, hLdef]
      calc ‖τ + (m : ℂ) - s‖ ≤ ‖τ + (m : ℂ)‖ + ‖s‖ := norm_sub_le _ _
        _ ≤ (‖τ‖ + ‖(m : ℂ)‖) + ‖s‖ := by linarith [norm_add_le τ ((m : ℂ))]
        _ = ‖τ‖ + (m : ℝ) + ‖s‖ := by rw [Complex.norm_natCast]
    have hLl_le : Ll ≤ 1 + L := by
      rw [hLldef, hLdef]
      have h2 : (0 : ℝ) < 2 + ‖τ‖ := by positivity
      calc Real.log (2 + ‖τ‖) ≤ (2 + ‖τ‖) - 1 := Real.log_le_sub_one_of_pos h2
        _ = 1 + ‖τ‖ := by ring
    have hbound : 1 + ‖τ'‖ ≤ (2 + L) * (2 + 2 * K₂ + ‖s‖) := by
      have hK₂b : K₂ * (Ll + 1) ≤ K₂ * (2 + L) := by
        have : Ll + 1 ≤ 2 + L := by linarith
        exact mul_le_mul_of_nonneg_left this hK₂nn
      have hLnn : 0 ≤ L := by rw [hLdef]; positivity
      have hsnn : 0 ≤ ‖s‖ := norm_nonneg s
      nlinarith [h1, hm_le, hK₂b, hLnn, hsnn, hK₂nn, hLl_nn]
    have hcpos : (0 : ℝ) < 2 + L := by rw [hLdef]; positivity
    have hCpos : (0 : ℝ) < 2 + 2 * K₂ + ‖s‖ := by have h := norm_nonneg s; linarith [hK₂nn]
    have h3 : Real.log (1 + ‖τ'‖) ≤ Real.log ((2 + L) * (2 + 2 * K₂ + ‖s‖)) :=
      Real.log_le_log (by positivity) hbound
    rw [Real.log_mul (ne_of_gt hcpos) (ne_of_gt hCpos)] at h3
    have h4 : Real.log (2 + L) = Ll := by rw [hLldef]
    have h5 : Real.log (2 + 2 * K₂ + ‖s‖) = D₁ := by rw [hD₁def]
    linarith
  -- condition (I)
  have hI : logSlack K₁ X₁ τ' < τ'.re := by
    rw [logSlack_apply, hτ're]
    have hlogA' : K₁ * Real.log (1 + ‖τ'‖) ≤ K₁ * (Ll + D₁) :=
      mul_le_mul_of_nonneg_left hlogA hK₁
    have hXa2 : X₁ + K₁ * (D₁ + Real.pi) - K₁ + s.re ≤ Xsat := by linarith [hXsat_a]
    nlinarith [hlogA', hm_ge, hXa2, hτ, hK₂def, hLl_nn, Real.pi_pos, hD₁nn]
  obtain ⟨W₀, hW₀re, hW₀ψ, hW₀re', hW₀im'⟩ := hS1 τ' hI
  -- condition (II)
  have hsgeo : Ml + (m : ℝ) * Cb ≤ sgauge W₀ := by
    have hLS_le : logSlack K₁ X₁ τ' ≤ X₁ + K₁ * (Ll + D₁ + Real.pi) := by
      rw [logSlack_apply]
      have h := mul_le_mul_of_nonneg_left hlogA hK₁
      linarith
    have hsg1 : τ'.re + |τ'.im| - 2 * logSlack K₁ X₁ τ' ≤ sgauge W₀ := by
      rw [sgauge]; linarith [hW₀re', hW₀im']
    have hτim : |τ.im| - ‖s‖ ≤ |τ'.im| := by
      rw [hτ'im]
      have h1 : |τ.im| - |s.im| ≤ |τ.im - s.im| := abs_sub_abs_le_abs_sub τ.im s.im
      have h2 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
      linarith
    have hτpi : L ≤ τ.re + |τ.im| := by
      rw [hLdef]
      have h1 := Complex.norm_le_abs_re_add_abs_im τ
      rw [abs_of_pos hτre_pos] at h1
      linarith
    have hsplit : L + (m : ℝ) - ss ≤ τ'.re + |τ'.im| := by
      have h1 : (τ.re + |τ.im|) + (m : ℝ) - ss ≤ τ'.re + |τ'.im| := by
        rw [hτ're, hssdef]; linarith [hτim]
      linarith [hτpi, h1]
    have h2LS : 2 * logSlack K₁ X₁ τ' ≤ 2 * (X₁ + K₁ * (Ll + D₁ + Real.pi)) := by
      linarith [hLS_le]
    have hmone : (K₂ * (Ll + 1) + 1) * (1 - Cb) ≤ (m : ℝ) * (1 - Cb) := by
      have h : 1 - Cb ≤ 0 := by linarith
      exact mul_le_mul_of_nonpos_right hm_le h
    have hkey2 : L - Acoef * Ll - Bcoef ≤ sgauge W₀ - Ml - (m : ℝ) * Cb := by
      rw [hAdef, hBdef, hssdef, hK₂def]
      nlinarith [hsg1, hsplit, h2LS, hmone]
    have hfinal : 0 ≤ L - Acoef * Ll - Bcoef := by
      have hlog_sqrt : Real.log (2 + L) ≤ 2 * Real.sqrt (2 + L) :=
        log_le_two_sqrt (by rw [hLdef]; positivity)
      have hstep1 : Acoef * Ll ≤ 2 * Acoef * Real.sqrt (2 + L) := by
        rw [hLldef]
        calc Acoef * Real.log (2 + L) ≤ Acoef * (2 * Real.sqrt (2 + L)) :=
              mul_le_mul_of_nonneg_left hlog_sqrt hAcoef_nn
          _ = 2 * Acoef * Real.sqrt (2 + L) := by ring
      have hstep2 : Y₀ ^ 2 - 2 * Acoef * Y₀ - 2 ≤ L - 2 * Acoef * Real.sqrt (2 + L) := by
        set s'' : ℝ := Real.sqrt (2 + L) with hs''def
        have hs''sq : s'' ^ 2 = 2 + L := by
          rw [hs''def]; exact Real.sq_sqrt (by rw [hLdef]; positivity)
        have hs''ge : Y₀ ≤ s'' := by
          rw [hs''def]
          have h2X : 2 + X₂ ≤ 2 + L := by linarith [hX₂_le_L]
          have h := Real.sqrt_le_sqrt h2X
          rwa [hX₂_sqrt] at h
        have hsq_mono : (Y₀ - Acoef) ^ 2 ≤ (s'' - Acoef) ^ 2 := by
          apply pow_le_pow_left₀ (by linarith [hAcoef_nn, hY_ge_2A])
          linarith [hs''ge]
        nlinarith [hs''sq, hsq_mono]
      have hEex : Bcoef ≤ Y₀ ^ 2 - 2 * Acoef * Y₀ - 2 := by linarith [hY_key, hEe_ge]
      linarith [hstep1, hstep2, hEex]
    linarith [hkey2, hfinal]
  obtain ⟨W', hW'g, hW'f⟩ := hbwd W₀ m Ml hMl_M₀ hsgeo
  have hW'0 : W' ≠ 0 := by
    intro h0
    have hz : sgauge W' = 0 := by rw [h0]; simp [sgauge]
    linarith [hW'g, hMl_pos]
  set z : ℂ := -1 / W' with hzdef
  have hz0 : z ≠ 0 := by rw [hzdef]; exact div_ne_zero (by norm_num) hW'0
  have hzchart : (-1 : ℂ) / z = W' := by
    rw [hzdef]; exact Work.FatouCoordFix.neg_one_div_neg_one_div' hW'0
  have hMgz : Mg < sgauge (-1 / z) := by rw [hzchart]; linarith [hW'g, hMl_Mg]
  have hgl0 := hgloss z hz0 hMgz
  have hgUz_gt : Ms' < sgauge (-1 / (gU z)) := by
    rw [hzchart] at hgl0
    linarith [hgl0, hW'g, hMl_sCg]
  have hgUz0 : gU z ≠ 0 := by
    intro h0
    have hz : sgauge (-1 / (gU z)) = 0 := by rw [h0]; simp [sgauge]
    linarith [hgUz_gt, hMs'pos]
  have hzPa : z ∈ fl.Pa := hwide' z hz0 (by rw [hzchart]; linarith [hW'g, hMl_Ms])
  have hgUzPa : gU z ∈ fl.Pa := hwide' (gU z) hgUz0 hgUz_gt
  -- evaluate φa
  have hW₀ne : W₀ ≠ 0 := by
    intro h0
    have : W₀.re = 0 := by rw [h0]; simp
    linarith [hW₀re, hMh'nn]
  have hu₀ : (-1 : ℂ) / W₀ ∈ Work.FatouCoordFix.HPlanePetal Mh' := by
    simp only [Work.FatouCoordFix.mem_HPlanePetal]
    refine ⟨div_ne_zero (by norm_num) hW₀ne, ?_⟩
    have hchart : (-1 : ℂ) / (-1 / W₀) = W₀ :=
      Work.FatouCoordFix.neg_one_div_neg_one_div' hW₀ne
    rw [hchart]; exact hW₀re
  have hφa_u₀ : fl.φa (-1 / W₀) = τ + (m : ℂ) := by
    rw [hφa_Pg' (-1 / W₀) hu₀]
    rw [Work.FatouCoord.fatouCoord_eq]
    have hchart : Work.FatouCoord.chart (-1 / W₀) = W₀ := by
      show (-1 : ℂ) / (-1 / W₀) = W₀
      exact Work.FatouCoordFix.neg_one_div_neg_one_div' hW₀ne
    rw [hchart, hW₀ψ, hτ'def]
    ring
  have hiter := fl.φa_shift_iterate hzPa m
  rw [hzdef] at hiter
  rw [hW'f] at hiter
  rw [hφa_u₀] at hiter
  exact ⟨z, hzPa, hgUzPa, (add_right_cancel hiter).symm⟩

/-- **The wide, sign-free saturating germ flower.**  (wire note §B.2, step S2)

Copy of `Work.GATE2.PL.germ_parabolicFlowerFix_saturating`
(`Submission/Work/GATE2/PL/germ_parabolicFlowerFix_saturating.lean`) with the hypothesis
`ha1 : a.re < 1` **deleted** and the saturation clause replaced by the sign-free one.

*Which parts of that file use `ha1`?*  Exactly one: the final `hsat` block, where
`Work.GATE2.PL.fatouCoordW_saturates_petal ... ha1 Mh` is applied.  Everything else — the
`ParabolicBounds` bookkeeping, the local injectivity, the conjugacy `V`, the entire repelling
coordinate `Ψ`, the petal `Pa = WidePetal Ms ∪ Ψ '' {w | w.re < -(R+1) ∧ T < |w.im|}`,
the half-plane sub-petal `Pg = HPlanePetal Mh`, the thresholds `Mh`/`Ms`, the push-forward
`exists_phia_pushforward_agree` with the offset `s` (`hφa_Pg : ∀ z ∈ Pg, φa z = fatouCoord f
(1-a) z + s`), `hPg_sub_M : Pg ⊆ Petal ρ M`, `hφa_shift`, `hPa_ball_δ : Pa ⊆ ball 0 δ` — is
sign-free.  So copy the file, delete `ha1`, and replace the last block.

*The new saturation proof.*  Keep the constants produced by the copy plus
`obtain ⟨X₁, K₁, hK₁, hS1⟩ := SatFree.fatouCoordW_saturates_log hbρ Mh`,
`obtain ⟨Mb, Cb, hCb, hbwd⟩ := SatFree.backward_orbit hbρ`,
`obtain ⟨Mg, Cg, hCg, hgloss⟩ := SatFree.gU_sgauge_loss hρ hgl`
and set `M := max Ms (Mg + Ms + Cg) + 1` (so that `WidePetal M ⊆ WidePetal Ms` and
`sgauge W ≥ M ⟹ sgauge (-1/(gU (-1/W))) > Ms`).  Given `τ` with `X < τ.re` (with `X` chosen
below, large), put
`m := Nat.ceil (K₂ * (Real.log (2 + ‖τ‖) + 1)) + K₃` with `K₂ := 2*(K₁ + Cb) + 2`,
`K₃` a large constant, and apply S1 to the target `τ' := τ + (m : ℂ) - s` (so that, because
`φa u = fatouCoord f (1-a) u + s` on `Pg`, a point `u` with `φa u = τ + m` is what we want):

* the hypothesis `logSlack K₁ X₁ τ' < τ'.re` holds for `Re τ > X` once `X` is large: `K₂ ≥ K₁`
  makes the `log` terms cancel, and the constant is absorbed by `X`;
* S1 gives `W₀` with `Mh < W₀.re`, `fatouCoordW f (1-a) W₀ = τ'` and the two quantitative
  lower bounds `τ'.re - logSlack ≤ W₀.re`, `|τ'.im| - logSlack ≤ |W₀.im|`.  Hence
  `u₀ := -1/W₀ ∈ Pg` (since `Pg = HPlanePetal Mh`) and `φa u₀ = τ + m`, and
  `sgauge W₀ ≥ W₀.re + |W₀.im| ≥ τ.re + |τ.im| + m - (const)*log(2+‖τ‖) - (const)`
  (using `τ.re + |τ.im| ≥ ‖τ‖` and `log (1 + ‖τ'‖) ≤ log (2 + ‖τ‖) + const`).
  With `K₂` chosen at least `Cb + 2*K₁ + 2` this is `≥ M + (m:ℝ) * Cb`;
* `SatFree.backward_orbit` at that `W₀` and `m` gives `W'` with `sgauge W' ≥ M` and
  `(f^[m]) (-1/W') = -1/W₀ = u₀`.  Put `z := -1/W'`.  Then
  `z ∈ fl.Pa` (as `sgauge W' ≥ M > Ms`, so `z ∈ WidePetal Ms ⊆ Pa`),
  `gU z ∈ fl.Pa` (`gU_sgauge_loss` gives `sgauge (-1/(gU z)) ≥ sgauge W' - Cg > Ms`), and
  `fl.φa z = fl.φa u₀ - m = τ` by `ParabolicFlowerFix.φa_shift_iterate` (`z ∈ Pa`).
  This is `SatHalfPlane gU fl.Pa fl.φa` with the threshold `X`.

The first two conjuncts of the conclusion are the copy's `hPa_ball_δ` and the wide containment
`WidePetal Ms ⊆ Pa`, which is `Or.inl` of `hPadef`, so they are immediate; only
`SatHalfPlane gU fl.Pa fl.φa` is new. -/
theorem germ_flowerFix_wideSat {f gU h : ℂ → ℂ} {a : ℂ} {r A A' G₀ ρ δ : ℝ}
    (hf : Differentiable ℂ f)
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') (hρ : 0 < ρ) (hρr : ρ ≤ r)
    (hδpos : 0 < δ)
    (hgl : ∀ z : ℂ, ‖z‖ < ρ → ‖gU z - star z‖ ≤ G₀ * ‖z‖ ^ 2)
    (hgU_anti : ∀ z : ℂ, DifferentiableAt ℂ (fun z => star (gU z)) z)
    (hgg : gU ∘ gU = f) (hgU0 : gU 0 = 0) (ha : star a = a) :
    ∃ fl : Work.FatouCoordFix.ParabolicFlowerFix f gU 0, fl.Pa ⊆ Metric.ball 0 δ ∧
      (∃ Ms : ℝ, ∀ u : ℂ, u ≠ 0 → Ms < Work.FatouCoord.Flower.sgauge (-1 / u) → u ∈ fl.Pa) ∧
      Work.SatFree.SatHalfPlane gU fl.Pa fl.φa := by
  obtain ⟨fl, Ms, Mh, s, hball, hwide, hφa_Pg⟩ :=
    germ_flowerFix_wideSat_core hf hb hρ hρr hδpos hgl hgU_anti hgg hgU0 ha
  exact ⟨fl, hball, ⟨Ms, hwide⟩,
    SatHalfPlane_of_core hb hρ hρr hgl fl Ms Mh s hwide hφa_Pg⟩


end

end Work.SatFree
