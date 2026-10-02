import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.Implosion.Approx
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL2.Lavaurs.approxEcal_transit_rot_unif
import Submission.Work.PARIMPL2.Direct.inbound_bounds
import Submission.Work.PARIMPL2.Direct.modelDisp_step_bounds2
import Submission.Work.PARIMPL2.Direct.ecalPt_norm_le_four_div
import Submission.Work.PARIMPL2.Direct.goodTransitRotOfStrip
import Submission.Work.PARIMPL2.Direct.ecalPt_re_pos
import Submission.Work.PARIMPL2.Direct.orbitImDriftHalf
import Submission.Work.PARIMPL2.Direct.orbitImLamSmall
import Submission.Work.PARIMPL2.Direct.approxEcalReLeAtExit4
import Submission.Work.PARIMPL2.Direct.Rtop_le_two_R
import Submission.Work.PARIMPL2.Direct.lam_re_lt_half_of_level2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

namespace Work.PARIMPL2.Direct

open Complex
open Work.Implosion

noncomputable section

/-! ## Elementary strip facts -/

/-- In the strip `0 < λ Re u < π` the chart point `Z u = sinh(a u)/a` lies in the slit plane. -/
theorem sinh_div_slitPlane_of_strip (lam : ℝ) (hlam : 0 < lam) (u : ℂ)
    (h1 : 0 < lam * u.re) (h2 : lam * u.re < Real.pi) :
    Complex.sinh (((lam : ℂ) * Complex.I) * u) / ((lam : ℂ) * Complex.I) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  rw [inbound_Z_re lam (ne_of_gt hlam) u]
  exact div_pos (mul_pos (Real.sin_pos_of_pos_of_lt_pi h1 h2) (Real.cosh_pos _)) hlam

/-! ## The transit (assembly)

The proof of `modelTransit` below follows the design of
`Submission/Work/PARIMPL2/Lavaurs/NOTES_LEAD_transit_exit_direct_S2.md` §1--§3:
let `u_j = modelOrbit a h j u₀` (`a = iλ`), `W(u) = approxEcal a (τ - h1/τ) u`,
`L_j = (W u_j).re`, `N = ⌊4π/λ⌋₊ + 4` and define `k` as the least `j ≤ N` with `L_j ≤ R+2`.

Invariant (for all `j ≤ N` under `(∀ i < j, R + 2 < L_i)`):
`R/4+2 ≤ (u_j).re ≤ π/λ - R/4`, `‖ecalPt a u_j‖ ≤ 4/R`, `‖ecalPt a u_j‖ < r`,
`L_0 - 2j ≤ L_j ≤ L_0 - j/4`, together with the one-step facts
`(u_{j+1}).re ≤ (u_j).re - 1/3`, `L_j - 2 ≤ L_{j+1} ≤ L_j - 1/4` and the slit condition.

Step `j → j+1` (with `L_j > R+2`):
* `Direct.inbound_bounds` gives `|(u_0).im| ≤ 2H+8+log R`, `R/4 ≤ (u_0).re ≤ π/λ - R/4`,
  and `Direct.Rtop_le_two_R` gives `π/λ - 2R ≤ (u_0).re`.
* If `(u_j).re ≤ R/4+4` then `Direct.orbitImDriftHalf` (the `Im`-drift bound in the exit
  window, where the two halves of the transit cancel) and
  `Direct.approxEcalReLeAtExit4` give `L_j ≤ R+2`, contradicting `L_j > R+2`: hence
  `(u_j).re > R/4+4`.
* `Direct.modelDisp_step_bounds2` at `u_j` then gives the next invariant, and
  `Direct.ecalPt_norm_le_four_div` re-establishes `‖ecalPt a u_{j+1}‖ ≤ 4/R`.
* At `k`: `L_k ∈ [R, R+2]`, `(u_k).re ≥ R/4+2`, `λ (u_k).re < π/2`
  (`Direct.lam_re_lt_half_of_level2`, with `λ|(u_k).im| ≤ 1` from
  `Direct.orbitImLamSmall`), hence `0 < Re (ecalPt a u_k)` (`Direct.ecalPt_re_pos`),
  and `GoodTransitRot` for `j ≤ k` (`Direct.goodTransitRotOfStrip`).
* The final error is `approxEcal_transit_rot_unif` at `n = k` (strip parameter `R/4`) plus
  `k‖τ-1‖ ≤ (4π/λ + 4)‖τ-1‖ ≤ 3/(4R)` from `hτpi`. -/

/-- Real arithmetic of the final error estimate: if the exit index `k` satisfies
`k ≤ 4π/λ + 4` and `(π/λ)·d ≤ 1/(8R)` with `d ≥ 0`, then `k·d ≤ 3/(4R)`
(for `λR² ≤ 1`, `R ≥ 128`). -/
private theorem natCast_mul_le (lam R c d : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1) (hd0 : 0 ≤ d) (hk : c ≤ 4 * (Real.pi / lam) + 4)
    (hτpi : (Real.pi / lam) * d ≤ 1 / (8 * R)) : c * d ≤ 3 / (4 * R) := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hd : d ≤ lam / (8 * Real.pi * R) := by
    have hpos : (0 : ℝ) ≤ lam / Real.pi := by positivity
    have h := mul_le_mul_of_nonneg_left hτpi hpos
    have heq : (lam / Real.pi) * ((Real.pi / lam) * d) = d := by field_simp
    have heq2 : (lam / Real.pi) * (1 / (8 * R)) = lam / (8 * Real.pi * R) := by field_simp
    rw [heq, heq2] at h
    exact h
  have hlamR2 : lam ≤ 1 / R ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
  have h4d : 4 * d ≤ 1 / (4 * R) := by
    have h2 : lam / (8 * Real.pi * R) ≤ 1 / (16 * R) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hlamR2, hR, Real.pi_gt_three]
    have h3 : 4 * d ≤ 4 * (1 / (16 * R)) :=
      mul_le_mul_of_nonneg_left (le_trans hd h2) (by norm_num)
    have h4 : 4 * (1 / (16 * R)) = 1 / (4 * R) := by field_simp; ring
    linarith [h3, h4.le]
  have hcd : c * d ≤ (4 * (Real.pi / lam) + 4) * d := mul_le_mul_of_nonneg_right hk hd0
  have hexp : (4 * (Real.pi / lam) + 4) * d = 4 * ((Real.pi / lam) * d) + 4 * d := by ring
  have h4pil : 4 * ((Real.pi / lam) * d) ≤ 4 * (1 / (8 * R)) :=
    mul_le_mul_of_nonneg_left hτpi (by norm_num)
  have h4pil' : 4 * (1 / (8 * R)) = 1 / (2 * R) := by field_simp; ring
  have hsum : 1 / (2 * R) + 1 / (4 * R) = 3 / (4 * R) := by field_simp; ring
  linarith [hcd, hexp.le, hexp.ge, h4pil, h4d, h4pil'.le, h4pil'.ge, hsum.le, hsum.ge]

theorem modelTransit (A r B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (lam R H : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
      (hH : 0 ≤ H) (hHR : 8 * (H + 2) ≤ R)
      (h : ℂ → ℂ) (τ h1 : ℂ) (hb : Work.PARIMPL.ParBounds h τ h1 A r)
      (hτ1 : ‖τ - 1‖ ≤ 1 / 8) (hh1 : ‖h1‖ ≤ B)
      (hAr : 4 * B / R + 16 * A / R ^ 2 ≤ 3 / 8) (hrr : 16 ≤ R * r)
      (hκR : 64 * ‖τ - h1 / τ‖ ≤ R) (hκI : |(τ - h1 / τ).im| ≤ 1 / 4)
      (hκlog : ‖τ - h1 / τ‖ * (1 + Real.log R) ≤ 3 * R / 4)
      (hτpi : (Real.pi / lam) * ‖τ - 1‖ ≤ 1 / (8 * R))
      (u0 : ℂ)
      (hbranch : -(Real.pi / 2) < lam * u0.re - Real.pi ∧ lam * u0.re - Real.pi ≤ Real.pi / 2)
      (hlev : (Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) (τ - h1 / τ) u0).re ∈
        Set.Icc (Real.pi / lam - R - 2) (Real.pi / lam - R))
      (him : |(Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) (τ - h1 / τ) u0).im| ≤ H)
      (hζre : (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u0).re < 0)
      (hζn : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u0‖ ≤ 4 / R),
      ∃ k : ℕ,
        (Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) (τ - h1 / τ)
            (Work.Implosion.modelOrbit ((lam : ℂ) * Complex.I) h k u0)).re ∈ Set.Icc R (R + 2) ∧
        0 < (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I)
            (Work.Implosion.modelOrbit ((lam : ℂ) * Complex.I) h k u0)).re ∧
        ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I)
            (Work.Implosion.modelOrbit ((lam : ℂ) * Complex.I) h k u0)‖ ≤ 4 / R ∧
        (∀ j : ℕ, j ≤ k → Work.PARIMPL.GoodTransitRot ((lam : ℂ) * Complex.I) h τ lam (R / 4)
          (Work.Implosion.modelOrbit ((lam : ℂ) * Complex.I) h j u0)) ∧
        (∀ j : ℕ, j ≤ k → ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I)
          (Work.Implosion.modelOrbit ((lam : ℂ) * Complex.I) h j u0)‖ < r) ∧
        (∀ j : ℕ, j < k → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
          Complex.sinh (((lam : ℂ) * Complex.I)
            * (Work.Implosion.modelOrbit ((lam : ℂ) * Complex.I) h j u0
              + (t : ℂ) * Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h
                  (Work.Implosion.modelOrbit ((lam : ℂ) * Complex.I) h j u0)))
            / ((lam : ℂ) * Complex.I) ∈ Complex.slitPlane) ∧
        ‖Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) (τ - h1 / τ)
            (Work.Implosion.modelOrbit ((lam : ℂ) * Complex.I) h k u0)
          - Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) (τ - h1 / τ) u0
          + (k : ℂ)‖ ≤ C / R := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := Work.PARIMPL2.Lavaurs.approxEcal_transit_rot_unif A r B hA
  refine ⟨5 * C₁ + 1, by positivity, ?_⟩
  intro lam R H hlam hR hlamR hH hHR h τ h1 hb hτ1 hh1 hAr hrr hκR hκI hκlog hτpi u0
    hbranch hlev him hζre hζn
  have hRpos : (0 : ℝ) < R := by linarith
  have hA0 : 0 ≤ A := hA
  have hB0 : 0 ≤ B := hB
  set a : ℂ := (lam : ℂ) * Complex.I with ha
  set κ : ℂ := τ - h1 / τ with hκdef
  have hκeq : κ = τ - h1 / τ := hκdef
  -- the imaginary part of `τ ^ 2 - h1 = τ * κ`
  have hcim : |(τ ^ 2 - h1).im| ≤ 1 / 2 := by
    have hτne : τ ≠ 0 := by
      intro h0
      have h1' := hb.2.1
      rw [h0] at h1'
      simp at h1'
    have hmul : τ ^ 2 - h1 = τ * κ := by
      rw [hκeq]
      field_simp
    have hτim : ‖τ - 1‖ ≤ lam / (8 * Real.pi * R) := by
      have hpos : (0 : ℝ) ≤ lam / Real.pi := by positivity
      have h := mul_le_mul_of_nonneg_left hτpi hpos
      have heq : (lam / Real.pi) * ((Real.pi / lam) * ‖τ - 1‖) = ‖τ - 1‖ := by field_simp
      have heq2 : (lam / Real.pi) * (1 / (8 * R)) = lam / (8 * Real.pi * R) := by field_simp
      rw [heq, heq2] at h
      exact h
    have hτim2 : |τ.im| ≤ ‖τ - 1‖ := by
      have := Complex.abs_im_le_norm (τ - 1)
      simpa using this
    have hτre : |τ.re| ≤ 1 := by
      have := Complex.abs_re_le_norm τ
      rw [hb.2.1] at this
      simpa using this
    have hk : ‖κ‖ ≤ 3 * R := by
      have hlog : 1 ≤ 1 + Real.log R := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ R by linarith)
        linarith
      have h1' : ‖κ‖ * 1 ≤ ‖κ‖ * (1 + Real.log R) :=
        mul_le_mul_of_nonneg_left hlog (norm_nonneg κ)
      nlinarith [hκlog]
    have hlamR2 : lam ≤ 1 / R ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
    have hprod : lam / (8 * Real.pi * R) * ‖κ‖ ≤ 1 / 4 := by
      have hb1 : lam * ‖κ‖ ≤ 3 / R := by
        have h := mul_le_mul hlamR2 hk (norm_nonneg κ) (by positivity)
        have h2 : (1 / R ^ 2) * (3 * R) = 3 / R := by field_simp
        linarith [h, h2.le, h2.ge]
      have hle : lam * ‖κ‖ ≤ 2 * Real.pi * R := by
        have h3 : 3 / R ≤ 2 * Real.pi * R := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < R)]
          nlinarith [hR, Real.pi_gt_three]
        linarith [hb1, h3]
      have heq : lam / (8 * Real.pi * R) * ‖κ‖ = lam * ‖κ‖ / (8 * Real.pi * R) := by ring
      rw [heq, div_le_iff₀ (by positivity)]
      have h6 : (1 / 4) * (8 * Real.pi * R) = 2 * Real.pi * R := by ring
      linarith [hle, h6.le, h6.ge]
    have hlin : |(τ * κ).im| ≤ |τ.re| * |κ.im| + |τ.im| * |κ.re| := by
      rw [Complex.mul_im]
      calc |τ.re * κ.im + τ.im * κ.re| ≤ |τ.re * κ.im| + |τ.im * κ.re| := abs_add_le _ _
        _ = |τ.re| * |κ.im| + |τ.im| * |κ.re| := by rw [abs_mul, abs_mul]
    have h1'' : |τ.re| * |κ.im| ≤ 1 * (1 / 4) :=
      mul_le_mul hτre hκI (abs_nonneg _) (by norm_num)
    have hsmall : |τ.im| * |κ.re| ≤ 1 / 4 := by
      have h1' : |κ.re| ≤ ‖κ‖ := Complex.abs_re_le_norm κ
      have h2' : |τ.im| ≤ lam / (8 * Real.pi * R) := le_trans hτim2 hτim
      have h3' : |τ.im| * |κ.re| ≤ lam / (8 * Real.pi * R) * ‖κ‖ :=
        mul_le_mul h2' h1' (abs_nonneg _) (by positivity)
      linarith [h3', hprod]
    rw [hmul]
    linarith [hlin, hsmall, h1'']
  -- basic numerical facts
  have h4r : 4 / R < r := by
    have h1 : 16 / R ≤ r := by rw [div_le_iff₀ hRpos]; linarith
    have h2 : 4 / R < 16 / R := by rw [div_lt_div_iff₀ hRpos hRpos]; linarith
    linarith
  have hpi2 : 2 * R + 4 < Real.pi / lam := by
    have h1 : Real.pi * R ^ 2 ≤ Real.pi / lam := by
      rw [le_div_iff₀ hlam]
      nlinarith [Real.pi_pos]
    nlinarith [Real.pi_gt_three, hR]
  have hAr16 : 16 * A / R ^ 2 ≤ 3 / 8 := by
    have h1 : 0 ≤ 4 * B / R := by positivity
    linarith
  -- the orbit and the level
  let u : ℕ → ℂ := fun j => Work.Implosion.modelOrbit a h j u0
  let Φ : ℕ → ℂ := fun j => Work.Implosion.modelDisp a h (u j)
  let ζ : ℕ → ℂ := fun j => Work.Implosion.ecalPt a (u j)
  let L : ℕ → ℝ := fun j => (Work.Implosion.approxEcal a κ (u j)).re
  have hu : ∀ j : ℕ, u (j + 1) = u j + Φ j := by
    intro j
    simp only [u, Φ]
    exact Work.Implosion.modelOrbit_succ a h j u0
  -- inbound data
  obtain ⟨hy0, hx0lo, hx0hi⟩ :=
    inbound_bounds lam R H hlam hR hlamR hH hHR κ hκR hκI hκlog u0 hbranch hlev him hζre hζn
  have hy00 : |(u 0).im| ≤ 2 * H + 8 + Real.log R := by
    simpa only [u, Work.Implosion.modelOrbit_zero] using hy0
  have hx00lo : R / 4 ≤ (u 0).re := by
    simpa only [u, Work.Implosion.modelOrbit_zero] using hx0lo
  have hx00hi : (u 0).re ≤ Real.pi / lam - R / 4 := by
    simpa only [u, Work.Implosion.modelOrbit_zero] using hx0hi
  have hL0low : Real.pi / lam - R - 2 ≤ L 0 := by
    simpa only [L, u, Work.Implosion.modelOrbit_zero] using hlev.1
  have hL0up : L 0 ≤ Real.pi / lam - R := by
    simpa only [L, u, Work.Implosion.modelOrbit_zero] using hlev.2
  have hbase : R + 2 < L 0 := by linarith
  -- the top of the strip
  have htop : Real.pi / lam - 2 * R ≤ (u 0).re :=
    Rtop_le_two_R lam R H hlam hR hlamR hH hHR τ h1 κ hτ1 hκeq hκI hκlog u0 hy0 hx0lo hx0hi hlev
  have h2H8 : 2 * H + 8 ≤ R / 4 + 4 := by linarith
  -- `E` and the drift allowance
  have hE1 : 1 ≤ Real.exp (40 * max h1.re 0 / R) := Real.one_le_exp (by positivity)
  have hE0 : 0 ≤ Real.exp (40 * max h1.re 0 / R) := le_of_lt (Real.exp_pos _)
  -- the threshold: the level at a point of the exit window
  have hthr : ∀ j : ℕ, (u j).re ≤ R / 4 + 4 → R / 4 ≤ (u j).re →
      (∀ i ≤ j, R / 4 + 2 ≤ (u i).re ∧ (u i).re ≤ Real.pi / lam - R / 4 ∧
        ‖ζ i‖ ≤ 4 / R ∧ ‖ζ i‖ < r ∧ L 0 - 2 * (i : ℝ) ≤ L i ∧ L i ≤ L 0 - (i : ℝ) / 4) →
      (∀ i < j, (u (i + 1)).re ≤ (u i).re - 1 / 3) → L j ≤ R + 2 := by
    intro j hxj hxlo hdata hdec
    have hhu : ∀ i < j, Work.Implosion.modelOrbit a h (i + 1) u0
        = Work.Implosion.modelOrbit a h i u0
          + Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h
              (Work.Implosion.modelOrbit a h i u0) := by
      intro i hi
      simpa only [u, Φ, ha] using hu i
    have hhtop : Real.pi / lam - 2 * R ≤ (Work.Implosion.modelOrbit a h 0 u0).re := by
      simpa only [u, Work.Implosion.modelOrbit_zero] using htop
    have hhx1 : ∀ i ≤ j, R / 4 + 2 ≤ (Work.Implosion.modelOrbit a h i u0).re := by
      intro i hi
      simpa only [u] using (hdata i hi).1
    have hhx2 : ∀ i ≤ j, (Work.Implosion.modelOrbit a h i u0).re ≤ Real.pi / lam - R / 4 := by
      intro i hi
      simpa only [u] using (hdata i hi).2.1
    have hhzn : ∀ i ≤ j, ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I)
        (Work.Implosion.modelOrbit a h i u0)‖ ≤ 4 / R := by
      intro i hi
      simpa only [ζ, u] using (hdata i hi).2.2.1
    have hhzr : ∀ i ≤ j, ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I)
        (Work.Implosion.modelOrbit a h i u0)‖ < r := by
      intro i hi
      simpa only [ζ, u] using (hdata i hi).2.2.2.1
    have hhy0 : |(Work.Implosion.modelOrbit a h 0 u0).im| ≤ R / 4 + 4 + Real.log R := by
      have h' : |(u 0).im| ≤ R / 4 + 4 + Real.log R := by linarith [hy00, h2H8]
      simpa only [u, Work.Implosion.modelOrbit_zero] using h'
    have hdr := orbitImDriftHalf lam R hlam hR hlamR h τ h1 A r B hA hr hb hh1 hτ1 hAr hrr hτpi j
      (fun i => Work.Implosion.modelOrbit a h i u0) hhu hhtop hxj hhx1 hhx2 hdec hhzn hhzr hhy0
    have hy : |(u j).im| ≤ Real.exp (40 * max h1.re 0 / R) *
        (2 * H + 8 + Real.log R + 8 * |(τ ^ 2 - h1).im| * (1 + Real.log R) + 20 * A / R + 32) := by
      have hbr : |(u 0).im| + 8 * |(τ ^ 2 - h1).im| * (1 + Real.log R) + 20 * A / R + 32
          ≤ 2 * H + 8 + Real.log R + 8 * |(τ ^ 2 - h1).im| * (1 + Real.log R)
            + 20 * A / R + 32 := by
        linarith [hy00, h2H8]
      exact le_trans hdr (mul_le_mul_of_nonneg_left hbr hE0)
    have hres := approxEcalReLeAtExit4 lam R H A hlam hR hlamR τ h1 κ hτ1 hκeq hκI hcim hκlog
      hH hHR hA0 hAr16 (u j) hxlo hxj hy
    simpa only [L, ha] using hres
  -- the main invariant
  have hInv : ∀ j : ℕ, (∀ i < j, R + 2 < L i) →
      (∀ i ≤ j, R / 4 + 2 ≤ (u i).re ∧ (u i).re ≤ Real.pi / lam - R / 4 ∧
        ‖ζ i‖ ≤ 4 / R ∧ ‖ζ i‖ < r ∧ L 0 - 2 * (i : ℝ) ≤ L i ∧ L i ≤ L 0 - (i : ℝ) / 4) ∧
      (∀ i < j, (u (i + 1)).re ≤ (u i).re - 1 / 3 ∧ L (i + 1) ≥ L i - 2 ∧
        L (i + 1) ≤ L i - 1 / 4 ∧
        (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
          Complex.sinh (a * (u i + (t : ℂ) * Φ i)) / a ∈ Complex.slitPlane)) := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hprev
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · -- base case `j = 0`
        subst hj0
        have hζ0n : ‖ζ 0‖ ≤ 4 / R := by
          simpa only [ζ, u, Work.Implosion.modelOrbit_zero] using hζn
        have hstrip : R / 4 + 2 ≤ (u 0).re ∧ (u 0).re ≤ Real.pi / lam - R / 4 := by
          refine ⟨?_, hx00hi⟩
          by_contra hcon
          push_neg at hcon
          have hle : (u 0).re ≤ R / 4 + 4 := by linarith
          have hy : |(u 0).im| ≤ Real.exp (40 * max h1.re 0 / R) *
              (2 * H + 8 + Real.log R + 8 * |(τ ^ 2 - h1).im| * (1 + Real.log R)
                + 20 * A / R + 32) := by
            have hlog : 0 ≤ Real.log R := Real.log_nonneg (show (1 : ℝ) ≤ R by linarith)
            have hA8 : 0 ≤ 8 * |(τ ^ 2 - h1).im| * (1 + Real.log R) :=
              mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (by linarith)
            have hA20 : 0 ≤ 20 * A / R := by positivity
            have hB : 2 * H + 8 + Real.log R ≤
                2 * H + 8 + Real.log R + 8 * |(τ ^ 2 - h1).im| * (1 + Real.log R)
                  + 20 * A / R + 32 := by linarith
            have hB0' : 0 ≤ 2 * H + 8 + Real.log R + 8 * |(τ ^ 2 - h1).im| * (1 + Real.log R)
                + 20 * A / R + 32 := by linarith
            calc |(u 0).im| ≤ 2 * H + 8 + Real.log R := hy00
              _ ≤ _ := hB
              _ = 1 * (2 * H + 8 + Real.log R + 8 * |(τ ^ 2 - h1).im| * (1 + Real.log R)
                    + 20 * A / R + 32) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_right hE1 hB0'
          have hres := approxEcalReLeAtExit4 lam R H A hlam hR hlamR τ h1 κ hτ1 hκeq hκI hcim
            hκlog hH hHR hA0 hAr16 (u 0) hx00lo hle hy
          have hL0' : L 0 ≤ R + 2 := by simpa only [L, ha] using hres
          linarith

        refine ⟨?_, ?_⟩
        · intro i hi
          have hi0 : i = 0 := Nat.le_zero.mp hi
          subst hi0
          exact ⟨hstrip.1, hstrip.2, hζ0n, by linarith [h4r], by simp, by simp⟩
        · intro i hi
          exact absurd hi (Nat.not_lt_zero i)
      · -- step
        obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hjpos)
        have hprev' : ∀ i < j', R + 2 < L i := fun i hi => hprev i (by omega)
        have hIj' := ih j' (by omega) hprev'
        have hLj' : R + 2 < L j' := hprev j' (by omega)
        have hx1' : R / 4 + 2 ≤ (u j').re := (hIj'.1 j' le_rfl).1
        have hx2' : (u j').re ≤ Real.pi / lam - R / 4 := (hIj'.1 j' le_rfl).2.1
        have hzn' : ‖ζ j'‖ ≤ 4 / R := (hIj'.1 j' le_rfl).2.2.1
        have hzr' : ‖ζ j'‖ < r := (hIj'.1 j' le_rfl).2.2.2.1
        have hLlo' : L 0 - 2 * (j' : ℝ) ≤ L j' := (hIj'.1 j' le_rfl).2.2.2.2.1
        have hLup' : L j' ≤ L 0 - (j' : ℝ) / 4 := (hIj'.1 j' le_rfl).2.2.2.2.2
        -- the drift bound at `j'`
        have hstrip' := hIj'.1
        have hdec' : ∀ i < j', (u (i + 1)).re ≤ (u i).re - 1 / 3 :=
          fun i hi => (hIj'.2 i hi).1
        -- hence `(u j').re > R/4 + 4`
        have hxg : R / 4 + 4 < (u j').re := by
          by_contra hcon
          push_neg at hcon
          exact absurd (hthr j' hcon (by linarith) hstrip' hdec') (by linarith)
        -- the one-step bounds
        have hstep := modelDisp_step_bounds2 lam R B hlam hR hlamR hB0 h τ h1 κ A r hA hr hb
          hκeq hh1 hτ1 hAr hrr hκR (u j') hx1' hx2' hzn' hzr'
        obtain ⟨hΦ1, hΦ2, hΦ3, hΔ1, hΔ2, hslit'⟩ := hstep
        have hΦ1' : (-2 : ℝ) ≤ (Φ j').re := by simpa only [Φ, ha] using hΦ1
        have hΦ2' : (Φ j').re ≤ -(1 / 3) := by simpa only [Φ, ha] using hΦ2
        have hxsucc : (u (j' + 1)).re = (u j').re + (Φ j').re := by
          rw [hu j', Complex.add_re]
        have hΔ1' : (-2 : ℝ) ≤ L (j' + 1) - L j' := by
          simp only [L]
          rw [hu j']
          exact hΔ1
        have hΔ2' : L (j' + 1) - L j' ≤ -(1 / 4) := by
          simp only [L]
          rw [hu j']
          exact hΔ2
        -- new strip and chart bounds
        have hx1'' : R / 4 + 2 ≤ (u (j' + 1)).re := by rw [hxsucc]; linarith
        have hx2'' : (u (j' + 1)).re ≤ Real.pi / lam - R / 4 := by rw [hxsucc]; linarith
        have hzn'' : ‖ζ (j' + 1)‖ ≤ 4 / R := by
          have := ecalPt_norm_le_four_div lam R hlam hR hlamR (u (j' + 1)) hx1'' hx2''
          simpa only [ζ, ha] using this
        have hzr'' : ‖ζ (j' + 1)‖ < r := by linarith [hzn'', h4r]
        -- level bounds
        have hLlo'' : L 0 - 2 * ((j' + 1 : ℕ) : ℝ) ≤ L (j' + 1) := by
          push_cast; linarith
        have hLup'' : L (j' + 1) ≤ L 0 - ((j' + 1 : ℕ) : ℝ) / 4 := by
          push_cast; linarith
        constructor
        · intro i hi
          rcases Nat.lt_or_eq_of_le hi with hlt | heq
          · exact hIj'.1 i (Nat.lt_succ_iff.mp hlt)
          · subst heq
            exact ⟨hx1'', hx2'', hzn'', hzr'', hLlo'', hLup''⟩
        · intro i hi
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
          · exact hIj'.2 i hlt
          · subst heq
            exact ⟨by rw [hxsucc]; linarith, by linarith, by linarith,
              fun t ht => by simpa only [a, ha] using hslit' t ht⟩
  -- existence of the exit index
  set N : ℕ := ⌊4 * (Real.pi / lam)⌋₊ + 4 with hN
  have hex : ∃ j : ℕ, j ≤ N ∧ L j ≤ R + 2 := by
    by_contra hc
    rw [not_exists] at hc
    have hc' : ∀ j, j ≤ N → R + 2 < L j := by
      intro j hj
      by_contra hlt
      exact hc j ⟨hj, le_of_not_gt hlt⟩
    have hIN := hInv N (fun i hi => hc' i (le_of_lt hi))
    have hLN : L N ≤ L 0 - (N : ℝ) / 4 := (hIN.1 N le_rfl).2.2.2.2.2
    have hNge : Real.pi / lam + 3 / 4 ≤ (N : ℝ) / 4 := by
      rw [hN]
      have hfl : 4 * (Real.pi / lam) - 1 ≤ ((⌊4 * (Real.pi / lam)⌋₊ : ℕ) : ℝ) :=
        le_of_lt (Nat.sub_one_lt_floor (4 * (Real.pi / lam)))
      push_cast
      linarith
    have hNx : R + 2 < L N := hc' N le_rfl
    linarith
  set k : ℕ := Nat.find hex with hk
  have hkspec : k ≤ N ∧ L k ≤ R + 2 := Nat.find_spec hex
  have hkmin : ∀ i < k, R + 2 < L i := by
    intro i hi
    have h1 := Nat.find_min hex hi
    have h2 : i ≤ N := le_of_lt (lt_of_lt_of_le hi hkspec.1)
    by_contra hcon
    exact h1 ⟨h2, le_of_not_gt hcon⟩
  have hIk := hInv k hkmin
  have hLk_le : L k ≤ R + 2 := hkspec.2
  have hstripk := hIk.1
  have hdeck : ∀ i < k, (u (i + 1)).re ≤ (u i).re - 1 / 3 := fun i hi => (hIk.2 i hi).1
  have hkpos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · exfalso
      have h0' : L 0 ≤ R + 2 := by
        have := hLk_le
        rw [h0] at this
        exact this
      linarith
    · exact hpos
  have hLk_ge : R ≤ L k := by
    have hkm1 : k - 1 < k := by omega
    have hprev : R + 2 < L (k - 1) := hkmin (k - 1) hkm1
    have hdecL : L (k - 1) - 2 ≤ L (k - 1 + 1) := (hIk.2 (k - 1) hkm1).2.1
    have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
    have hLk : L (k - 1 + 1) = L k := congrArg L hk1
    linarith [hLk.le, hLk.ge, hdecL, hprev]
  -- `Re ζ k > 0`
  have hylk : lam * |(u k).im| ≤ 1 := by
    have hhu : ∀ i < k, Work.Implosion.modelOrbit a h (i + 1) u0
        = Work.Implosion.modelOrbit a h i u0
          + Work.Implosion.modelDisp ((lam : ℂ) * Complex.I) h
              (Work.Implosion.modelOrbit a h i u0) := by
      intro i hi
      simpa only [u, Φ, ha] using hu i
    have hhtop : Real.pi / lam - 2 * R ≤ (Work.Implosion.modelOrbit a h 0 u0).re := by
      simpa only [u, Work.Implosion.modelOrbit_zero] using htop
    have hhx1 : ∀ i ≤ k, R / 4 + 2 ≤ (Work.Implosion.modelOrbit a h i u0).re := by
      intro i hi
      simpa only [u] using (hstripk i hi).1
    have hhx2 : ∀ i ≤ k, (Work.Implosion.modelOrbit a h i u0).re ≤ Real.pi / lam - R / 4 := by
      intro i hi
      simpa only [u] using (hstripk i hi).2.1
    have hhdec : ∀ i < k, (Work.Implosion.modelOrbit a h (i + 1) u0).re
        ≤ (Work.Implosion.modelOrbit a h i u0).re - 1 / 3 := by
      intro i hi
      simpa only [u] using hdeck i hi
    have hhzn : ∀ i ≤ k, ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I)
        (Work.Implosion.modelOrbit a h i u0)‖ ≤ 4 / R := by
      intro i hi
      simpa only [ζ, u] using (hstripk i hi).2.2.1
    have hhzr : ∀ i ≤ k, ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I)
        (Work.Implosion.modelOrbit a h i u0)‖ < r := by
      intro i hi
      simpa only [ζ, u] using (hstripk i hi).2.2.2.1
    have hhy0 : |(Work.Implosion.modelOrbit a h 0 u0).im| ≤ R / 4 + 4 + Real.log R := by
      have h' : |(u 0).im| ≤ R / 4 + 4 + Real.log R := by linarith [hy00, h2H8]
      simpa only [u, Work.Implosion.modelOrbit_zero] using h'
    exact orbitImLamSmall lam R hlam hR hlamR h τ h1 A r B hA hr hb hh1 hτ1 hAr hrr hτpi k
      (fun i => Work.Implosion.modelOrbit a h i u0) hhu hhtop hhx1 hhx2 hhdec hhzn hhzr hhy0
  have hlxk : lam * (u k).re < Real.pi / 2 :=
    lam_re_lt_half_of_level2 lam R H A |(u k).im| hlam hR hlamR τ h1 κ hτ1 hκeq hκI hκlog
      hH hHR hA0 hAr16 (u k) (hstripk k le_rfl).2.1 (by simpa only [L, ha] using hLk_le)
      (le_refl _) hylk
  have hζkre : 0 < (ζ k).re := by
    have h1 : 0 < (u k).re := by linarith [(hstripk k le_rfl).1]
    have h2 : (u k).re < Real.pi / (2 * lam) := by
      rw [lt_div_iff₀ (by positivity)]
      linarith
    simpa only [ζ, ha] using ecalPt_re_pos lam hlam (u k) h1 h2
  -- the `GoodTransitRot` conditions
  have hGT : ∀ j ≤ k, Work.PARIMPL.GoodTransitRot a h τ lam (R / 4) (u j) := by
    intro j hj
    have hsj := hstripk j hj
    have hslitj : Complex.sinh (a * (u j)) / a ∈ Complex.slitPlane := by
      have h1 : 0 < lam * (u j).re := mul_pos hlam (by linarith [hsj.1])
      have h2 : lam * (u j).re < Real.pi := by
        have h3 : lam * (Real.pi / lam - R / 4) = Real.pi - lam * R / 4 := by field_simp
        have h3b : lam * (u j).re ≤ Real.pi - lam * R / 4 :=
          calc lam * (u j).re ≤ lam * (Real.pi / lam - R / 4) :=
                mul_le_mul_of_nonneg_left hsj.2.1 hlam.le
            _ = Real.pi - lam * R / 4 := h3
        have h5 : 0 < lam * R / 4 := by positivity
        linarith
      have hres := sinh_div_slitPlane_of_strip lam hlam (u j) h1 h2
      simpa only [ha] using hres
    exact goodTransitRotOfStrip lam R A B r hlam hR hlamR hA0 hB0 h τ h1 hb hh1 hτ1 hAr
      (u j) hsj.1 hsj.2.1 (by simpa only [ζ, ha] using hsj.2.2.1)
      (by simpa only [ζ, ha] using hsj.2.2.2.1) hslitj
  have hslitseg : ∀ j < k, ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Complex.sinh (a * (u j + (t : ℂ) * Φ j)) / a ∈ Complex.slitPlane := by
    intro j hj t ht
    have hres := (hIk.2 j hj).2.2.2 t ht
    simpa only [a, ha] using hres
  have hζrk : ∀ j ≤ k, ‖ζ j‖ < r := fun j hj => (hstripk j hj).2.2.2.1
  have htransit := hC₁ h τ h1 hb hh1 lam (R / 4) a u0 k hlam ha.symm
    (fun j hj => hGT j hj)
    (fun j hj => hζrk j hj)
    (fun j hj t ht => hslitseg j hj t ht)
  have hk_le : (k : ℝ) ≤ 4 * (Real.pi / lam) + 4 := by
    have hNle : (N : ℝ) ≤ 4 * (Real.pi / lam) + 4 := by
      rw [hN]
      have hfl : ((⌊4 * (Real.pi / lam)⌋₊ : ℕ) : ℝ) ≤ 4 * (Real.pi / lam) :=
        Nat.floor_le (show (0 : ℝ) ≤ 4 * (Real.pi / lam) by positivity)
      push_cast
      linarith
    have hkN : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkspec.1
    linarith
  -- the final error estimate
  have herr : ‖Work.Implosion.approxEcal a κ (u k) - Work.Implosion.approxEcal a κ (u 0)
      + (k : ℂ)‖ ≤ (5 * C₁ + 1) / R := by
    have h1 : ‖Work.Implosion.approxEcal a κ (u k) - Work.Implosion.approxEcal a κ (u 0)
        + (k : ℂ) * τ‖ ≤ C₁ * (1 / (R / 4) + lam) := by
      have hres := htransit
      simpa only [hκeq, u, Work.Implosion.modelOrbit_zero] using hres
    have htri : ‖Work.Implosion.approxEcal a κ (u k) - Work.Implosion.approxEcal a κ (u 0)
        + (k : ℂ)‖ ≤ ‖Work.Implosion.approxEcal a κ (u k)
            - Work.Implosion.approxEcal a κ (u 0) + (k : ℂ) * τ‖
          + ‖(k : ℂ) * τ - (k : ℂ)‖ := by
      have h := norm_add_le (Work.Implosion.approxEcal a κ (u k)
          - Work.Implosion.approxEcal a κ (u 0) + (k : ℂ) * τ) ((k : ℂ) - (k : ℂ) * τ)
      have he : (Work.Implosion.approxEcal a κ (u k) - Work.Implosion.approxEcal a κ (u 0)
            + (k : ℂ) * τ) + ((k : ℂ) - (k : ℂ) * τ)
          = Work.Implosion.approxEcal a κ (u k) - Work.Implosion.approxEcal a κ (u 0)
            + (k : ℂ) := by ring
      rw [he, norm_sub_rev] at h
      exact h
    have hkt : ‖(k : ℂ) * τ - (k : ℂ)‖ ≤ 3 / (4 * R) := by
      have he : (k : ℂ) * τ - (k : ℂ) = (k : ℂ) * (τ - 1) := by ring
      rw [he, norm_mul, Complex.norm_natCast]
      exact natCast_mul_le lam R (k : ℝ) ‖τ - 1‖ hlam hR hlamR (norm_nonneg _) hk_le hτpi
    have h12 : C₁ * (1 / (R / 4) + lam) + 3 / (4 * R) ≤ (5 * C₁ + 1) / R := by
      have he : 1 / (R / 4) = 4 / R := by ring
      rw [he]
      have h13 : lam ≤ 1 / R := by
        have h14 : lam ≤ 1 / R ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
        have h15 : 1 / R ^ 2 ≤ 1 / R := by
          rw [div_le_div_iff₀ (by positivity) hRpos]
          nlinarith [hR]
        linarith
      have hA : C₁ * (4 / R + lam) ≤ C₁ * (5 / R) := by
        have h4 : 4 / R + lam ≤ 5 / R := by
          have he : 4 / R + lam ≤ 4 / R + 1 / R := by linarith [h13]
          have h5 : 4 / R + 1 / R = 5 / R := by ring
          linarith [he, h5.le, h5.ge]
        exact mul_le_mul_of_nonneg_left h4 hC₁0
      have hB : 3 / (4 * R) ≤ 1 / R := by
        rw [div_le_div_iff₀ (by positivity) hRpos]
        linarith
      have hC : C₁ * (5 / R) + 1 / R = (5 * C₁ + 1) / R := by ring
      linarith [hA, hB, hC.le, hC.ge]
    linarith [h1, htri, hkt, h12]
  refine ⟨k, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hLk_ge, hLk_le⟩
  · exact hζkre
  · exact (hstripk k le_rfl).2.2.1
  · exact hGT
  · exact hζrk
  · exact fun j hj t ht => hslitseg j hj t ht
  · exact herr

end

end Work.PARIMPL2.Direct
