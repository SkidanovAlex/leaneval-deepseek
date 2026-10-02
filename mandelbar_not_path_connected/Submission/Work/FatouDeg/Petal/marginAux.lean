import Mathlib
import Submission.Work.FatouDeg.Petal.DefsAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouDeg.Petal

/-! ## The Cauchy margin of the petal inside the working domain

This file proves `Work.FatouDeg.Petal.marginAux`: every point of the petal
`Pet m ρ = {‖z‖ < ρ} ∩ {m |Im z| < Re z}` has a ball of radius `(1/(32m)) ‖z‖`
contained in the working domain `Dom m ρ = {‖z‖ < 2ρ} ∩ {(7m/8) |Im z| < Re z}`.

The two ingredients are

* `pet_norm_lt_sqrt_two_mul_re`: on the sector `m |Im z| < Re z` with `m ≥ 1` one has
  `‖z‖ < √2 * Re z`, i.e. `Re z > ‖z‖/√2`;
* `margin_aux_const`: the numerical inequality `7/256 + 1/(32m) ≤ √2/16` for `m ≥ 4`
  (note `√2/16 = 1/(8√2)`, and `(1/(32m))(1 + 7m/8) = 1/(32m) + 7/256`).
-/

/-- On the sector `m * |Im z| < Re z` (with `m ≥ 1`), the real part dominates the modulus:
`‖z‖ < √2 * Re z`. -/
lemma pet_norm_lt_sqrt_two_mul_re {m : ℕ} (hm : 1 ≤ m) {z : ℂ}
    (hz : (m : ℝ) * |z.im| < z.re) : ‖z‖ < Real.sqrt 2 * z.re := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have him : |z.im| < z.re := by
    have h := mul_le_mul_of_nonneg_right hm1 (abs_nonneg z.im)
    linarith
  have hre : 0 < z.re := lt_of_le_of_lt (abs_nonneg z.im) him
  have hsq : z.im ^ 2 < z.re ^ 2 := sq_lt_sq.mpr (by rwa [abs_of_pos hre])
  have hmain : ‖z‖ ^ 2 < (Real.sqrt 2 * z.re) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [hs, hsq]
  have h2pos : (0 : ℝ) ≤ Real.sqrt 2 * z.re := by positivity
  have := sq_lt_sq.mp hmain
  rwa [abs_of_nonneg (norm_nonneg z), abs_of_nonneg h2pos] at this

/-- Numerical constant: for `m ≥ 3`, `7/256 + 1/(32m) ≤ √2/16 = 1/(8√2)`. -/
lemma margin_aux_const {m : ℕ} (hm : 3 ≤ m) :
    (7 : ℝ) / 256 + 1 / (32 * (m : ℝ)) ≤ Real.sqrt 2 / 16 := by
  have hm3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h1 : 1 / (32 * (m : ℝ)) ≤ 1 / 96 := by
    have h : (96 : ℝ) ≤ 32 * (m : ℝ) := by linarith
    exact one_div_le_one_div_of_le (by norm_num) h
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  have h3 : (29 : ℝ) / 768 ≤ Real.sqrt 2 / 16 := by nlinarith [h2]
  linarith

/-- **The petal has a Cauchy margin inside the working domain.**

Every point `z` of the petal `Pet m ρ = {‖z‖ < ρ} ∩ {m |Im z| < Re z}` has the ball of radius
`(1/(32m)) * ‖z‖` around it contained in the working domain
`Dom m ρ = {‖z‖ < 2ρ} ∩ {(7m/8) |Im z| < Re z}`.

Indeed for `z ∈ Pet m ρ` one has `Re z ≥ ‖z‖/√2` and
`Re z - (7m/8)|Im z| ≥ Re z/8 ≥ ‖z‖/(8√2)`, while `(1/(32m))(1 + 7m/8) ≤ 0.036 < 1/(8√2)` for
`m ≥ 4`; the Lipschitz estimates `|Re w - Re z| ≤ ‖w - z‖` and `| |Im w| - |Im z| | ≤ ‖w - z‖`
then give the sector condition for `w`, and `‖w‖ ≤ ‖z‖(1 + 1/(32m)) < 2ρ`. -/
theorem marginAux (m : ℕ) (hm : 3 ≤ m) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ z ∈ Pet m ρ, ∀ w : ℂ, ‖w - z‖ ≤ (1 / (32 * (m : ℝ))) * ‖z‖ → w ∈ Dom m ρ := by
  intro z hz w hw
  rw [mem_Pet] at hz
  obtain ⟨hz_ball, hz_sect⟩ := hz
  rw [mem_Dom]
  have hm3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hkey : ‖z‖ < Real.sqrt 2 * z.re := pet_norm_lt_sqrt_two_mul_re (by omega : 1 ≤ m) hz_sect
  -- `z.re / 8` dominates `7‖z‖/256 + ‖z‖/(32m)`
  have harith : 7 * ‖z‖ / 256 + ‖z‖ / (32 * (m : ℝ)) ≤ z.re / 8 := by
    have hc := margin_aux_const hm
    have h1 : ‖z‖ * (7 / 256 + 1 / (32 * (m : ℝ))) ≤ ‖z‖ * (Real.sqrt 2 / 16) :=
      mul_le_mul_of_nonneg_left hc (norm_nonneg z)
    have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := by
      rw [← sq, Real.sq_sqrt (by norm_num)]
    have h2 : ‖z‖ * (Real.sqrt 2 / 16) < z.re / 8 := by
      have hsp : (0 : ℝ) < Real.sqrt 2 / 16 := by
        have := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num); linarith
      have hstep := mul_lt_mul_of_pos_right hkey hsp
      rw [show Real.sqrt 2 * z.re * (Real.sqrt 2 / 16) = z.re / 8 by
        rw [show Real.sqrt 2 * z.re * (Real.sqrt 2 / 16)
              = z.re * (Real.sqrt 2 * Real.sqrt 2) / 16 by ring, hs]; ring] at hstep
      exact hstep
    have h3 : ‖z‖ * (7 / 256 + 1 / (32 * (m : ℝ))) =
        7 * ‖z‖ / 256 + ‖z‖ / (32 * (m : ℝ)) := by ring
    linarith
  have hRe : |w.re - z.re| ≤ ‖w - z‖ := by
    have := Complex.abs_re_le_norm (w - z)
    rwa [Complex.sub_re] at this
  have hIm : |(|w.im| - |z.im|)| ≤ ‖w - z‖ := by
    calc |(|w.im| - |z.im|)| ≤ |w.im - z.im| := abs_abs_sub_abs_le_abs_sub _ _
      _ = |(w - z).im| := by rw [Complex.sub_im]
      _ ≤ ‖w - z‖ := Complex.abs_im_le_norm _
  -- the sector condition at `w`
  have hsect : (7 * (m : ℝ) / 8) * |w.im| < w.re := by
    have hc_nn : (0 : ℝ) ≤ 7 * (m : ℝ) / 8 := by linarith
    have hwre : z.re - ‖w - z‖ ≤ w.re := by
      have := (abs_le.mp hRe).1
      linarith
    have hwim : |w.im| ≤ |z.im| + ‖w - z‖ := by
      have := (abs_le.mp hIm).2
      linarith
    have hA : (7 * (m : ℝ) / 8) * |w.im| ≤
        (7 * (m : ℝ) / 8) * |z.im| + (7 * (m : ℝ) / 8) * ‖w - z‖ := by
      calc (7 * (m : ℝ) / 8) * |w.im| ≤ (7 * (m : ℝ) / 8) * (|z.im| + ‖w - z‖) :=
            mul_le_mul_of_nonneg_left hwim hc_nn
        _ = _ := by ring
    have hB : (7 * (m : ℝ) / 8) * |z.im| < (7 / 8) * z.re := by
      have h : (7 * (m : ℝ) / 8) * |z.im| = (7 / 8) * ((m : ℝ) * |z.im|) := by ring
      rw [h]
      exact mul_lt_mul_of_pos_left hz_sect (by norm_num)
    have hE : (7 * (m : ℝ) / 8) * ‖w - z‖ ≤ 7 * ‖z‖ / 256 := by
      have hd : (7 * (m : ℝ) / 8) * ((1 / (32 * (m : ℝ))) * ‖z‖) = 7 * ‖z‖ / 256 := by
        field_simp
        ring
      calc (7 * (m : ℝ) / 8) * ‖w - z‖
          ≤ (7 * (m : ℝ) / 8) * ((1 / (32 * (m : ℝ))) * ‖z‖) :=
            mul_le_mul_of_nonneg_left hw hc_nn
        _ = 7 * ‖z‖ / 256 := hd
    have hdz : z.re - ‖z‖ / (32 * (m : ℝ)) ≤ w.re := by
      have hD : (1 / (32 * (m : ℝ))) * ‖z‖ = ‖z‖ / (32 * (m : ℝ)) := by ring
      have hw' : ‖w - z‖ ≤ ‖z‖ / (32 * (m : ℝ)) := by rw [← hD]; exact hw
      linarith
    linarith [hA, hB, hE, harith, hdz]
  refine ⟨?_, hsect⟩
  -- the ball condition at `w`
  have hnorm : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
    have := norm_add_le z (w - z)
    rwa [show z + (w - z) = w by ring] at this
  have hstep : ‖z‖ + ‖w - z‖ ≤ ‖z‖ + (1 / (32 * (m : ℝ))) * ‖z‖ := add_le_add le_rfl hw
  have hlt : ‖z‖ + (1 / (32 * (m : ℝ))) * ‖z‖ < 2 * ρ := by
    have hm32 : 1 / (32 * (m : ℝ)) ≤ 1 / 96 := by
      have h : (96 : ℝ) ≤ 32 * (m : ℝ) := by linarith
      exact one_div_le_one_div_of_le (by norm_num) h
    have hfac : (0 : ℝ) < 1 + 1 / (32 * (m : ℝ)) := by positivity
    have ha : ‖z‖ * (1 + 1 / (32 * (m : ℝ))) < ρ * (1 + 1 / (32 * (m : ℝ))) :=
      mul_lt_mul_of_pos_right hz_ball hfac
    have hb : ρ * (1 + 1 / (32 * (m : ℝ))) < ρ * 2 :=
      mul_lt_mul_of_pos_left (by linarith) hρ
    have heq : ‖z‖ + (1 / (32 * (m : ℝ))) * ‖z‖ = ‖z‖ * (1 + 1 / (32 * (m : ℝ))) := by ring
    linarith
  linarith

end Work.FatouDeg.Petal
