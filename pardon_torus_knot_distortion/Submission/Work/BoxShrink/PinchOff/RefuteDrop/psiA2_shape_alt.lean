import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.dropTrace

namespace Work.BoxShrink.PinchOff.RefuteDrop.ZShape

open Work.BoxShrink.PinchOff.RefuteDrop

noncomputable section

/-!
## The `z`-window of the `A` branch

The function `psiA2 u = 3 * |trN2 u| - (7/5) * (2 * (97/100) - trS u)` is the `z`-window of the
`A` branch of the trace: it vanishes exactly where the branch meets one of the two `z`-faces of
the box.  This file determines the shape of its sublevel set on `[0, 2π]`.
-/

/-- `psiA2 u / 3`. -/
def psiE (u : ℝ) : ℝ := |trN2 u| - (7/15) * (2 * (97/100) - trS u)

/-- The `A` window with the sign of `trN2` removed (the value of `psiE` where `trN2 ≥ 0`). -/
def psiF1 (u : ℝ) : ℝ := trN2 u - (7/15) * (2 * (97/100) - trS u)

/-- The `A` window with the sign of `trN2` removed (the value of `psiE` where `trN2 ≤ 0`). -/
def psiF2 (u : ℝ) : ℝ := -trN2 u - (7/15) * (2 * (97/100) - trS u)

/-- The derivative of `trA`. -/
def trAd (u : ℝ) : ℝ := (2/25) * Real.sin u - (39/100) * Real.cos u

theorem psiA2_eq_three_psiE (u : ℝ) : psiA2 u = 3 * psiE u := by
  simp only [psiA2, psiE]
  ring

theorem psiE_eq_max (u : ℝ) : psiE u = max (psiF1 u) (psiF2 u) := by
  simp only [psiE, psiF1, psiF2]
  rcases le_total 0 (trN2 u) with h | h
  · rw [max_eq_left, abs_of_nonneg h]; linarith
  · rw [max_eq_right, abs_of_nonpos h]; linarith

/-! ## Periodicity -/

theorem trA_add_pi (u : ℝ) : trA (u + Real.pi) = -trA u := by
  simp only [trA, Real.cos_add_pi, Real.sin_add_pi]
  ring

theorem trB2_add_pi (u : ℝ) : trB2 (u + Real.pi) = -trB2 u := by
  simp only [trB2, Real.cos_add_pi, Real.sin_add_pi]
  ring

theorem trN2_add_pi (u : ℝ) : trN2 (u + Real.pi) = -trN2 u := by
  rw [trN2, trN2, trB2_add_pi, trA_add_pi]
  ring

theorem trS_add_pi (u : ℝ) : trS (u + Real.pi) = trS u := by
  rw [trS, trS, trA_add_pi]
  norm_num

theorem psiE_add_pi (u : ℝ) : psiE (u + Real.pi) = psiE u := by
  rw [psiE, psiE, trN2_add_pi, trS_add_pi, abs_neg]

theorem psiA2_add_pi (u : ℝ) : psiA2 (u + Real.pi) = psiA2 u := by
  rw [psiA2_eq_three_psiE, psiA2_eq_three_psiE, psiE_add_pi]

/-! ## Derivatives -/

theorem hasDerivAt_trA (u : ℝ) : HasDerivAt trA (trAd u) u := by
  have htrA : trA = fun v : ℝ => -(2/25) * Real.cos v - (39/100) * Real.sin v := rfl
  rw [htrA]
  have h1 : HasDerivAt (fun v : ℝ => -(2/25) * Real.cos v) ((-(2/25)) * (-(Real.sin u))) u :=
    (Real.hasDerivAt_cos u).const_mul (-(2/25))
  have h2 : HasDerivAt (fun v : ℝ => (39/100) * Real.sin v) ((39/100) * Real.cos u) u :=
    (Real.hasDerivAt_sin u).const_mul (39/100)
  have h := h1.sub h2
  have hval : ((-(2/25)) * (-(Real.sin u)) - (39/100) * Real.cos u) = trAd u := by
    simp only [trAd]; ring
  rwa [hval] at h

theorem deriv_trA (u : ℝ) : deriv trA u = trAd u := (hasDerivAt_trA u).deriv

theorem hasDerivAt_trS (u : ℝ) : HasDerivAt trS (-(3 * trA u * trAd u) / trS u) u := by
  have hA : HasDerivAt trA (trAd u) u := hasDerivAt_trA u
  have hp : HasDerivAt (fun v : ℝ => (trA v)^2) (2 * (trA u)^1 * trAd u) u := hA.pow 2
  have h2 : HasDerivAt (fun v : ℝ => (97/100)^2 - 3 * (trA v)^2)
      (0 - 3 * (2 * (trA u)^1 * trAd u)) u :=
    (hasDerivAt_const u ((97/100)^2)).sub (hp.const_mul 3)
  have h3 := h2.sqrt (ne_of_gt (trS_arg_pos u))
  have h4 : HasDerivAt trS
      ((0 - 3 * (2 * (trA u)^1 * trAd u)) / (2 * Real.sqrt ((97/100)^2 - 3 * (trA u)^2))) u := h3
  have hval : (0 - 3 * (2 * (trA u)^1 * trAd u)) / (2 * Real.sqrt ((97/100)^2 - 3 * (trA u)^2))
      = -(3 * trA u * trAd u) / trS u := by
    rw [show (97/100)^2 - 3 * (trA u)^2 = (trS u)^2 from (trS_sq u).symm,
      Real.sqrt_sq (trS_nonneg u)]
    ring
  rwa [hval] at h4

theorem deriv_trS (u : ℝ) : deriv trS u = -(3 * trA u * trAd u) / trS u :=
  (hasDerivAt_trS u).deriv

theorem hasDerivAt_trN2 (u : ℝ) :
    HasDerivAt trN2 (-(209/400) * Real.sin u + (14329/10000) * Real.cos u) u := by
  have htrN2 : trN2 = fun v : ℝ => (209/400) * Real.cos v + (14329/10000) * Real.sin v := by
    funext v
    simp only [trN2, trB2, trA]
    ring
  rw [htrN2]
  have h1 : HasDerivAt (fun v : ℝ => (209/400) * Real.cos v) ((209/400) * (-(Real.sin u))) u :=
    (Real.hasDerivAt_cos u).const_mul (209/400)
  have h2 : HasDerivAt (fun v : ℝ => (14329/10000) * Real.sin v) ((14329/10000) * Real.cos u) u :=
    (Real.hasDerivAt_sin u).const_mul (14329/10000)
  have h := h1.add h2
  have hval : ((209/400) * (-(Real.sin u)) + (14329/10000) * Real.cos u)
      = (-(209/400) * Real.sin u + (14329/10000) * Real.cos u) := by ring
  rwa [hval] at h

theorem deriv_trN2 (u : ℝ) :
    deriv trN2 u = -(209/400) * Real.sin u + (14329/10000) * Real.cos u :=
  (hasDerivAt_trN2 u).deriv

theorem hasDerivAt_psiF1 (u : ℝ) : HasDerivAt psiF1
    ((-(209/400) * Real.sin u + (14329/10000) * Real.cos u)
      + (7/15) * (-(3 * trA u * trAd u) / trS u)) u := by
  have h1 : HasDerivAt (fun v : ℝ => trN2 v - (7/15) * (2 * (97/100) - trS v))
      ((-(209/400) * Real.sin u + (14329/10000) * Real.cos u)
        - (7/15) * (0 - (-(3 * trA u * trAd u) / trS u))) u := by
    refine (hasDerivAt_trN2 u).sub ?_
    exact ((hasDerivAt_const u (2 * (97/100))).sub (hasDerivAt_trS u)).const_mul (7/15)
  have hval : ((-(209/400) * Real.sin u + (14329/10000) * Real.cos u)
        - (7/15) * (0 - (-(3 * trA u * trAd u) / trS u)))
      = ((-(209/400) * Real.sin u + (14329/10000) * Real.cos u)
      + (7/15) * (-(3 * trA u * trAd u) / trS u)) := by ring
  rw [hval] at h1
  exact h1

theorem deriv_psiF1 (u : ℝ) : deriv psiF1 u =
    ((-(209/400) * Real.sin u + (14329/10000) * Real.cos u)
      + (7/15) * (-(3 * trA u * trAd u) / trS u)) :=
  (hasDerivAt_psiF1 u).deriv

theorem hasDerivAt_psiF2 (u : ℝ) : HasDerivAt psiF2
    ((-(-(209/400) * Real.sin u + (14329/10000) * Real.cos u))
      + (7/15) * (-(3 * trA u * trAd u) / trS u)) u := by
  have h1 : HasDerivAt (fun v : ℝ => -trN2 v - (7/15) * (2 * (97/100) - trS v))
      ((-(-(209/400) * Real.sin u + (14329/10000) * Real.cos u))
        - (7/15) * (0 - (-(3 * trA u * trAd u) / trS u))) u := by
    refine ((hasDerivAt_trN2 u).neg).sub ?_
    exact ((hasDerivAt_const u (2 * (97/100))).sub (hasDerivAt_trS u)).const_mul (7/15)
  have hval : ((-(-(209/400) * Real.sin u + (14329/10000) * Real.cos u))
        - (7/15) * (0 - (-(3 * trA u * trAd u) / trS u)))
      = ((-(-(209/400) * Real.sin u + (14329/10000) * Real.cos u))
      + (7/15) * (-(3 * trA u * trAd u) / trS u)) := by ring
  rw [hval] at h1
  exact h1

theorem deriv_psiF2 (u : ℝ) : deriv psiF2 u =
    ((-(-(209/400) * Real.sin u + (14329/10000) * Real.cos u))
      + (7/15) * (-(3 * trA u * trAd u) / trS u)) :=
  (hasDerivAt_psiF2 u).deriv

theorem continuous_trN2 : Continuous trN2 := by
  have h : trN2 = fun u : ℝ => (209/400) * Real.cos u + (14329/10000) * Real.sin u := by
    funext u; simp only [trN2, trB2, trA]; ring
  rw [h]; fun_prop

theorem continuous_psiF1 : Continuous psiF1 := by
  have h1 := continuous_trN2
  have h2 := continuous_trS
  unfold psiF1
  fun_prop

theorem continuous_psiF2 : Continuous psiF2 := by
  have h1 := continuous_trN2
  have h2 := continuous_trS
  unfold psiF2
  fun_prop

theorem continuous_psiE : Continuous psiE := by
  have h1 := continuous_trN2
  have h2 := continuous_trS
  unfold psiE
  fun_prop

/-! ## Elementary estimates -/

theorem trA_abs_le (u : ℝ) : |trA u| ≤ 2/5 := by
  have h := trA_sq_le u
  have h2 : (trA u)^2 ≤ (2/5 : ℝ)^2 := by norm_num at h ⊢; linarith
  calc |trA u| = Real.sqrt ((trA u)^2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((2/5 : ℝ)^2) := Real.sqrt_le_sqrt h2
    _ = 2/5 := Real.sqrt_sq (by norm_num)

theorem trAd_abs_le (u : ℝ) : |trAd u| ≤ 47/100 := by
  have h1 : |Real.sin u| ≤ 1 := Real.abs_sin_le_one u
  have h2 : |Real.cos u| ≤ 1 := Real.abs_cos_le_one u
  have h3 : |(2/25) * Real.sin u| = (2/25) * |Real.sin u| := by
    rw [abs_mul]; norm_num
  have h4 : |(39/100) * Real.cos u| = (39/100) * |Real.cos u| := by
    rw [abs_mul]; norm_num
  have h5 : |(2/25) * Real.sin u - (39/100) * Real.cos u|
      ≤ |(2/25) * Real.sin u| + |(39/100) * Real.cos u| := abs_sub _ _
  simp only [trAd]
  rw [h3, h4] at h5
  linarith

theorem trS_ge (u : ℝ) : 68/100 ≤ trS u := by
  have h := trS_sq u
  have hA := trA_sq_le u
  have hnn := trS_nonneg u
  nlinarith [h, hA, hnn]

/-! ## Monotonicity -/

theorem cos_le_neg_21_29 {u : ℝ} (hu : u ∈ Set.Icc (ang (5/2)) Real.pi) :
    Real.cos u ≤ -(21/29) := by
  have h1 : ang (5/2) ∈ Set.Icc (0:ℝ) Real.pi :=
    ⟨le_of_lt (ang_pos (by norm_num)), le_of_lt (ang_lt_pi (by norm_num))⟩
  have h2 : u ∈ Set.Icc (0:ℝ) Real.pi := ⟨le_trans h1.1 hu.1, hu.2⟩
  have h3 : Real.cos u ≤ Real.cos (ang (5/2)) :=
    Real.strictAntiOn_cos.antitoneOn h1 h2 hu.1
  rw [cos_ang] at h3
  norm_num at h3
  linarith

theorem sin_nonneg_of_ang {u : ℝ} (hu : u ∈ Set.Icc (ang (5/2)) Real.pi) :
    0 ≤ Real.sin u := by
  refine Real.sin_nonneg_of_mem_Icc ⟨?_, hu.2⟩
  exact le_trans (le_of_lt (ang_pos (by norm_num))) hu.1

theorem trN2_deriv_neg {u : ℝ} (hu : u ∈ Set.Ioo (ang (5/2)) Real.pi) : deriv trN2 u < 0 := by
  rw [deriv_trN2]
  have hc := cos_le_neg_21_29 ⟨le_of_lt hu.1, le_of_lt hu.2⟩
  have hs := sin_nonneg_of_ang ⟨le_of_lt hu.1, le_of_lt hu.2⟩
  nlinarith [hc, hs]

theorem trN2_strictAntiOn : StrictAntiOn trN2 (Set.Icc (ang (5/2)) Real.pi) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) continuous_trN2.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  exact trN2_deriv_neg hx

/-- The elementary bound `|-(3 A A') / sqrt (c² - 3 A²)| ≤ 3·(2/5)·(47/100)/(68/100)`. -/
theorem three_mul_abs_le (u : ℝ) :
    |(-(3 * trA u * trAd u)) / trS u| ≤ 3 * (2/5) * (47/100) / (68/100) := by
  have hSp := trS_pos u
  have hA := trA_abs_le u
  have hAd := trAd_abs_le u
  have hS := trS_ge u
  have habs : |(-(3 * trA u * trAd u))| = 3 * |trA u| * |trAd u| := by
    rw [abs_neg, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
  rw [abs_div, abs_of_pos hSp, habs]
  have h1 : 3 * |trA u| * |trAd u| / trS u ≤ 3 * (2/5) * (47/100) / trS u := by
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hSp)
    nlinarith [hA, hAd, abs_nonneg (trA u), abs_nonneg (trAd u)]
  have h2 : 3 * (2/5) * (47/100) / trS u ≤ 3 * (2/5) * (47/100) / (68/100) := by
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hS
  exact le_trans h1 h2

theorem YF_upper (u : ℝ) :
    -(3 * trA u * trAd u) / trS u ≤ 3 * (2/5) * (47/100) / (68/100) :=
  le_trans (le_abs_self _) (three_mul_abs_le u)

theorem YF_lower (u : ℝ) :
    -(3 * (2/5) * (47/100) / (68/100)) ≤ -(3 * trA u * trAd u) / trS u :=
  le_trans (neg_le_neg (three_mul_abs_le u)) (neg_abs_le _)

theorem psiF1_deriv_neg {u : ℝ} (hu : u ∈ Set.Ioo (ang (5/2)) Real.pi) : deriv psiF1 u < 0 := by
  rw [deriv_psiF1]
  have hc := cos_le_neg_21_29 ⟨le_of_lt hu.1, le_of_lt hu.2⟩
  have hs := sin_nonneg_of_ang ⟨le_of_lt hu.1, le_of_lt hu.2⟩
  have hb := YF_upper u
  nlinarith [hc, hs, hb]

theorem psiF1_strictAntiOn : StrictAntiOn psiF1 (Set.Icc (ang (5/2)) Real.pi) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) continuous_psiF1.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  exact psiF1_deriv_neg hx

theorem psiF2_deriv_pos {u : ℝ} (hu : u ∈ Set.Ioo (ang (9/2)) Real.pi) : 0 < deriv psiF2 u := by
  rw [deriv_psiF2]
  have hc : Real.cos u ≤ -(21/29) :=
    cos_le_neg_21_29 ⟨le_trans (ang_le_ang (by norm_num)) (le_of_lt hu.1), le_of_lt hu.2⟩
  have hs := sin_nonneg_of_ang ⟨le_trans (ang_le_ang (by norm_num)) (le_of_lt hu.1), le_of_lt hu.2⟩
  have hb := YF_lower u
  nlinarith [hc, hs, hb]

theorem psiF2_strictMonoOn : StrictMonoOn psiF2 (Set.Icc (ang (9/2)) Real.pi) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) continuous_psiF2.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  exact psiF2_deriv_pos hx

theorem ang_half_lt_pi_div_two : ang (1/2) < Real.pi / 2 :=
  ang_lt_pi_div_two (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)

theorem sin_le_four_fifths {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) (ang (1/2))) :
    Real.sin u ≤ 4/5 := by
  have hhalf_lt : ang (1/2) < Real.pi / 2 := ang_half_lt_pi_div_two
  have hmem1 : u ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith [hu.1, Real.pi_pos], by linarith [hu.2, hhalf_lt]⟩
  have hmem2 : ang (1/2) ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith [ang_pos (by norm_num : (0:ℝ) < 1/2), Real.pi_pos], by linarith [hhalf_lt]⟩
  have h : Real.sin u ≤ Real.sin (ang (1/2)) :=
    (Real.strictMonoOn_sin.le_iff_le hmem1 hmem2).mpr hu.2
  rw [sin_ang] at h
  norm_num at h
  linarith

theorem three_fifths_le_cos {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) (ang (1/2))) :
    3/5 ≤ Real.cos u := by
  have h1 : ang (1/2) ∈ Set.Icc (0:ℝ) Real.pi :=
    ⟨le_of_lt (ang_pos (by norm_num)), le_of_lt (ang_lt_pi (by norm_num))⟩
  have h3 : u ∈ Set.Icc (0:ℝ) Real.pi := ⟨hu.1, le_trans hu.2 h1.2⟩
  have h : Real.cos (ang (1/2)) ≤ Real.cos u :=
    Real.strictAntiOn_cos.antitoneOn h3 h1 hu.2
  rw [cos_ang] at h
  norm_num at h
  linarith

theorem trN2_deriv_pos_of_le_half {u : ℝ} (hu : u ∈ Set.Ioo (0:ℝ) (ang (1/2))) :
    0 < deriv trN2 u := by
  rw [deriv_trN2]
  have hs := sin_le_four_fifths ⟨le_of_lt hu.1, le_of_lt hu.2⟩
  have hc := three_fifths_le_cos ⟨le_of_lt hu.1, le_of_lt hu.2⟩
  nlinarith [hs, hc]

theorem psiF1_deriv_pos_of_le_half {u : ℝ} (hu : u ∈ Set.Ioo (0:ℝ) (ang (1/2))) :
    0 < deriv psiF1 u := by
  rw [deriv_psiF1]
  have hs := sin_le_four_fifths ⟨le_of_lt hu.1, le_of_lt hu.2⟩
  have hc := three_fifths_le_cos ⟨le_of_lt hu.1, le_of_lt hu.2⟩
  have hb := YF_lower u
  nlinarith [hs, hc, hb]

theorem psiF1_strictMonoOn_half : StrictMonoOn psiF1 (Set.Icc 0 (ang (1/2))) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) continuous_psiF1.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  exact psiF1_deriv_pos_of_le_half hx

/-! ## The values at the Pythagorean angles -/

theorem trN2_eq (u : ℝ) :
    trN2 u = (209/400) * Real.cos u + (14329/10000) * Real.sin u := by
  rw [trN2, trB2, trA]; ring

theorem trN2_ang (t : ℝ) :
    trN2 (ang t) = (5225 - 5225 * t^2 + 28658 * t) / (10000 * (1 + t^2)) := by
  rw [trN2_eq, cos_ang, sin_ang]
  field_simp
  ring

theorem trA_ang (t : ℝ) :
    trA (ang t) = (8 * t^2 - 78 * t - 8) / (100 * (1 + t^2)) := by
  rw [trA, cos_ang, sin_ang]
  field_simp
  ring

theorem trS_ang_ge (t S₀ : ℝ) (h : S₀^2 ≤ (97/100)^2 - 3 * (trA (ang t))^2) (h0 : 0 ≤ S₀) :
    S₀ ≤ trS (ang t) := by
  have hsq := trS_sq (ang t)
  have hnn := trS_nonneg (ang t)
  nlinarith [hsq, h, hnn, h0]

theorem trS_ang_le (t S₀ : ℝ) (h : (97/100)^2 - 3 * (trA (ang t))^2 ≤ S₀^2) (h0 : 0 ≤ S₀) :
    trS (ang t) ≤ S₀ := by
  have hsq := trS_sq (ang t)
  have hnn := trS_nonneg (ang t)
  nlinarith [hsq, h, hnn, h0]

theorem trS_zero_ge : (96/100 : ℝ) ≤ trS 0 := by
  have hsq := trS_sq 0
  have h0 : trA 0 = -(2/25) := by rw [trA]; norm_num
  rw [h0] at hsq
  nlinarith [hsq, trS_nonneg 0]

theorem psiE_zero_pos : 0 < psiE 0 := by
  have hN : trN2 0 = 209/400 := by rw [trN2_eq]; norm_num
  have hS := trS_zero_ge
  rw [psiE, hN, abs_of_pos (by norm_num : (0:ℝ) < 209/400)]
  nlinarith [hS]

theorem psiE_pi_pos : 0 < psiE Real.pi := by
  have hN : trN2 Real.pi = -(209/400) := by rw [trN2_eq]; norm_num
  have hS : (96/100 : ℝ) ≤ trS Real.pi := by
    rw [show Real.pi = 0 + Real.pi from (zero_add Real.pi).symm, trS_add_pi 0]
    exact trS_zero_ge
  rw [psiE, hN, abs_of_neg (by norm_num : (-(209/400) : ℝ) < 0)]
  nlinarith [hS]

theorem psiE_ang52_pos : 0 < psiE (ang (5/2)) := by
  have hN : trN2 (ang (5/2)) = 35371/58000 := by rw [trN2_ang]; norm_num
  have hS : (898/1000 : ℝ) ≤ trS (ang (5/2)) := by
    refine trS_ang_ge (5/2) (898/1000) ?_ (by norm_num)
    rw [trA_ang]; norm_num
  rw [psiE, hN, abs_of_pos (by norm_num : (0:ℝ) < 35371/58000)]
  nlinarith [hS]

theorem psiE_ang92_neg : psiE (ang (9/2)) < 0 := by
  have hN : trN2 (ang (9/2)) = 113519/850000 := by rw [trN2_ang]; norm_num
  have hS : trS (ang (9/2)) ≤ (96/100 : ℝ) := by
    refine trS_ang_le (9/2) (96/100) ?_ (by norm_num)
    rw [trA_ang]; norm_num
  rw [psiE, hN, abs_of_pos (by norm_num : (0:ℝ) < 113519/850000)]
  nlinarith [hS]

theorem psiE_ang14_neg : psiE (ang 14) < 0 := by
  have hN : trN2 (ang 14) = -(617663/1970000) := by rw [trN2_ang]; norm_num
  have hS : trS (ang 14) ≤ (97/100 : ℝ) := by
    refine trS_ang_le 14 (97/100) ?_ (by norm_num)
    rw [trA_ang]; norm_num
  rw [psiE, hN, abs_of_neg (by norm_num : (-(617663/1970000) : ℝ) < 0)]
  nlinarith [hS]

theorem psiE_ang15_neg : psiE (ang 15) < 0 := by
  have hN : trN2 (ang 15) = -(74053/226000) := by rw [trN2_ang]; norm_num
  have hS : trS (ang 15) ≤ (97/100 : ℝ) := by
    refine trS_ang_le 15 (97/100) ?_ (by norm_num)
    rw [trA_ang]; norm_num
  rw [psiE, hN, abs_of_neg (by norm_num : (-(74053/226000) : ℝ) < 0)]
  nlinarith [hS]

theorem psiE_ang400_pos : 0 < psiE (ang 400) := by
  have hN : trN2 (ang 400) = -(32981263/64000400) := by rw [trN2_ang]; norm_num
  have hS : (96/100 : ℝ) ≤ trS (ang 400) := by
    refine trS_ang_ge 400 (96/100) ?_ (by norm_num)
    rw [trA_ang]; norm_num
  rw [psiE, hN, abs_of_neg (by norm_num : (-(32981263/64000400) : ℝ) < 0)]
  nlinarith [hS]

/-! ## The sign of `trN2` and the sign pattern of `psiE` on the pieces -/

theorem psiF1_eq_psiE_of_nonneg {u : ℝ} (h : 0 ≤ trN2 u) : psiF1 u = psiE u := by
  rw [psiF1, psiE, abs_of_nonneg h]

theorem psiF2_eq_psiE_of_nonpos {u : ℝ} (h : trN2 u ≤ 0) : psiF2 u = psiE u := by
  rw [psiF2, psiE, abs_of_nonpos h]

theorem cos_nonneg_of_le_pi_div_two {u : ℝ} (h0 : 0 ≤ u) (h : u ≤ Real.pi / 2) :
    0 ≤ Real.cos u := by
  have h1 : Real.pi / 2 ∈ Set.Icc (0:ℝ) Real.pi :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have h3 : u ∈ Set.Icc (0:ℝ) Real.pi := ⟨h0, by linarith [h, Real.pi_pos]⟩
  have hm := Real.strictAntiOn_cos.antitoneOn h3 h1 h
  rwa [Real.cos_pi_div_two] at hm

theorem cos_ge_neg_21_29 {u : ℝ} (hu : u ∈ Set.Icc (ang (1/2)) (ang (5/2))) :
    -(21/29 : ℝ) ≤ Real.cos u := by
  have h1 : ang (5/2) ∈ Set.Icc (0:ℝ) Real.pi :=
    ⟨le_of_lt (ang_pos (by norm_num : (0:ℝ) < 5/2)),
     le_of_lt (ang_lt_pi (by norm_num : (0:ℝ) < 5/2))⟩
  have h3 : u ∈ Set.Icc (0:ℝ) Real.pi :=
    ⟨le_trans (ang_pos (by norm_num : (0:ℝ) < 1/2)).le hu.1, le_trans hu.2 h1.2⟩
  have hm : Real.cos (ang (5/2)) ≤ Real.cos u := Real.strictAntiOn_cos.antitoneOn h3 h1 hu.2
  rw [cos_ang] at hm
  norm_num at hm
  linarith

theorem sin_ge_20_29 {u : ℝ} (hu : u ∈ Set.Icc (ang (1/2)) (ang (5/2))) :
    (20/29 : ℝ) ≤ Real.sin u := by
  have hhalfpos : 0 < ang (1/2) := ang_pos (by norm_num : (0:ℝ) < 1/2)
  rcases le_or_gt u (Real.pi / 2) with h | h
  · have h1 : ang (1/2) ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) :=
      ⟨by linarith [hhalfpos, Real.pi_pos], by linarith [ang_half_lt_pi_div_two]⟩
    have h2 : u ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) :=
      ⟨by linarith [hhalfpos, hu.1, Real.pi_pos], by linarith [h, Real.pi_pos]⟩
    have hm : Real.sin (ang (1/2)) ≤ Real.sin u :=
      (Real.strictMonoOn_sin.le_iff_le h1 h2).mpr hu.1
    rw [sin_ang] at hm
    norm_num at hm
    linarith
  · have h1 : ang (5/2) ∈ Set.Icc (Real.pi/2) Real.pi :=
      ⟨(ang_pi_div_two_lt (by norm_num : (1:ℝ) < 5/2)).le,
       le_of_lt (ang_lt_pi (by norm_num : (0:ℝ) < 5/2))⟩
    have h2 : u ∈ Set.Icc (Real.pi/2) Real.pi :=
      ⟨h.le, le_trans hu.2 (le_of_lt (ang_lt_pi (by norm_num : (0:ℝ) < 5/2)))⟩
    have hm : Real.sin (ang (5/2)) ≤ Real.sin u :=
      (strictAntiOn_sin_Icc.le_iff_ge h1 h2).mpr hu.2
    rw [sin_ang] at hm
    norm_num at hm
    linarith

theorem trN2_pos_of_le_ang52 {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) (ang (5/2))) :
    0 < trN2 u := by
  rw [trN2_eq]
  rcases le_or_gt u (Real.pi / 2) with h | h
  · have hc : 0 ≤ Real.cos u := cos_nonneg_of_le_pi_div_two hu.1 h
    have hs : 0 ≤ Real.sin u :=
      Real.sin_nonneg_of_mem_Icc ⟨hu.1, by linarith [h, Real.pi_pos]⟩
    have hsq : 1 ≤ (Real.cos u + Real.sin u)^2 := by
      nlinarith [Real.cos_sq_add_sin_sq u, hc, hs, mul_nonneg hc hs]
    have hnn : 0 ≤ Real.cos u + Real.sin u := by linarith
    nlinarith [hsq, hnn, hc, hs]
  · have h2 : u ∈ Set.Icc (ang (1/2)) (ang (5/2)) :=
      ⟨by linarith [h, ang_half_lt_pi_div_two], hu.2⟩
    have hs := sin_ge_20_29 h2
    have hc := cos_ge_neg_21_29 h2
    nlinarith [hs, hc]

theorem trN2_ge_of_between {u : ℝ} (hu : u ∈ Set.Icc (ang (1/2)) (ang (5/2))) :
    (35371/58000 : ℝ) ≤ trN2 u := by
  have hs := sin_ge_20_29 hu
  have hc := cos_ge_neg_21_29 hu
  rw [trN2_eq]
  nlinarith [hs, hc]

theorem psiE_pos_of_between {u : ℝ} (hu : u ∈ Set.Icc (ang (1/2)) (ang (5/2))) :
    0 < psiE u := by
  have hN := trN2_ge_of_between hu
  have hS := trS_ge u
  have hNpos : 0 < trN2 u := by linarith
  rw [psiE, abs_of_pos hNpos]
  nlinarith [hN, hS]

theorem psiE_pos_of_le_ang52 {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) (ang (5/2))) :
    0 < psiE u := by
  rcases lt_or_eq_of_le hu.1 with hu0 | hu0
  · rcases le_or_gt u (ang (1/2)) with h | h
    · have hNpos := trN2_pos_of_le_ang52 hu
      have hN0 : 0 ≤ trN2 0 := by rw [trN2_eq]; norm_num
      have hmem0 : (0:ℝ) ∈ Set.Icc (0:ℝ) (ang (1/2)) :=
        ⟨le_rfl, (ang_pos (by norm_num : (0:ℝ) < 1/2)).le⟩
      have hmemu : u ∈ Set.Icc (0:ℝ) (ang (1/2)) := ⟨hu.1, h⟩
      have hm : psiF1 0 < psiF1 u := psiF1_strictMonoOn_half hmem0 hmemu hu0
      rw [psiF1_eq_psiE_of_nonneg hN0, psiF1_eq_psiE_of_nonneg hNpos.le] at hm
      linarith [hm, psiE_zero_pos]
    · exact psiE_pos_of_between ⟨h.le, hu.2⟩
  · rw [← hu0]; exact psiE_zero_pos

theorem trN2_pos_of_le_ang92 {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) (ang (9/2))) :
    0 < trN2 u := by
  rcases le_or_gt u (ang (5/2)) with h | h
  · exact trN2_pos_of_le_ang52 ⟨hu.1, h⟩
  · have h1 : ang (9/2) ∈ Set.Icc (ang (5/2)) Real.pi :=
      ⟨ang_le_ang (by norm_num), le_of_lt (ang_lt_pi (by norm_num : (0:ℝ) < 9/2))⟩
    have h2 : u ∈ Set.Icc (ang (5/2)) Real.pi :=
      ⟨h.le, le_trans hu.2 (le_of_lt (ang_lt_pi (by norm_num : (0:ℝ) < 9/2)))⟩
    have hm : trN2 (ang (9/2)) ≤ trN2 u := trN2_strictAntiOn.antitoneOn h2 h1 hu.2
    have hval : trN2 (ang (9/2)) = 113519/850000 := by rw [trN2_ang]; norm_num
    linarith [hm, hval]

theorem trN2_neg_of_ang14_le {u : ℝ} (hu : u ∈ Set.Icc (ang 14) Real.pi) : trN2 u < 0 := by
  have h1 : ang 14 ∈ Set.Icc (ang (5/2)) Real.pi :=
    ⟨ang_le_ang (by norm_num), le_of_lt (ang_lt_pi (by norm_num : (0:ℝ) < 14))⟩
  have h2 : u ∈ Set.Icc (ang (5/2)) Real.pi := ⟨le_trans h1.1 hu.1, hu.2⟩
  have hm : trN2 u ≤ trN2 (ang 14) := trN2_strictAntiOn.antitoneOn h1 h2 hu.1
  have hval : trN2 (ang 14) = -(617663/1970000) := by rw [trN2_ang]; norm_num
  linarith [hm, hval]

theorem psiE_neg_of_mid {u : ℝ} (hu : u ∈ Set.Icc (ang (9/2)) (ang 14)) : psiE u < 0 := by
  have hpi : ang 14 ≤ Real.pi := (ang_lt_pi (by norm_num : (0:ℝ) < 14)).le
  have h1 : psiF1 u ≤ psiF1 (ang (9/2)) := by
    have ha : ang (9/2) ∈ Set.Icc (ang (5/2)) Real.pi :=
      ⟨ang_le_ang (by norm_num), le_of_lt (ang_lt_pi (by norm_num : (0:ℝ) < 9/2))⟩
    have hb : u ∈ Set.Icc (ang (5/2)) Real.pi :=
      ⟨le_trans ha.1 hu.1, le_trans hu.2 hpi⟩
    exact psiF1_strictAntiOn.antitoneOn ha hb hu.1
  have h2 : psiF2 u ≤ psiF2 (ang 14) := by
    have ha : ang 14 ∈ Set.Icc (ang (9/2)) Real.pi :=
      ⟨ang_le_ang (by norm_num), le_of_lt (ang_lt_pi (by norm_num : (0:ℝ) < 14))⟩
    have hb : u ∈ Set.Icc (ang (9/2)) Real.pi := ⟨hu.1, le_trans hu.2 hpi⟩
    exact psiF2_strictMonoOn.monotoneOn hb ha hu.2
  have hv1 : psiF1 (ang (9/2)) = psiE (ang (9/2)) :=
    psiF1_eq_psiE_of_nonneg (trN2_pos_of_le_ang92
      ⟨(ang_pos (by norm_num : (0:ℝ) < 9/2)).le, le_rfl⟩).le
  have hv2 : psiF2 (ang 14) = psiE (ang 14) :=
    psiF2_eq_psiE_of_nonpos (trN2_neg_of_ang14_le
      ⟨le_rfl, (ang_lt_pi (by norm_num : (0:ℝ) < 14)).le⟩).le
  rw [psiE_eq_max]
  rw [hv1] at h1
  rw [hv2] at h2
  exact max_lt (lt_of_le_of_lt h1 psiE_ang92_neg) (lt_of_le_of_lt h2 psiE_ang14_neg)

theorem psiE_pos_of_ang400_pi {u : ℝ} (hu : u ∈ Set.Icc (ang 400) Real.pi) : 0 < psiE u := by
  have hN : trN2 u < 0 := trN2_neg_of_ang14_le
    ⟨le_trans (ang_le_ang (by norm_num)) hu.1, hu.2⟩
  have hm : psiF2 (ang 400) ≤ psiF2 u := by
    have ha : ang 400 ∈ Set.Icc (ang (9/2)) Real.pi :=
      ⟨ang_le_ang (by norm_num), le_of_lt (ang_lt_pi (by norm_num : (0:ℝ) < 400))⟩
    have hb : u ∈ Set.Icc (ang (9/2)) Real.pi := ⟨le_trans ha.1 hu.1, hu.2⟩
    exact psiF2_strictMonoOn.monotoneOn ha hb hu.1
  have hv : psiF2 (ang 400) = psiE (ang 400) :=
    psiF2_eq_psiE_of_nonpos (trN2_neg_of_ang14_le
      ⟨ang_le_ang (by norm_num), (ang_lt_pi (by norm_num : (0:ℝ) < 400)).le⟩).le
  rw [psiE, abs_of_nonpos hN.le]
  rw [show -(trN2 u) - (7/15) * (2 * (97/100) - trS u) = psiF2 u from rfl]
  linarith [hm, hv, psiE_ang400_pos]

/-! ## The two zeroes on `[0, π]` -/

theorem ang_inv_add (t : ℝ) (h : 0 < t) : ang t + ang t⁻¹ = Real.pi := by
  rw [ang, ang, Real.arctan_inv_of_pos h]
  ring

theorem two_pi_sub_ang (t : ℝ) (h : 0 < t) : 2 * Real.pi - ang t = Real.pi + ang t⁻¹ := by
  have := ang_inv_add t h
  linarith

theorem exists_psiE_zero_low :
    ∃ w : ℝ, w ∈ Set.Ioo (ang (5/2)) (ang (9/2)) ∧ psiE w = 0 := by
  have hcont : ContinuousOn (fun u : ℝ => -psiE u) (Set.Icc (ang (5/2)) (ang (9/2))) :=
    continuous_psiE.neg.continuousOn
  have hle : ang (5/2) ≤ ang (9/2) := ang_le_ang (by norm_num)
  have h0 : (0:ℝ) ∈ Set.Ioo ((fun u : ℝ => -psiE u) (ang (5/2)))
      ((fun u : ℝ => -psiE u) (ang (9/2))) :=
    ⟨by simpa using neg_lt_neg psiE_ang52_pos, by simpa using neg_lt_neg psiE_ang92_neg⟩
  obtain ⟨w, hw, hw0⟩ := (intermediate_value_Ioo hle hcont) h0
  exact ⟨w, hw, by simpa using hw0⟩

theorem exists_psiE_zero_high :
    ∃ w : ℝ, w ∈ Set.Ioo (ang 14) (ang 400) ∧ psiE w = 0 := by
  have hcont : ContinuousOn psiE (Set.Icc (ang 14) (ang 400)) := continuous_psiE.continuousOn
  have hle : ang 14 ≤ ang 400 := ang_le_ang (by norm_num)
  have h0 : (0:ℝ) ∈ Set.Ioo (psiE (ang 14)) (psiE (ang 400)) := ⟨psiE_ang14_neg, psiE_ang400_pos⟩
  exact (intermediate_value_Ioo hle hcont) h0

noncomputable def w1 : ℝ := Classical.choose exists_psiE_zero_low

noncomputable def w2 : ℝ := Classical.choose exists_psiE_zero_high

theorem w1_mem : w1 ∈ Set.Ioo (ang (5/2)) (ang (9/2)) :=
  (Classical.choose_spec exists_psiE_zero_low).1

theorem w1_zero : psiE w1 = 0 := (Classical.choose_spec exists_psiE_zero_low).2

theorem w2_mem : w2 ∈ Set.Ioo (ang 14) (ang 400) :=
  (Classical.choose_spec exists_psiE_zero_high).1

theorem w2_zero : psiE w2 = 0 := (Classical.choose_spec exists_psiE_zero_high).2

theorem w1_unique {u : ℝ} (hu : u ∈ Set.Icc (ang (5/2)) (ang (9/2))) (h0 : psiE u = 0) :
    u = w1 := by
  have hNu : 0 ≤ trN2 u := (trN2_pos_of_le_ang92
    ⟨le_trans (ang_pos (by norm_num : (0:ℝ) < 5/2)).le hu.1, hu.2⟩).le
  have hNw : 0 ≤ trN2 w1 := (trN2_pos_of_le_ang92 (u := w1)
    ⟨le_trans (ang_pos (by norm_num : (0:ℝ) < 5/2)).le w1_mem.1.le, w1_mem.2.le⟩).le
  have ha : u ∈ Set.Icc (ang (5/2)) Real.pi :=
    ⟨hu.1, le_trans hu.2 (ang_lt_pi (by norm_num : (0:ℝ) < 9/2)).le⟩
  have hb : w1 ∈ Set.Icc (ang (5/2)) Real.pi :=
    ⟨w1_mem.1.le, le_trans w1_mem.2.le (ang_lt_pi (by norm_num : (0:ℝ) < 9/2)).le⟩
  have h1 : psiF1 u = psiF1 w1 := by
    rw [psiF1_eq_psiE_of_nonneg hNu, psiF1_eq_psiE_of_nonneg hNw, h0, w1_zero]
  exact psiF1_strictAntiOn.injOn ha hb h1

theorem w2_unique {u : ℝ} (hu : u ∈ Set.Icc (ang 14) (ang 400)) (h0 : psiE u = 0) :
    u = w2 := by
  have hNu : trN2 u ≤ 0 := (trN2_neg_of_ang14_le
    ⟨hu.1, le_trans hu.2 (ang_lt_pi (by norm_num : (0:ℝ) < 400)).le⟩).le
  have hNw : trN2 w2 ≤ 0 := (trN2_neg_of_ang14_le
    ⟨w2_mem.1.le, le_trans w2_mem.2.le (ang_lt_pi (by norm_num : (0:ℝ) < 400)).le⟩).le
  have ha : u ∈ Set.Icc (ang (9/2)) Real.pi :=
    ⟨le_trans (ang_le_ang (by norm_num)) hu.1,
     le_trans hu.2 (ang_lt_pi (by norm_num : (0:ℝ) < 400)).le⟩
  have hb : w2 ∈ Set.Icc (ang (9/2)) Real.pi :=
    ⟨le_trans (ang_le_ang (by norm_num)) w2_mem.1.le,
     le_trans w2_mem.2.le (ang_lt_pi (by norm_num : (0:ℝ) < 400)).le⟩
  have h1 : psiF2 u = psiF2 w2 := by
    rw [psiF2_eq_psiE_of_nonpos hNu, psiF2_eq_psiE_of_nonpos hNw, h0, w2_zero]
  exact psiF2_strictMonoOn.injOn ha hb h1

theorem psiE_le_zero_iff_w1_le {u : ℝ} (hu : u ∈ Set.Icc (ang (5/2)) (ang (9/2))) :
    (psiE u ≤ 0 ↔ w1 ≤ u) := by
  have hNu : 0 ≤ trN2 u := (trN2_pos_of_le_ang92
    ⟨le_trans (ang_pos (by norm_num : (0:ℝ) < 5/2)).le hu.1, hu.2⟩).le
  have hNw : 0 ≤ trN2 w1 := (trN2_pos_of_le_ang92 (u := w1)
    ⟨le_trans (ang_pos (by norm_num : (0:ℝ) < 5/2)).le w1_mem.1.le, w1_mem.2.le⟩).le
  have ha : u ∈ Set.Icc (ang (5/2)) Real.pi :=
    ⟨hu.1, le_trans hu.2 (ang_lt_pi (by norm_num : (0:ℝ) < 9/2)).le⟩
  have hb : w1 ∈ Set.Icc (ang (5/2)) Real.pi :=
    ⟨w1_mem.1.le, le_trans w1_mem.2.le (ang_lt_pi (by norm_num : (0:ℝ) < 9/2)).le⟩
  have hw1 : psiF1 w1 = 0 := by rw [psiF1_eq_psiE_of_nonneg hNw, w1_zero]
  constructor
  · intro h
    by_contra hcon
    rw [not_le] at hcon
    have hlt : psiF1 w1 < psiF1 u := psiF1_strictAntiOn ha hb hcon
    rw [hw1, psiF1_eq_psiE_of_nonneg hNu] at hlt
    linarith
  · intro h
    have hle : psiF1 u ≤ psiF1 w1 := psiF1_strictAntiOn.antitoneOn hb ha h
    rw [hw1, psiF1_eq_psiE_of_nonneg hNu] at hle
    linarith

theorem psiE_lt_zero_iff_w1_lt {u : ℝ} (hu : u ∈ Set.Icc (ang (5/2)) (ang (9/2))) :
    (psiE u < 0 ↔ w1 < u) := by
  have hNu : 0 ≤ trN2 u := (trN2_pos_of_le_ang92
    ⟨le_trans (ang_pos (by norm_num : (0:ℝ) < 5/2)).le hu.1, hu.2⟩).le
  have hNw : 0 ≤ trN2 w1 := (trN2_pos_of_le_ang92 (u := w1)
    ⟨le_trans (ang_pos (by norm_num : (0:ℝ) < 5/2)).le w1_mem.1.le, w1_mem.2.le⟩).le
  have ha : u ∈ Set.Icc (ang (5/2)) Real.pi :=
    ⟨hu.1, le_trans hu.2 (ang_lt_pi (by norm_num : (0:ℝ) < 9/2)).le⟩
  have hb : w1 ∈ Set.Icc (ang (5/2)) Real.pi :=
    ⟨w1_mem.1.le, le_trans w1_mem.2.le (ang_lt_pi (by norm_num : (0:ℝ) < 9/2)).le⟩
  have hw1 : psiF1 w1 = 0 := by rw [psiF1_eq_psiE_of_nonneg hNw, w1_zero]
  constructor
  · intro h
    by_contra hcon
    rw [not_lt] at hcon
    have hle : psiF1 w1 ≤ psiF1 u := psiF1_strictAntiOn.antitoneOn ha hb hcon
    rw [hw1, psiF1_eq_psiE_of_nonneg hNu] at hle
    linarith
  · intro h
    have hlt : psiF1 u < psiF1 w1 := psiF1_strictAntiOn hb ha h
    rw [hw1, psiF1_eq_psiE_of_nonneg hNu] at hlt
    linarith

theorem psiE_le_zero_iff_le_w2 {u : ℝ} (hu : u ∈ Set.Icc (ang 14) (ang 400)) :
    (psiE u ≤ 0 ↔ u ≤ w2) := by
  have hNu : trN2 u ≤ 0 := (trN2_neg_of_ang14_le
    ⟨hu.1, le_trans hu.2 (ang_lt_pi (by norm_num : (0:ℝ) < 400)).le⟩).le
  have hNw : trN2 w2 ≤ 0 := (trN2_neg_of_ang14_le
    ⟨w2_mem.1.le, le_trans w2_mem.2.le (ang_lt_pi (by norm_num : (0:ℝ) < 400)).le⟩).le
  have ha : u ∈ Set.Icc (ang (9/2)) Real.pi :=
    ⟨le_trans (ang_le_ang (by norm_num)) hu.1,
     le_trans hu.2 (ang_lt_pi (by norm_num : (0:ℝ) < 400)).le⟩
  have hb : w2 ∈ Set.Icc (ang (9/2)) Real.pi :=
    ⟨le_trans (ang_le_ang (by norm_num)) w2_mem.1.le,
     le_trans w2_mem.2.le (ang_lt_pi (by norm_num : (0:ℝ) < 400)).le⟩
  have hw2 : psiF2 w2 = 0 := by rw [psiF2_eq_psiE_of_nonpos hNw, w2_zero]
  constructor
  · intro h
    by_contra hcon
    rw [not_le] at hcon
    have hlt : psiF2 w2 < psiF2 u := psiF2_strictMonoOn hb ha hcon
    rw [hw2, psiF2_eq_psiE_of_nonpos hNu] at hlt
    linarith
  · intro h
    have hle : psiF2 u ≤ psiF2 w2 := psiF2_strictMonoOn.monotoneOn ha hb h
    rw [hw2, psiF2_eq_psiE_of_nonpos hNu] at hle
    linarith

theorem psiE_lt_zero_iff_lt_w2 {u : ℝ} (hu : u ∈ Set.Icc (ang 14) (ang 400)) :
    (psiE u < 0 ↔ u < w2) := by
  have hNu : trN2 u ≤ 0 := (trN2_neg_of_ang14_le
    ⟨hu.1, le_trans hu.2 (ang_lt_pi (by norm_num : (0:ℝ) < 400)).le⟩).le
  have hNw : trN2 w2 ≤ 0 := (trN2_neg_of_ang14_le
    ⟨w2_mem.1.le, le_trans w2_mem.2.le (ang_lt_pi (by norm_num : (0:ℝ) < 400)).le⟩).le
  have ha : u ∈ Set.Icc (ang (9/2)) Real.pi :=
    ⟨le_trans (ang_le_ang (by norm_num)) hu.1,
     le_trans hu.2 (ang_lt_pi (by norm_num : (0:ℝ) < 400)).le⟩
  have hb : w2 ∈ Set.Icc (ang (9/2)) Real.pi :=
    ⟨le_trans (ang_le_ang (by norm_num)) w2_mem.1.le,
     le_trans w2_mem.2.le (ang_lt_pi (by norm_num : (0:ℝ) < 400)).le⟩
  have hw2 : psiF2 w2 = 0 := by rw [psiF2_eq_psiE_of_nonpos hNw, w2_zero]
  constructor
  · intro h
    by_contra hcon
    rw [not_lt] at hcon
    have hle : psiF2 w2 ≤ psiF2 u := psiF2_strictMonoOn.monotoneOn hb ha hcon
    rw [hw2, psiF2_eq_psiE_of_nonpos hNu] at hle
    linarith
  · intro h
    have hlt : psiF2 u < psiF2 w2 := psiF2_strictMonoOn ha hb h
    rw [hw2, psiF2_eq_psiE_of_nonpos hNu] at hlt
    linarith

theorem ang15_lt_w2 : ang 15 < w2 := by
  have h := (psiE_le_zero_iff_le_w2
    ⟨ang_le_ang (by norm_num), ang_le_ang (by norm_num)⟩).mp psiE_ang15_neg.le
  refine lt_of_le_of_ne h ?_
  intro he
  have hneg := psiE_ang15_neg
  rw [he, w2_zero] at hneg
  exact lt_irrefl 0 hneg

/-! ## The shape on `[0, π]` and on `[0, 2π]` -/

theorem psiE_le_zero_iff_Icc_pi (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) Real.pi) :
    (psiE u ≤ 0 ↔ u ∈ Set.Icc w1 w2) := by
  have hlt12 : ang (5/2) < ang (9/2) := ang_lt_ang (by norm_num)
  have hlt24 : ang (9/2) < ang 14 := ang_lt_ang (by norm_num)
  rcases le_or_gt u (ang (5/2)) with hA | hA
  · have hp : 0 < psiE u := psiE_pos_of_le_ang52 ⟨hu.1, hA⟩
    have hlt : u < w1 := lt_of_le_of_lt hA w1_mem.1
    refine iff_of_false (not_le_of_gt hp) (fun hc => ?_)
    rw [Set.mem_Icc] at hc
    linarith [hc.1]
  rcases le_or_gt u (ang (9/2)) with hB | hB
  · rw [psiE_le_zero_iff_w1_le ⟨hA.le, hB⟩]
    exact ⟨fun h => ⟨h, by linarith [hB, w1_mem.2, w2_mem.1, hlt24]⟩, fun h => h.1⟩
  rcases le_or_gt u (ang 14) with hC | hC
  · have hp : psiE u < 0 := psiE_neg_of_mid ⟨hB.le, hC⟩
    exact iff_of_true hp.le ⟨by linarith [hB, w1_mem.2, hlt12], by linarith [hC, w2_mem.1, hlt24]⟩
  rcases le_or_gt u (ang 400) with hD | hD
  · rw [psiE_le_zero_iff_le_w2 ⟨hC.le, hD⟩]
    exact ⟨fun h => ⟨by linarith [hC, w1_mem.2, hlt24], h⟩, fun h => h.2⟩
  · have hp : 0 < psiE u := psiE_pos_of_ang400_pi ⟨hD.le, hu.2⟩
    have hlt : w2 < u := lt_of_lt_of_le w2_mem.2 hD.le
    refine iff_of_false (not_le_of_gt hp) (fun hc => ?_)
    rw [Set.mem_Icc] at hc
    linarith [hc.2]

theorem psiE_lt_zero_iff_Ioo_pi (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) Real.pi) :
    (psiE u < 0 ↔ u ∈ Set.Ioo w1 w2) := by
  have hlt12 : ang (5/2) < ang (9/2) := ang_lt_ang (by norm_num)
  have hlt24 : ang (9/2) < ang 14 := ang_lt_ang (by norm_num)
  rcases le_or_gt u (ang (5/2)) with hA | hA
  · have hp : 0 < psiE u := psiE_pos_of_le_ang52 ⟨hu.1, hA⟩
    have hlt : u < w1 := lt_of_le_of_lt hA w1_mem.1
    refine iff_of_false (not_lt_of_ge hp.le) (fun hc => ?_)
    rw [Set.mem_Ioo] at hc
    linarith [hc.1]
  rcases le_or_gt u (ang (9/2)) with hB | hB
  · rw [psiE_lt_zero_iff_w1_lt ⟨hA.le, hB⟩]
    exact ⟨fun h => ⟨h, by linarith [hB, w1_mem.2, w2_mem.1, hlt24]⟩, fun h => h.1⟩
  rcases le_or_gt u (ang 14) with hC | hC
  · have hp : psiE u < 0 := psiE_neg_of_mid ⟨hB.le, hC⟩
    exact iff_of_true hp ⟨by linarith [hB, w1_mem.2, hlt12], by linarith [hC, w2_mem.1, hlt24]⟩
  rcases le_or_gt u (ang 400) with hD | hD
  · rw [psiE_lt_zero_iff_lt_w2 ⟨hC.le, hD⟩]
    exact ⟨fun h => ⟨by linarith [hC, w1_mem.2, hlt24], h⟩, fun h => h.2⟩
  · have hp : 0 < psiE u := psiE_pos_of_ang400_pi ⟨hD.le, hu.2⟩
    have hlt : w2 < u := lt_of_lt_of_le w2_mem.2 hD.le
    refine iff_of_false (not_lt_of_ge hp.le) (fun hc => ?_)
    rw [Set.mem_Ioo] at hc
    linarith [hc.2]

theorem psiE_le_zero_iff_Icc_two_pi (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) (2*Real.pi)) :
    (psiE u ≤ 0 ↔ u ∈ Set.Icc w1 w2 ∪ Set.Icc (w1 + Real.pi) (w2 + Real.pi)) := by
  have hw2pi : w2 < Real.pi := lt_trans w2_mem.2 (ang_lt_pi (by norm_num : (0:ℝ) < 400))
  rcases le_or_gt u Real.pi with h | h
  · have h1 := psiE_le_zero_iff_Icc_pi u ⟨hu.1, h⟩
    have hnot : u ∉ Set.Icc (w1 + Real.pi) (w2 + Real.pi) := by
      rw [Set.mem_Icc]; intro hc
      linarith [hc.1, h, w1_mem.1, ang_pos (by norm_num : (0:ℝ) < 5/2), Real.pi_pos]
    rw [h1]
    exact ⟨fun h2 => Or.inl h2, fun h2 => h2.elim id (fun h3 => absurd h3 hnot)⟩
  · have h2 : u - Real.pi ∈ Set.Icc (0:ℝ) Real.pi := ⟨by linarith [h], by linarith [hu.2]⟩
    have hper : psiE u = psiE (u - Real.pi) := by
      have hs := psiE_add_pi (u - Real.pi)
      rw [sub_add_cancel] at hs
      exact hs
    have h3 := psiE_le_zero_iff_Icc_pi (u - Real.pi) h2
    have hnot : u ∉ Set.Icc w1 w2 := by
      rw [Set.mem_Icc]; intro hc; linarith [hc.2, hw2pi, h]
    rw [hper, h3]
    exact ⟨fun h4 => Or.inr ⟨by linarith [h4.1], by linarith [h4.2]⟩,
      fun h4 => h4.elim (fun h5 => absurd h5 hnot) (fun h5 => ⟨by linarith [h5.1], by linarith [h5.2]⟩)⟩

theorem psiE_lt_zero_iff_Ioo_two_pi (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) (2*Real.pi)) :
    (psiE u < 0 ↔ u ∈ Set.Ioo w1 w2 ∪ Set.Ioo (w1 + Real.pi) (w2 + Real.pi)) := by
  have hw2pi : w2 < Real.pi := lt_trans w2_mem.2 (ang_lt_pi (by norm_num : (0:ℝ) < 400))
  rcases le_or_gt u Real.pi with h | h
  · have h1 := psiE_lt_zero_iff_Ioo_pi u ⟨hu.1, h⟩
    have hnot : u ∉ Set.Ioo (w1 + Real.pi) (w2 + Real.pi) := by
      rw [Set.mem_Ioo]; intro hc
      linarith [hc.1, h, w1_mem.1, ang_pos (by norm_num : (0:ℝ) < 5/2), Real.pi_pos]
    rw [h1]
    exact ⟨fun h2 => Or.inl h2, fun h2 => h2.elim id (fun h3 => absurd h3 hnot)⟩
  · have h2 : u - Real.pi ∈ Set.Icc (0:ℝ) Real.pi := ⟨by linarith [h], by linarith [hu.2]⟩
    have hper : psiE u = psiE (u - Real.pi) := by
      have hs := psiE_add_pi (u - Real.pi)
      rw [sub_add_cancel] at hs
      exact hs
    have h3 := psiE_lt_zero_iff_Ioo_pi (u - Real.pi) h2
    have hnot : u ∉ Set.Ioo w1 w2 := by
      rw [Set.mem_Ioo]; intro hc; linarith [hc.2, hw2pi, h]
    rw [hper, h3]
    exact ⟨fun h4 => Or.inr ⟨by linarith [h4.1], by linarith [h4.2]⟩,
      fun h4 => h4.elim (fun h5 => absurd h5 hnot) (fun h5 => ⟨by linarith [h5.1], by linarith [h5.2]⟩)⟩

theorem psiE_eq_zero_iff (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) (2*Real.pi)) :
    (psiE u = 0 ↔ u = w1 ∨ u = w2 ∨ u = w1 + Real.pi ∨ u = w2 + Real.pi) := by
  constructor
  · intro h0
    have hle := (psiE_le_zero_iff_Icc_two_pi u hu).mp h0.le
    have hn1 : u ∉ Set.Ioo w1 w2 := fun hc => by
      have hlt : psiE u < 0 := (psiE_lt_zero_iff_Ioo_two_pi u hu).mpr (Or.inl hc)
      rw [h0] at hlt
      exact lt_irrefl 0 hlt
    have hn2 : u ∉ Set.Ioo (w1 + Real.pi) (w2 + Real.pi) := fun hc => by
      have hlt : psiE u < 0 := (psiE_lt_zero_iff_Ioo_two_pi u hu).mpr (Or.inr hc)
      rw [h0] at hlt
      exact lt_irrefl 0 hlt
    rw [Set.mem_union, Set.mem_Icc, Set.mem_Icc] at hle
    rw [Set.mem_Ioo] at hn1 hn2
    rcases hle with hc | hc
    · rcases eq_or_lt_of_le hc.1 with heq | hlt
      · exact Or.inl heq.symm
      · rcases eq_or_lt_of_le hc.2 with heq2 | hlt2
        · exact Or.inr (Or.inl heq2)
        · exact absurd ⟨hlt, hlt2⟩ hn1
    · rcases eq_or_lt_of_le hc.1 with heq | hlt
      · exact Or.inr (Or.inr (Or.inl heq.symm))
      · rcases eq_or_lt_of_le hc.2 with heq2 | hlt2
        · exact Or.inr (Or.inr (Or.inr heq2))
        · exact absurd ⟨hlt, hlt2⟩ hn2
  · intro h
    rcases h with h | h | h | h
    · rw [h, w1_zero]
    · rw [h, w2_zero]
    · rw [h, psiE_add_pi, w1_zero]
    · rw [h, psiE_add_pi, w2_zero]

/-! ## The parameters of `dropTrace` -/

theorem zA1_eq : zA1 = w1 := by
  have hset : {u : ℝ | u ∈ Set.Icc (ang (5/2)) (ang (9/2)) ∧ psiA2 u = 0} = {w1} := by
    ext u
    constructor
    · intro hu
      obtain ⟨huI, hu0⟩ := hu
      have hp : psiE u = 0 := by
        have h := psiA2_eq_three_psiE u
        rw [hu0] at h
        linarith
      exact Set.mem_singleton_iff.mpr (w1_unique huI hp)
    · intro hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      exact ⟨⟨w1_mem.1.le, w1_mem.2.le⟩,
        by rw [psiA2_eq_three_psiE, w1_zero]; ring⟩
  have hz : zA1 = sInf {u : ℝ | u ∈ Set.Icc (ang (5/2)) (ang (9/2)) ∧ psiA2 u = 0} := rfl
  rw [hz, hset, csInf_singleton]

theorem zA2_eq : zA2 = w2 := by
  have hset : {u : ℝ | u ∈ Set.Icc (ang 14) (ang 400) ∧ psiA2 u = 0} = {w2} := by
    ext u
    constructor
    · intro hu
      obtain ⟨huI, hu0⟩ := hu
      have hp : psiE u = 0 := by
        have h := psiA2_eq_three_psiE u
        rw [hu0] at h
        linarith
      exact Set.mem_singleton_iff.mpr (w2_unique huI hp)
    · intro hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      exact ⟨⟨w2_mem.1.le, w2_mem.2.le⟩,
        by rw [psiA2_eq_three_psiE, w2_zero]; ring⟩
  have hz : zA2 = sInf {u : ℝ | u ∈ Set.Icc (ang 14) (ang 400) ∧ psiA2 u = 0} := rfl
  rw [hz, hset, csInf_singleton]

theorem zA3_eq : zA3 = w1 + Real.pi := by
  have h50 : 2 * Real.pi - ang (2/5) = Real.pi + ang (5/2) := by
    rw [two_pi_sub_ang (2/5) (by norm_num : (0:ℝ) < 2/5)]
    norm_num
  have h15 : 2 * Real.pi - ang (1/5) = Real.pi + ang 5 := by
    rw [two_pi_sub_ang (1/5) (by norm_num : (0:ℝ) < 1/5)]
    norm_num
  have hset : {u : ℝ | u ∈ Set.Icc (2 * Real.pi - ang (2/5)) (2 * Real.pi - ang (1/5))
      ∧ psiA2 u = 0} = {w1 + Real.pi} := by
    ext u
    constructor
    · intro hu
      obtain ⟨huI, hu0⟩ := hu
      rw [h50, h15] at huI
      have hp : psiE u = 0 := by
        have h := psiA2_eq_three_psiE u
        rw [hu0] at h
        linarith
      have hu2pi : u ∈ Set.Icc (0:ℝ) (2 * Real.pi) :=
        ⟨by linarith [huI.1, (ang_pos (by norm_num : (0:ℝ) < 5/2)).le, Real.pi_pos],
         by linarith [huI.2, (ang_lt_pi (by norm_num : (0:ℝ) < 5)).le, Real.pi_pos]⟩
      rcases (psiE_eq_zero_iff u hu2pi).mp hp with h | h | h | h
      · exfalso
        linarith [h, huI.1, w1_mem.2, (ang_lt_pi (by norm_num : (0:ℝ) < 9/2)).le,
          (ang_pos (by norm_num : (0:ℝ) < 5/2)).le]
      · exfalso
        linarith [h, huI.1, w2_mem.2, (ang_lt_pi (by norm_num : (0:ℝ) < 400)).le,
          (ang_pos (by norm_num : (0:ℝ) < 5/2)).le, Real.pi_pos]
      · exact h
      · exfalso
        linarith [h, huI.2, w2_mem.1, ang_lt_ang (show (5:ℝ) < 14 by norm_num)]
    · intro hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      refine ⟨?_, ?_⟩
      · rw [h50, h15]
        constructor <;>
          linarith [w1_mem.1, w1_mem.2, ang_lt_ang (show (9:ℝ)/2 < 5 by norm_num)]
      · rw [psiA2_add_pi, psiA2_eq_three_psiE, w1_zero]; ring
  have hz : zA3 = sInf {u : ℝ | u ∈ Set.Icc (2 * Real.pi - ang (2/5)) (2 * Real.pi - ang (1/5))
      ∧ psiA2 u = 0} := rfl
  rw [hz, hset, csInf_singleton]

theorem zA4_eq : zA4 = w2 + Real.pi := by
  have h15 : 2 * Real.pi - ang (1/15) = Real.pi + ang 15 := by
    rw [two_pi_sub_ang (1/15) (by norm_num : (0:ℝ) < 1/15)]
    norm_num
  have h1000 : 2 * Real.pi - ang (1/1000) = Real.pi + ang 1000 := by
    rw [two_pi_sub_ang (1/1000) (by norm_num : (0:ℝ) < 1/1000)]
    norm_num
  have hset : {u : ℝ | u ∈ Set.Icc (2 * Real.pi - ang (1/15)) (2 * Real.pi - ang (1/1000))
      ∧ psiA2 u = 0} = {w2 + Real.pi} := by
    ext u
    constructor
    · intro hu
      obtain ⟨huI, hu0⟩ := hu
      rw [h15, h1000] at huI
      have hp : psiE u = 0 := by
        have h := psiA2_eq_three_psiE u
        rw [hu0] at h
        linarith
      have hu2pi : u ∈ Set.Icc (0:ℝ) (2 * Real.pi) :=
        ⟨by linarith [huI.1, (ang_pos (by norm_num : (0:ℝ) < 15)).le, Real.pi_pos],
         by linarith [huI.2, (ang_lt_pi (by norm_num : (0:ℝ) < 1000)).le, Real.pi_pos]⟩
      rcases (psiE_eq_zero_iff u hu2pi).mp hp with h | h | h | h
      · exfalso
        linarith [h, huI.1, w1_mem.2,
          (ang_lt_pi (by norm_num : (0:ℝ) < 9/2)).le,
          (ang_pos (by norm_num : (0:ℝ) < 15)).le]
      · exfalso
        linarith [h, huI.1, w2_mem.2, (ang_lt_pi (by norm_num : (0:ℝ) < 400)).le,
          (ang_pos (by norm_num : (0:ℝ) < 15)).le]
      · exfalso
        linarith [h, huI.1, w1_mem.2, ang_lt_ang (show (9:ℝ)/2 < 15 by norm_num)]
      · exact h
    · intro hu
      rw [Set.mem_singleton_iff] at hu
      subst hu
      refine ⟨?_, ?_⟩
      · rw [h15, h1000]
        constructor
        · linarith [ang15_lt_w2]
        · linarith [w2_mem.2, ang_lt_ang (show (400:ℝ) < 1000 by norm_num)]
      · rw [psiA2_add_pi, psiA2_eq_three_psiE, w2_zero]; ring
  have hz : zA4 = sInf {u : ℝ | u ∈ Set.Icc (2 * Real.pi - ang (1/15)) (2 * Real.pi - ang (1/1000))
      ∧ psiA2 u = 0} := rfl
  rw [hz, hset, csInf_singleton]

/-- **The shape of the `z`-window of the `A` branch.** -/
theorem psiA2_shape :
    (Work.BoxShrink.PinchOff.RefuteDrop.zA1 < Work.BoxShrink.PinchOff.RefuteDrop.zA2 ∧
        Work.BoxShrink.PinchOff.RefuteDrop.zA2 < Work.BoxShrink.PinchOff.RefuteDrop.zA3 ∧
        Work.BoxShrink.PinchOff.RefuteDrop.zA3 < Work.BoxShrink.PinchOff.RefuteDrop.zA4 ∧
        Work.BoxShrink.PinchOff.RefuteDrop.zA4 < 2 * Real.pi) ∧
      (Work.BoxShrink.PinchOff.RefuteDrop.zA1 ∈ Set.Ioo (Work.BoxShrink.PinchOff.RefuteDrop.ang (5/2)) (Work.BoxShrink.PinchOff.RefuteDrop.ang (9/2)) ∧
        Work.BoxShrink.PinchOff.RefuteDrop.zA2 ∈ Set.Ioo (Work.BoxShrink.PinchOff.RefuteDrop.ang 14) (Work.BoxShrink.PinchOff.RefuteDrop.ang 400) ∧
        Work.BoxShrink.PinchOff.RefuteDrop.zA3 ∈ Set.Ioo (2 * Real.pi - Work.BoxShrink.PinchOff.RefuteDrop.ang (2/5)) (2 * Real.pi - Work.BoxShrink.PinchOff.RefuteDrop.ang (1/5)) ∧
        Work.BoxShrink.PinchOff.RefuteDrop.zA4 ∈ Set.Ioo (2 * Real.pi - Work.BoxShrink.PinchOff.RefuteDrop.ang (1/15)) (2 * Real.pi - Work.BoxShrink.PinchOff.RefuteDrop.ang (1/1000))) ∧
      (∀ u : ℝ, u ∈ Set.Icc (0:ℝ) (2 * Real.pi) →
        (Work.BoxShrink.PinchOff.RefuteDrop.psiA2 u ≤ 0 ↔
          u ∈ Set.Icc Work.BoxShrink.PinchOff.RefuteDrop.zA1 Work.BoxShrink.PinchOff.RefuteDrop.zA2 ∪ Set.Icc Work.BoxShrink.PinchOff.RefuteDrop.zA3 Work.BoxShrink.PinchOff.RefuteDrop.zA4)) ∧
      (∀ u : ℝ, u ∈ Set.Icc (0:ℝ) (2 * Real.pi) →
        (Work.BoxShrink.PinchOff.RefuteDrop.psiA2 u < 0 ↔
          u ∈ Set.Ioo Work.BoxShrink.PinchOff.RefuteDrop.zA1 Work.BoxShrink.PinchOff.RefuteDrop.zA2 ∪ Set.Ioo Work.BoxShrink.PinchOff.RefuteDrop.zA3 Work.BoxShrink.PinchOff.RefuteDrop.zA4)) := by
  have hlt12 : ang (5/2) < ang (9/2) := ang_lt_ang (by norm_num)
  have hlt24 : ang (9/2) < ang 14 := ang_lt_ang (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [zA1_eq, zA2_eq, zA3_eq, zA4_eq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · linarith [w1_mem.2, w2_mem.1, hlt24]
    · linarith [w2_mem.2, w1_mem.1, (ang_lt_pi (by norm_num : (0:ℝ) < 400)).le,
        (ang_pos (by norm_num : (0:ℝ) < 5/2)).le, Real.pi_pos]
    · linarith [w1_mem.2, w2_mem.1, hlt24]
    · linarith [w2_mem.2, (ang_lt_pi (by norm_num : (0:ℝ) < 400)).le]
  · rw [zA1_eq, zA2_eq, zA3_eq, zA4_eq]
    refine ⟨w1_mem, w2_mem, ?_, ?_⟩
    · rw [two_pi_sub_ang (2/5) (by norm_num : (0:ℝ) < 2/5),
        two_pi_sub_ang (1/5) (by norm_num : (0:ℝ) < 1/5)]
      constructor <;>
        linarith [w1_mem.1, w1_mem.2, ang_lt_ang (show (9:ℝ)/2 < 5 by norm_num)]
    · rw [two_pi_sub_ang (1/15) (by norm_num : (0:ℝ) < 1/15),
        two_pi_sub_ang (1/1000) (by norm_num : (0:ℝ) < 1/1000)]
      constructor
      · linarith [ang15_lt_w2]
      · linarith [w2_mem.2, ang_lt_ang (show (400:ℝ) < 1000 by norm_num)]
  · intro u hu
    rw [zA1_eq, zA2_eq, zA3_eq, zA4_eq, psiA2_eq_three_psiE]
    constructor
    · intro h
      exact (psiE_le_zero_iff_Icc_two_pi u hu).mp (by linarith)
    · intro h
      have := (psiE_le_zero_iff_Icc_two_pi u hu).mpr h
      linarith
  · intro u hu
    rw [zA1_eq, zA2_eq, zA3_eq, zA4_eq, psiA2_eq_three_psiE]
    constructor
    · intro h
      exact (psiE_lt_zero_iff_Ioo_two_pi u hu).mp (by linarith)
    · intro h
      have := (psiE_lt_zero_iff_Ioo_two_pi u hu).mpr h
      linarith
