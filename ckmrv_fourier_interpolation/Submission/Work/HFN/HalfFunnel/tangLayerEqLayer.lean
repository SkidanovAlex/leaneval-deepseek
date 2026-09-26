/-
# The tangency layer agrees with the paper's layer

`tangLayer ℓ d τ r = layer (Gcusp ℓ d) ℓ d τ r` for `τ` in the tangency region and `r ≠ 0`.

Both sides are `sinSq r · (contour profile) + highPart`, so it suffices to identify the profiles:

  `tangPhi τ (r²) = ∫_0¹ K(τ,it)e^{-πr²t}dt + ∫_1^∞ (K - Aexp)(τ,it)e^{-πr²t}dt`.

This is the telescoping

  `∫_0^{1/2} + ∫_{1/2}^{3/2} + ∫_{3/2}^∞ (K - A) - ∫_1^{3/2} A = ∫_0¹ K + ∫_1^∞ (K - A)`

obtained from the disjoint decompositions `[0,1] = [0,1/2] ∪ [1/2,1]`,
`[1/2,3/2] = [1/2,1] ∪ [1,3/2]`, `(1,∞) = (1,3/2] ∪ (3/2,∞)` and `K·g = (K-A)·g + A·g` on
`(1,3/2]`.  All the set integrals are genuine: on `[0,1/2]` the kernel obeys the cusp flatness
`tangKaxisFlatLow`, on `[1/2,3/2]` it is bounded because the contour avoids the coincidence
divisor (`tangOrbitRectCl` + `tangPoleGeom`), and on `(3/2,∞)` the cusp expansion
`tangTailExpansion` makes `(K - A)g` integrable.
-/
import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.tangLayerDefs
import Submission.Work.HFN.HalfFunnel.tangTailExpansion
import Submission.Work.Asymptotics.HalfFunnel.tangKaxisFlatLow
import Submission.Work.Asymptotics.HalfFunnel.exists_bound_Kfun_off_coincidence
import Submission.Work.Asymptotics.paperLayer_agreement
import Submission.Work.Asymptotics.HalfFunnel.tangPoleGeom
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq

set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter UpperHalfPlane
open scoped Topology

namespace Work.HFN.HalfFunnel
open Work.Asymptotics Work.Asymptotics.HalfFunnel  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open Work.Kernels

/-- The contour point `ctFun t` has coordinate `t·i` for `t > 0`. -/
lemma ctFun_coe_pos {t : ℝ} (ht : 0 < t) : ((ctFun t : ℍ) : ℂ) = (t : ℂ) * Complex.I := by
  unfold ctFun
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (z := Complex.I * (t : ℂ))
    (by simpa [Complex.mul_im] using ht), UpperHalfPlane.coe_mk]
  ring

lemma ctFun_re_contour {t : ℝ} (ht : 0 < t) : (ctFun t).re = 0 := by
  rw [← UpperHalfPlane.coe_re, ctFun_coe_pos ht]
  simp

lemma ctFun_im_contour {t : ℝ} (ht : 0 < t) : (ctFun t).im = t := by
  rw [← UpperHalfPlane.coe_im, ctFun_coe_pos ht]
  simp

/-- The abstract telescoping behind `tangLayerEqLayer`. -/
private lemma tangTelescope (F H Ag : ℝ → ℂ) (hHF : ∀ t, H t = F t - Ag t)
    (I1 : IntegrableOn F (Set.Ioc (0 : ℝ) (1 / 2)))
    (I2 : IntegrableOn F (Set.Ioc (1 / 2 : ℝ) 1))
    (I3 : IntegrableOn F (Set.Ioc (1 : ℝ) (3 / 2)))
    (I5 : IntegrableOn Ag (Set.Ioc (1 : ℝ) (3 / 2)))
    (J3 : IntegrableOn H (Set.Ioc (1 : ℝ) (3 / 2)))
    (J4 : IntegrableOn H (Set.Ioi (3 / 2 : ℝ))) :
    (∫ t in Set.Ioc (0 : ℝ) (1 / 2), F t) + (∫ t in Set.Ioc (1 / 2 : ℝ) (3 / 2), F t)
        + (∫ t in Set.Ioi (3 / 2 : ℝ), H t) - (∫ t in Set.Ioc (1 : ℝ) (3 / 2), Ag t)
      = (∫ t in Set.Ioc (0 : ℝ) 1, F t) + ∫ t in Set.Ici (1 : ℝ), H t := by
  have hdisj₁ : Disjoint (Set.Ioc (0 : ℝ) (1 / 2)) (Set.Ioc (1 / 2 : ℝ) 1) := by
    rw [Set.disjoint_left]
    intro t h1 h2
    exact absurd h2.1 (not_lt.mpr h1.2)
  have hdisj₂ : Disjoint (Set.Ioc (1 / 2 : ℝ) 1) (Set.Ioc (1 : ℝ) (3 / 2)) := by
    rw [Set.disjoint_left]
    intro t h1 h2
    exact absurd h2.1 (not_lt.mpr h1.2)
  have hdisj₃ : Disjoint (Set.Ioc (1 : ℝ) (3 / 2)) (Set.Ioi (3 / 2 : ℝ)) := by
    rw [Set.disjoint_left]
    intro t h1 h2
    exact absurd h2 (not_lt.mpr h1.2)
  have hA : (∫ t in Set.Ioc (0 : ℝ) 1, F t)
      = (∫ t in Set.Ioc (0 : ℝ) (1 / 2), F t) + (∫ t in Set.Ioc (1 / 2 : ℝ) 1, F t) := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1),
      MeasureTheory.setIntegral_union hdisj₁ measurableSet_Ioc I1 I2]
  have hB : (∫ t in Set.Ioc (1 / 2 : ℝ) (3 / 2), F t)
      = (∫ t in Set.Ioc (1 / 2 : ℝ) 1, F t) + (∫ t in Set.Ioc (1 : ℝ) (3 / 2), F t) := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc (by norm_num : (1 / 2 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) ≤ 3 / 2),
      MeasureTheory.setIntegral_union hdisj₂ measurableSet_Ioc I2 I3]
  have hD : (∫ t in Set.Ioi (1 : ℝ), H t)
      = (∫ t in Set.Ioc (1 : ℝ) (3 / 2), H t) + (∫ t in Set.Ioi (3 / 2 : ℝ), H t) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (1 : ℝ) ≤ 3 / 2),
      MeasureTheory.setIntegral_union hdisj₃ measurableSet_Ioi J3 J4]
  have hE : (∫ t in Set.Ioc (1 : ℝ) (3 / 2), H t)
      = (∫ t in Set.Ioc (1 : ℝ) (3 / 2), F t) - (∫ t in Set.Ioc (1 : ℝ) (3 / 2), Ag t) := by
    have hcongr : (∫ t in Set.Ioc (1 : ℝ) (3 / 2), H t)
        = ∫ t in Set.Ioc (1 : ℝ) (3 / 2), (F t - Ag t) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t _ => hHF t)
    rw [hcongr, MeasureTheory.integral_sub I3 I5]
  rw [hA, MeasureTheory.integral_Ici_eq_integral_Ioi, hD, hE, hB]
  ring

theorem tangLayerEqLayer (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (r : ℝ) (hτ : τ ∈ ctanRegion) (hr : r ≠ 0) :
    tangLayer ℓ d τ r = Work.Asymptotics.layer (Gcusp ℓ d) ℓ d τ r := by
  have hτcl : τ ∈ ctanCl := ctanRegion_subset_ctanCl hτ
  set F : ℝ → ℂ := fun t => Kaxis (Kfun ℓ d) τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
    with hF
  set H : ℝ → ℂ := fun t => (Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t)
    * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hH
  set Ag : ℝ → ℂ := fun t => Aexp (Gcusp ℓ d) τ t
    * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hAg
  have hHF : ∀ t : ℝ, H t = F t - Ag t := by
    intro t
    rw [hH, hF, hAg]
    ring
  -- the Gaussian factor has modulus at most one
  have hexpnorm : ∀ t : ℝ, 0 ≤ t →
      ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ ≤ 1 := by
    intro t ht
    rw [Complex.norm_exp]
    refine Real.exp_le_one_iff.mpr ?_
    have h : (Real.pi * (r : ℂ) ^ 2 * (t : ℂ)) = ((Real.pi * r ^ 2 * t : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h, Complex.neg_re, Complex.ofReal_re]
    have h1 : (0 : ℝ) ≤ Real.pi * r ^ 2 * t :=
      mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg r)) ht
    linarith
  -- a uniform bound for the kernel on `(0, 3/2]`
  obtain ⟨c, hc0, hc⟩ := tangKaxisFlatLow ℓ d hd 0 le_rfl
  have hc' : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ‖Kaxis (Kfun ℓ d) τ t‖ ≤ c := by
    intro t ht ht2
    have h := hc τ t hτcl ht ht2
    simpa using h
  obtain ⟨CK, hCKpos, hCK⟩ := exists_bound_Kfun_off_coincidence ℓ d hd
    (S := ({τ} : Set ℍ)) (T := ctFun '' Set.Icc (1 / 2 : ℝ) (3 / 2)) isCompact_singleton
    (isCompact_Icc.image_of_continuousOn
      (continuousOn_ctFun.mono (by intro s hs; exact lt_of_lt_of_le (by norm_num) hs.1)))
    (by
      rintro τ' hτ' z ⟨s, hs, rfl⟩
      have hτ'eq : τ' = τ := Set.mem_singleton_iff.mp hτ'
      rw [hτ'eq]
      have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hs.1
      intro hj
      have hzeq : ctFun s = poleOne τ :=
        tangOrbitRectCl τ (ctFun s) hτcl
          (by rw [ctFun_re_contour hspos])
          (by rw [ctFun_re_contour hspos]; norm_num)
          (by rw [ctFun_im_contour hspos]; exact hs.1)
          (by rw [ctFun_im_contour hspos]; exact hs.2)
          hj.symm
      have hp := tangPoleGeom τ hτ
      have hre : (ctFun s).re = (poleOne τ).re := by rw [hzeq]
      rw [ctFun_re_contour hspos] at hre
      linarith [hp.1, hre])
  have hKbd : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ‖Kaxis (Kfun ℓ d) τ t‖ ≤ max c CK :=
    fun t ht ht2 => le_trans (hc' t ht ht2) (le_max_left _ _)
  have hKbd2 : ∀ t : ℝ, 1 / 2 ≤ t → t ≤ 3 / 2 → ‖Kaxis (Kfun ℓ d) τ t‖ ≤ max c CK := by
    intro t ht1 ht2
    have htpos : 0 < t := by linarith
    have h : ‖Kfun ℓ d τ (ctFun t)‖ ≤ CK :=
      hCK τ (by simp) (ctFun t) ⟨t, ⟨ht1, ht2⟩, rfl⟩
    rw [ctFun_eq_imagAxis htpos] at h
    have hka : Kaxis (Kfun ℓ d) τ t = Kfun ℓ d τ (imagAxis t htpos) := by
      rw [Kaxis, dif_pos htpos]
    rw [hka]
    exact le_trans h (le_max_right _ _)
  -- a bound for `Aexp` on `[1,3/2]`
  have hAcont : ContinuousOn (fun t : ℝ => Aexp (Gcusp ℓ d) τ t) (Set.Icc (1 : ℝ) (3 / 2)) :=
    ((continuous_Aexp_tang ℓ d hd).comp
      (continuous_const.prodMk continuous_id)).continuousOn
  obtain ⟨CA, hCA⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := (3 / 2 : ℝ))).exists_bound_of_continuousOn
    hAcont
  have hCA0 : (0 : ℝ) ≤ max CA 0 := le_max_right _ _
  have hCAle : ∀ t ∈ Set.Icc (1 : ℝ) (3 / 2), ‖Aexp (Gcusp ℓ d) τ t‖ ≤ max CA 0 :=
    fun t ht => le_trans (hCA t ht) (le_max_left _ _)
  -- integrability of `F`
  have hvolIoc : ∀ a b : ℝ, volume (Set.Ioc a b) < ⊤ := by
    intro a b
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hFmeas : AEStronglyMeasurable F (volume.restrict (Set.Ioc (0 : ℝ) (3 / 2 : ℝ))) := by
    rw [hF]
    exact ((measurable_Kaxis_Kfun ℓ d hd τ).aestronglyMeasurable).mul
      (by fun_prop : Continuous fun t : ℝ =>
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))).aestronglyMeasurable
  have hFbd : ∀ t ∈ Set.Ioc (0 : ℝ) (3 / 2 : ℝ), ‖F t‖ ≤ max c CK := by
    intro t ht
    have htpos : 0 < t := ht.1
    rw [hF, norm_mul]
    have h1 : ‖Kaxis (Kfun ℓ d) τ t‖ ≤ max c CK := by
      by_cases h2 : t ≤ 1 / 2
      · exact hKbd t htpos h2
      · push_neg at h2
        exact hKbd2 t h2.le ht.2
    calc ‖Kaxis (Kfun ℓ d) τ t‖ * ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖
        ≤ max c CK * 1 := mul_le_mul h1 (hexpnorm t (le_of_lt htpos)) (norm_nonneg _)
            (by positivity)
      _ = max c CK := mul_one _
  have hI : IntegrableOn F (Set.Ioc (0 : ℝ) (3 / 2 : ℝ)) :=
    MeasureTheory.IntegrableOn.of_bound (hvolIoc 0 (3 / 2)) hFmeas _
      (by
        filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
        exact hFbd t ht)
  have hI1 : IntegrableOn F (Set.Ioc (0 : ℝ) (1 / 2)) :=
    hI.mono_set (Set.Ioc_subset_Ioc_right (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2))
  have hI2 : IntegrableOn F (Set.Ioc (1 / 2 : ℝ) 1) :=
    hI.mono_set (by intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hI3 : IntegrableOn F (Set.Ioc (1 : ℝ) (3 / 2)) :=
    hI.mono_set (Set.Ioc_subset_Ioc_left (by norm_num : (0 : ℝ) ≤ 1))
  -- integrability of `Ag`
  have hAgmeas : AEStronglyMeasurable Ag (volume.restrict (Set.Ioc (1 : ℝ) (3 / 2))) := by
    rw [hAg]
    exact ((continuous_Aexp_tang ℓ d hd).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable.mul
      (by fun_prop : Continuous fun t : ℝ =>
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))).aestronglyMeasurable
  have hAgbd : ∀ t ∈ Set.Ioc (1 : ℝ) (3 / 2), ‖Ag t‖ ≤ max CA 0 := by
    intro t ht
    rw [hAg, norm_mul]
    calc ‖Aexp (Gcusp ℓ d) τ t‖ * ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖
        ≤ max CA 0 * 1 := mul_le_mul (hCAle t ⟨le_of_lt ht.1, ht.2⟩)
          (hexpnorm t (by linarith [ht.1])) (norm_nonneg _) hCA0
      _ = max CA 0 := mul_one _
  have hAgI : IntegrableOn Ag (Set.Ioc (1 : ℝ) (3 / 2)) :=
    MeasureTheory.IntegrableOn.of_bound (hvolIoc 1 (3 / 2)) hAgmeas _
      (by
        filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
        exact hAgbd t ht)
  -- integrability of `H` on the window
  have hHmeas : AEStronglyMeasurable H (volume.restrict (Set.Ioc (1 : ℝ) (3 / 2))) := by
    rw [hH]
    exact (((measurable_Kaxis_Kfun ℓ d hd τ).aestronglyMeasurable).sub
      ((continuous_Aexp_tang ℓ d hd).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable).mul
      (by fun_prop : Continuous fun t : ℝ =>
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))).aestronglyMeasurable
  have hHbd : ∀ t ∈ Set.Ioc (1 : ℝ) (3 / 2), ‖H t‖ ≤ max c CK + max CA 0 := by
    intro t ht
    rw [hH, norm_mul]
    have h1 : ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖ ≤ max c CK + max CA 0 := by
      refine le_trans (norm_sub_le _ _) (add_le_add (hKbd2 t (by linarith [ht.1]) ht.2)
        (hCAle t ⟨le_of_lt ht.1, ht.2⟩))
    calc ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
          * ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖
        ≤ (max c CK + max CA 0) * 1 := mul_le_mul h1 (hexpnorm t (by linarith [ht.1]))
          (norm_nonneg _) (add_nonneg (le_trans hc0.le (le_max_left _ _)) hCA0)
      _ = max c CK + max CA 0 := mul_one _
  have hH3 : IntegrableOn H (Set.Ioc (1 : ℝ) (3 / 2)) :=
    MeasureTheory.IntegrableOn.of_bound (hvolIoc 1 (3 / 2)) hHmeas _
      (by
        filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
        exact hHbd t ht)
  -- integrability of `H` on the tail
  obtain ⟨Ct, Mt, T₀, hCt, hMt, hT₀, htail⟩ := tangTailExpansion ℓ d hd
  have hmaj : IntegrableOn (fun t : ℝ => Ct * Real.exp (Real.pi * T₀) * 2 ^ Mt
      * (t ^ Mt * Real.exp (-(Real.pi * t)))) (Set.Ioi (3 / 2 : ℝ)) :=
    ((integrableOn_rpow_mul_exp_neg_mul_Ioi_pos Mt (a := 3 / 2) (d := Real.pi)
      (by norm_num) Real.pi_pos).const_mul _)
  have hHmeas' : AEStronglyMeasurable H (volume.restrict (Set.Ioi (3 / 2 : ℝ))) := by
    rw [hH]
    exact (((measurable_Kaxis_Kfun ℓ d hd τ).aestronglyMeasurable).sub
      ((continuous_Aexp_tang ℓ d hd).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable).mul
      (by fun_prop : Continuous fun t : ℝ =>
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))).aestronglyMeasurable
  have hH4 : IntegrableOn H (Set.Ioi (3 / 2 : ℝ)) := by
    refine Integrable.mono' hmaj hHmeas' ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht3 : (3 / 2 : ℝ) < t := ht
    have ht1 : (1 : ℝ) < t := by linarith
    have ht0 : (0 : ℝ) < t := by linarith
    rw [hH, norm_mul]
    have h1 : ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
        ≤ Ct * (1 + t) ^ Mt * Real.exp (-(Real.pi * (t - T₀))) := htail τ t hτcl (le_of_lt ht3)
    have h2 : ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ ≤ 1 := hexpnorm t (le_of_lt ht0)
    have h3 : (1 + t) ^ Mt ≤ 2 ^ Mt * t ^ Mt := by
      have h := Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ 1 + t) (by linarith : 1 + t ≤ 2 * t)
        hMt
      rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (0 : ℝ) ≤ t)] at h
    have h4 : Real.exp (-(Real.pi * (t - T₀))) = Real.exp (Real.pi * T₀) * Real.exp (-(Real.pi * t)) := by
      rw [← Real.exp_add]; ring_nf
    calc ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
          * ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖
        ≤ (Ct * (1 + t) ^ Mt * Real.exp (-(Real.pi * (t - T₀)))) * 1 :=
          mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (mul_nonneg hCt.le
            (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 1 + t) _)) (Real.exp_pos _).le)
      _ = Ct * (1 + t) ^ Mt * Real.exp (-(Real.pi * (t - T₀))) := mul_one _
      _ ≤ Ct * (2 ^ Mt * t ^ Mt) * (Real.exp (Real.pi * T₀) * Real.exp (-(Real.pi * t))) := by
          rw [← h4]
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hCt.le)
            (Real.exp_pos _).le
      _ = Ct * Real.exp (Real.pi * T₀) * 2 ^ Mt * (t ^ Mt * Real.exp (-(Real.pi * t))) := by ring
  -- the telescoping
  have htel := tangTelescope F H Ag hHF hI1 hI2 hI3 hAgI hH3 hH4
  -- the Gaussian substitution
  have hgauss : ∀ t : ℝ, tangGauss (r ^ 2) t
      = Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
    intro t
    rw [tangGauss]
    congr 1
    push_cast
    ring
  have hLow : tangLow ℓ d τ (r ^ 2) = ∫ t in Set.Ioc (0 : ℝ) (1 / 2), F t := by
    rw [tangLow, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    rw [hF, hgauss t]
  have hSpike : tangSpike ℓ d τ (r ^ 2) = ∫ t in Set.Ioc (1 / 2 : ℝ) (3 / 2), F t := by
    rw [tangSpike, intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2)]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    rw [hF, hgauss t]
  have hTail : tangTail ℓ d τ (r ^ 2) = ∫ t in Set.Ioi (3 / 2 : ℝ), H t := by
    rw [tangTail]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [hH, hgauss t]
  have hAp : tangA ℓ d τ (r ^ 2) = ∫ t in Set.Ioc (1 : ℝ) (3 / 2), Ag t := by
    rw [tangA, intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 3 / 2)]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    rw [hAg, hgauss t]
  have hLLow : Work.Asymptotics.layerLow ℓ d τ r = sinSq r * ∫ t in Set.Ioc (0 : ℝ) 1, F t := by
    rw [Work.Asymptotics.layerLow, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hLTrunc : Work.Asymptotics.layerTrunc (Gcusp ℓ d) ℓ d τ r
      = sinSq r * ∫ t in Set.Ici (1 : ℝ), H t := by
    rw [Work.Asymptotics.layerTrunc]
  rw [tangLayer, if_neg hr, Work.Asymptotics.layer, if_neg hr, Work.Asymptotics.paperLayer,
    hLLow, hLTrunc, tangPhi, hLow, hSpike, hTail, hAp, htel]
  ring

end Work.HFN.HalfFunnel
