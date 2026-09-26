/-
# The `r`-seminorm bound for the tangency layer

`tangLayer = sinSq r · tangPhi τ (r²) + highPart` (punctured at `r = 0`), where
`tangPhi = tangLow + tangSpike + tangTail - tangA`.  Each of the four pieces has derivatives
decaying faster than every power of `1 + x` (`tangLowDeriv`, `tangSpikeDeriv`, `tangTailDeriv`,
`tangADeriv`), so the sum does too; `exists_seminorm_bound_of_iteratedDeriv_bound_poly` then
turns this into the weighted bound `|r|^k ‖∂^l (sinSq · tangPhi(·²))‖`, and the `highPart`
contribution is `highPart_seminorm_scaled`.  The puncture at `r = 0` is removed with
`punctured_iteratedDeriv` (evenness in `r`).
-/
import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.tangLayerDefs
import Submission.Work.HFN.HalfFunnel.tangLowDeriv
import Submission.Work.HFN.HalfFunnel.tangSpikeDeriv
import Submission.Work.HFN.HalfFunnel.tangTailDeriv
import Submission.Work.HFN.HalfFunnel.tangADeriv
import Submission.Work.Asymptotics.HalfFunnel.tangKaxisFlatLow
import Submission.Work.HFN.HalfFunnel.tangTailExpansion
import Submission.Work.HFN.HalfFunnel.tangLayerEqLayer
import Submission.Work.HFN.HalfFunnel.lowRegion_badLine
import Submission.Work.Asymptotics.highPart_seminorm_scaled
import Submission.Work.Asymptotics.punctured_iteratedDeriv
import Submission.Work.HFN.kernelTransform_seminorm_on_compact

set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter UpperHalfPlane
open scoped Topology ContDiff

namespace Work.HFN.HalfFunnel
open Work.Asymptotics Work.Asymptotics.HalfFunnel  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open Work.Kernels

/-- **The kernel is bounded on the spike window `[1/2,3/2]` for `τ` in the tangency region.** -/
lemma exists_bound_Kaxis_window (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hτ : τ ∈ ctanRegion) :
    ∃ CK : ℝ, 0 < CK ∧ ∀ t : ℝ, 1 / 2 ≤ t → t ≤ 3 / 2 →
      ‖Kaxis (Kfun ℓ d) τ t‖ ≤ CK := by
  have hτcl : τ ∈ ctanCl := ctanRegion_subset_ctanCl hτ
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
  refine ⟨CK, hCKpos, fun t ht1 ht2 => ?_⟩
  have htpos : 0 < t := by linarith
  have h : ‖Kfun ℓ d τ (ctFun t)‖ ≤ CK := hCK τ (by simp) (ctFun t) ⟨t, ⟨ht1, ht2⟩, rfl⟩
  rw [ctFun_eq_imagAxis htpos] at h
  have hka : Kaxis (Kfun ℓ d) τ t = Kfun ℓ d τ (imagAxis t htpos) := by
    rw [Kaxis, dif_pos htpos]
  rw [hka]
  exact h

/-! ## Smoothness of the four pieces -/

lemma contDiffOn_tangLow (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hτ : τ ∈ ctanRegion) :
    ContDiffOn ℝ ω (tangLow ℓ d τ) (Set.Ioi (-1)) := by
  obtain ⟨c, hc0, hc⟩ := tangKaxisFlatLow ℓ d hd 0 le_rfl
  have hτcl : τ ∈ ctanCl := ctanRegion_subset_ctanCl hτ
  set κ : ℝ → ℂ := (Set.Ioc (0 : ℝ) (1 / 2)).indicator (fun t => Kaxis (Kfun ℓ d) τ t) with hκ
  have hmeas : AEStronglyMeasurable κ (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ((measurable_Kaxis_Kfun ℓ d hd τ).indicator measurableSet_Ioc).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), ‖κ t‖ ≤ c := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    by_cases hmem : t ∈ Set.Ioc (0 : ℝ) (1 / 2)
    · rw [hκ, Set.indicator_of_mem hmem]
      have h := hc τ t hτcl hmem.1 hmem.2
      simpa using h
    · rw [hκ, Set.indicator_of_notMem hmem, norm_zero]
      exact hc0.le
  have hkey := contDiffOn_intervalIntegral_exp_ofReal (κ := κ) hc0.le hmeas hbound
  refine hkey.congr (fun x _ => ?_)
  show tangLow ℓ d τ x = ∫ t in (0 : ℝ)..1, κ t * Complex.exp (-(Real.pi * (x : ℂ) * (t : ℂ)))
  rw [tangLow, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), hκ]
  have h1 : (∫ t in Set.Ioc (0 : ℝ) 1,
        (Set.Ioc (0 : ℝ) (1 / 2)).indicator (fun t => Kaxis (Kfun ℓ d) τ t) t
          * Complex.exp (-(Real.pi * (x : ℂ) * (t : ℂ))))
      = ∫ t in Set.Ioc (0 : ℝ) 1,
          (Set.Ioc (0 : ℝ) (1 / 2)).indicator
            (fun t => Kaxis (Kfun ℓ d) τ t
              * Complex.exp (-(Real.pi * (x : ℂ) * (t : ℂ)))) t := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    by_cases hmem : t ∈ Set.Ioc (0 : ℝ) (1 / 2)
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, zero_mul]
  rw [h1, MeasureTheory.setIntegral_indicator measurableSet_Ioc]
  rw [show Set.Ioc (0 : ℝ) 1 ∩ Set.Ioc (0 : ℝ) (1 / 2) = Set.Ioc (0 : ℝ) (1 / 2) from by
    ext t; constructor
    · intro h; exact h.2
    · intro h; exact ⟨⟨h.1, by linarith [h.2]⟩, h⟩]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
  rw [tangGauss]

lemma contDiffOn_tangSpike (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hτ : τ ∈ ctanRegion) :
    ContDiffOn ℝ ω (tangSpike ℓ d τ) (Set.Ioi (-1)) := by
  obtain ⟨CK, hCKpos, hCK⟩ := exists_bound_Kaxis_window ℓ d hd τ hτ
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Kaxis (Kfun ℓ d) τ t)
      (volume.restrict (Set.Ioc (1 / 2 : ℝ) (3 / 2))) :=
    (measurable_Kaxis_Kfun ℓ d hd τ).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) (3 / 2))),
      ‖Kaxis (Kfun ℓ d) τ t‖ ≤ CK := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact hCK t (le_of_lt ht.1) ht.2
  have hkey := contDiffOn_intervalIntegral_exp_ofReal_general (κ := fun t : ℝ => Kaxis (Kfun ℓ d) τ t)
    (a := 1 / 2) (b := 3 / 2) (B := CK) (by norm_num) (by norm_num) hCKpos.le hmeas hbound
  refine hkey.congr (fun x _ => ?_)
  show tangSpike ℓ d τ x = ∫ t in (1 / 2 : ℝ)..(3 / 2),
    Kaxis (Kfun ℓ d) τ t * Complex.exp (-(Real.pi * (x : ℂ) * (t : ℂ)))
  rw [tangSpike]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [tangGauss]

lemma contDiffOn_tangA (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) :
    ContDiffOn ℝ ω (tangA ℓ d τ) (Set.Ioi (-1)) := by
  obtain ⟨CA, hCA⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := (3 / 2 : ℝ))).exists_bound_of_continuousOn
    (((continuous_Aexp_tang ℓ d hd).comp
      (continuous_const.prodMk continuous_id)).continuousOn)
  have hCA0 : (0 : ℝ) ≤ max CA 0 := le_max_right _ _
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Aexp (Gcusp ℓ d) τ t)
      (volume.restrict (Set.Ioc (1 : ℝ) (3 / 2))) :=
    ((continuous_Aexp_tang ℓ d hd).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc (1 : ℝ) (3 / 2))),
      ‖Aexp (Gcusp ℓ d) τ t‖ ≤ max CA 0 := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact le_trans (hCA t ⟨le_of_lt ht.1, ht.2⟩) (le_max_left _ _)
  have hkey := contDiffOn_intervalIntegral_exp_ofReal_general (κ := fun t : ℝ => Aexp (Gcusp ℓ d) τ t)
    (a := 1) (b := 3 / 2) (B := max CA 0) (by norm_num) (by norm_num) hCA0 hmeas hbound
  refine hkey.congr (fun x _ => ?_)
  show tangA ℓ d τ x = ∫ t in (1 : ℝ)..(3 / 2),
    Aexp (Gcusp ℓ d) τ t * Complex.exp (-(Real.pi * (x : ℂ) * (t : ℂ)))
  rw [tangA]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [tangGauss]

lemma contDiffOn_tangTail (n : ℕ) (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) (hτ : τ ∈ ctanRegion) :
    ContDiffOn ℝ (n : ℕ∞ω) (tangTail ℓ d τ) (Set.Ioi (-1)) := by
  obtain ⟨Ct, Mt, T₀, hCt, hMt, hT₀, htail⟩ := tangTailExpansion ℓ d hd
  have hτcl : τ ∈ ctanCl := ctanRegion_subset_ctanCl hτ
  set C' : ℝ := Ct * 2 ^ Mt * Real.exp (Real.pi * T₀) with hC'
  have hC'0 : 0 ≤ C' := by rw [hC']; positivity
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t)
      (volume.restrict (Set.Ioi (3 / 2 : ℝ))) :=
    ((measurable_Kaxis_Kfun ℓ d hd τ).aestronglyMeasurable).sub
      ((continuous_Aexp_tang ℓ d hd).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hb : ∀ᵐ t ∂(volume.restrict (Set.Ioi (3 / 2 : ℝ))),
      ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
        ≤ C' * t ^ Mt * Real.exp (-(Real.pi * t)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) < t := lt_trans (by norm_num) ht
    have h1 := htail τ t hτcl (le_of_lt ht)
    have h2 : (1 + t) ^ Mt ≤ 2 ^ Mt * t ^ Mt := by
      have h := Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ 1 + t)
        (by linarith : 1 + t ≤ 2 * t) hMt
      rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (0 : ℝ) ≤ t)] at h
    have h4 : Real.exp (-(Real.pi * (t - T₀))) = Real.exp (Real.pi * T₀) * Real.exp (-(Real.pi * t)) := by
      rw [← Real.exp_add]; ring_nf
    rw [h4] at h1
    calc ‖Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
        ≤ Ct * (1 + t) ^ Mt * (Real.exp (Real.pi * T₀) * Real.exp (-(Real.pi * t))) := h1
      _ ≤ Ct * (2 ^ Mt * t ^ Mt) * (Real.exp (Real.pi * T₀) * Real.exp (-(Real.pi * t))) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
          exact mul_le_mul_of_nonneg_left h2 hCt.le
      _ = C' * t ^ Mt * Real.exp (-(Real.pi * t)) := by rw [hC']; ring
  have hkey := contDiffOn_Ioi_tail n (fun t : ℝ => Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t)
    hmeas hC'0 hMt hb
  refine hkey.congr (fun x _ => ?_)
  show tangTail ℓ d τ x = ∫ t in Set.Ioi (3 / 2 : ℝ),
    (Kaxis (Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t) * (Real.exp (-(Real.pi * x * t)) : ℂ)
  rw [tangTail]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  rw [tangGauss, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- `tangPhi τ` is `C^n` on `(-1,∞)`. -/
lemma contDiffOn_tangPhi (n : ℕ) (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) (hτ : τ ∈ ctanRegion) :
    ContDiffOn ℝ (n : ℕ∞ω) (tangPhi ℓ d τ) (Set.Ioi (-1)) := by
  have h1 : ContDiffOn ℝ (n : ℕ∞ω) (tangLow ℓ d τ) (Set.Ioi (-1)) :=
    (contDiffOn_tangLow ℓ d hd τ hτ).of_le le_top
  have h2 : ContDiffOn ℝ (n : ℕ∞ω) (tangSpike ℓ d τ) (Set.Ioi (-1)) :=
    (contDiffOn_tangSpike ℓ d hd τ hτ).of_le le_top
  have h3 : ContDiffOn ℝ (n : ℕ∞ω) (tangTail ℓ d τ) (Set.Ioi (-1)) :=
    contDiffOn_tangTail n ℓ d hd τ hτ
  have h4 : ContDiffOn ℝ (n : ℕ∞ω) (tangA ℓ d τ) (Set.Ioi (-1)) :=
    (contDiffOn_tangA ℓ d hd τ).of_le le_top
  rw [show tangPhi ℓ d τ = ((tangLow ℓ d τ + tangSpike ℓ d τ) + tangTail ℓ d τ)
    - tangA ℓ d τ from rfl]
  exact ((h1.add h2).add h3).sub h4

/-! ## The punctured body -/

/-- The unpunctured layer body `sinSq r · tangPhi τ (r²) + highPart τ r`. -/
def tangBody (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (r : ℝ) : ℂ :=
  sinSq r * tangPhi ℓ d τ (r ^ 2) + highPart (Gcusp ℓ d) τ r

lemma tangBody_neg (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (r : ℝ) :
    tangBody ℓ d τ (-r) = tangBody ℓ d τ r := by
  simp only [tangBody, neg_sq, Work.HFN.sinSq_neg, Work.HFN.highPart_neg]

lemma differentiable_tangBody (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hτ : τ ∈ ctanRegion) :
    Differentiable ℝ (fun r : ℝ => tangBody ℓ d τ r) := by
  have hphi : Differentiable ℝ (fun r : ℝ => tangPhi ℓ d τ (r ^ 2)) := by
    have hcd0 : ContDiffOn ℝ (1 : ℕ∞ω) (tangPhi ℓ d τ) (Set.Ici (0 : ℝ)) :=
      (contDiffOn_tangPhi 1 ℓ d hd τ hτ).mono
        (by intro x hx
            rw [Set.mem_Ici] at hx
            exact Set.mem_Ioi.mpr (by linarith))
    have h2 : ContDiff ℝ (1 : ℕ∞ω) (fun r : ℝ => tangPhi ℓ d τ (r ^ 2)) := by
      have h := hcd0.comp_contDiff (n := (1 : ℕ∞ω)) (f := fun r : ℝ => r ^ 2) (by fun_prop)
        (fun r => sq_nonneg r)
      simpa [Function.comp_def] using h
    exact h2.differentiable one_ne_zero
  have h1 : Differentiable ℝ (fun r : ℝ => sinSq r * tangPhi ℓ d τ (r ^ 2)) :=
    (contDiff_omega_sinSq.differentiable (by simp)).mul hphi
  have h2 : Differentiable ℝ (fun r : ℝ => highPart (Gcusp ℓ d) τ r) :=
    (contDiff_omega_highPart (Gcusp ℓ d) τ).differentiable (by simp)
  exact h1.add h2


/-! ## The main bound -/

theorem tangLayerSeminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      τ ∈ ctanRegion →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => tangLayer ℓ d τ s) r‖ ≤ C := by
  intro k l
  set N : ℝ := ((k + l : ℕ) : ℝ) with hN
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  -- uniform bounds for the derivatives of `tangPhi`
  have hmn : ∀ m : ℕ, ∃ K : ℝ, 0 ≤ K ∧ (m ≤ l → ∀ (τ : ℍ), τ ∈ ctanRegion →
      ∀ x : ℝ, 0 ≤ x → ‖iteratedDeriv m (tangPhi ℓ d τ) x‖ ≤ K * (1 + x) ^ (-N)) := by
    intro m
    by_cases hm : m ≤ l
    · obtain ⟨K1, hK1, hb1⟩ := tangLowDeriv ℓ d hd m N hN0
      obtain ⟨K2, hK2, hb2⟩ := tangSpikeDeriv ℓ d hd m N hN0
      obtain ⟨K3, hK3, hb3⟩ := tangTailDeriv ℓ d hd m N hN0
      obtain ⟨K4, hK4, hb4⟩ := tangADeriv ℓ d hd m N hN0
      refine ⟨K1 + K2 + K3 + K4, by positivity, fun _ τ hτ x hx => ?_⟩
      have hnhds : Set.Ioi (-1 : ℝ) ∈ 𝓝 x := IsOpen.mem_nhds isOpen_Ioi (by rw [Set.mem_Ioi]; linarith)
      have hd1 : ContDiffAt ℝ (m : ℕ∞) (tangLow ℓ d τ) x :=
        ((contDiffOn_tangLow ℓ d hd τ hτ).contDiffAt hnhds).of_le le_top
      have hd2 : ContDiffAt ℝ (m : ℕ∞) (tangSpike ℓ d τ) x :=
        ((contDiffOn_tangSpike ℓ d hd τ hτ).contDiffAt hnhds).of_le le_top
      have hd3 : ContDiffAt ℝ (m : ℕ∞) (tangTail ℓ d τ) x :=
        (contDiffOn_tangTail m ℓ d hd τ hτ).contDiffAt hnhds
      have hd4 : ContDiffAt ℝ (m : ℕ∞) (tangA ℓ d τ) x :=
        ((contDiffOn_tangA ℓ d hd τ).contDiffAt hnhds).of_le le_top
      have hLS : iteratedDeriv m (fun y : ℝ => tangLow ℓ d τ y + tangSpike ℓ d τ y) x
          = iteratedDeriv m (tangLow ℓ d τ) x + iteratedDeriv m (tangSpike ℓ d τ) x :=
        iteratedDeriv_add hd1 hd2
      have hLST : iteratedDeriv m ((fun y : ℝ => tangLow ℓ d τ y + tangSpike ℓ d τ y)
            + tangTail ℓ d τ) x
          = iteratedDeriv m (fun y : ℝ => tangLow ℓ d τ y + tangSpike ℓ d τ y) x
            + iteratedDeriv m (tangTail ℓ d τ) x :=
        iteratedDeriv_add (hd1.add hd2) hd3
      have hLSTA : iteratedDeriv m (((fun y : ℝ => tangLow ℓ d τ y + tangSpike ℓ d τ y)
            + tangTail ℓ d τ) - tangA ℓ d τ) x
          = iteratedDeriv m ((fun y : ℝ => tangLow ℓ d τ y + tangSpike ℓ d τ y)
              + tangTail ℓ d τ) x
            - iteratedDeriv m (tangA ℓ d τ) x :=
        iteratedDeriv_sub ((hd1.add hd2).add hd3) hd4
      have hid : iteratedDeriv m (tangPhi ℓ d τ) x
          = iteratedDeriv m (tangLow ℓ d τ) x + iteratedDeriv m (tangSpike ℓ d τ) x
            + iteratedDeriv m (tangTail ℓ d τ) x - iteratedDeriv m (tangA ℓ d τ) x := by
        rw [show tangPhi ℓ d τ = ((fun y : ℝ => tangLow ℓ d τ y + tangSpike ℓ d τ y)
              + tangTail ℓ d τ) - tangA ℓ d τ from rfl, hLSTA, hLST, hLS]
      rw [hid]
      have hL1 := hb1 τ x hτ hx
      have hL2 := hb2 τ x hτ hx
      have hL3 := hb3 τ x hτ hx
      have hL4 := hb4 τ x hτ hx
      have hstep : ‖iteratedDeriv m (tangLow ℓ d τ) x + iteratedDeriv m (tangSpike ℓ d τ) x
            + iteratedDeriv m (tangTail ℓ d τ) x - iteratedDeriv m (tangA ℓ d τ) x‖
          ≤ (K1 + K2 + K3 + K4) * (1 + x) ^ (-N) := by
        refine le_trans (norm_sub_le _ _) (le_trans (add_le_add (le_trans (norm_add_le _ _)
          (add_le_add (le_trans (norm_add_le _ _) (add_le_add hL1 hL2)) hL3)) hL4) ?_)
        exact le_of_eq (by ring)
      exact hstep
    · exact ⟨0, le_rfl, fun h => absurd h hm⟩
  choose Kf hKf using hmn
  set Ktot : ℝ := ∑ m ∈ Finset.range (l + 1), Kf m with hKtot
  have hKf0 : ∀ m, 0 ≤ Kf m := fun m => (hKf m).1
  have hKtot0 : 0 ≤ Ktot := Finset.sum_nonneg (fun m _ => hKf0 m)
  have hKtotb : ∀ m : ℕ, m ≤ l → ∀ (τ : ℍ), τ ∈ ctanRegion → ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv m (tangPhi ℓ d τ) x‖ ≤ Ktot * (1 + x) ^ (-N) := by
    intro m hm τ hτ x hx
    have hmem : m ∈ Finset.range (l + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
    have h := (hKf m).2 hm τ hτ x hx
    have hle : Kf m ≤ Ktot := Finset.single_le_sum (fun i _ => hKf0 i) hmem
    have hpow : 0 ≤ (1 + x) ^ (-N) := Real.rpow_nonneg (by linarith) _
    exact le_trans h (mul_le_mul_of_nonneg_right hle hpow)
  -- the `highPart` piece and the assembly constant
  obtain ⟨chp, Nhp, hchp, hhpb⟩ := highPart_seminorm_scaled (Gcusp ℓ d)
    (fun i j => Gcusp_moderate ℓ d i j) k l
  obtain ⟨c, hc, hcomp⟩ := exists_seminorm_bound_of_iteratedDeriv_bound_poly k l (k + l) (by omega)
  set Scale : ℝ := max ((17 / 4 : ℝ) ^ Nhp) 1 with hScale
  have hScale0 : 0 ≤ Scale := le_trans (Real.rpow_nonneg (by norm_num) _) (le_max_left _ _)
  have hscale : ∀ τ ∈ ctanRegion, (scale τ) ^ Nhp ≤ Scale := by
    intro τ hτ
    have hτcl : τ ∈ ctanCl := ctanRegion_subset_ctanCl hτ
    obtain ⟨-, him2⟩ := ctanCl_im_bounds τ hτcl
    have hinv : (τ.im)⁻¹ ≤ 2 := by
      have h := (inv_le_inv₀ τ.im_pos (by norm_num : (0 : ℝ) < 1 / 2)).mpr hτ.2.1
      simpa using h
    have hnorm : ‖(τ : ℂ)‖ ≤ 5 / 4 := by
      have h := Complex.norm_le_abs_re_add_abs_im (τ : ℂ)
      obtain ⟨-, hre2⟩ := ctanCl_abs_re_bounds τ hτcl
      have hre : |((τ : ℂ).re)| ≤ 5 / 8 := by
        rw [UpperHalfPlane.coe_re]; exact hre2
      have him : |((τ : ℂ).im)| ≤ 5 / 8 := by
        rw [UpperHalfPlane.coe_im, abs_of_pos τ.im_pos]; exact him2
      linarith [h, hre, him]
    have hs : Work.Kernels.scale τ ≤ 17 / 4 := by
      rw [Work.Kernels.scale]
      linarith [hinv, hnorm]
    rcases le_or_gt 0 Nhp with hNhp | hNhp
    · exact le_trans (Real.rpow_le_rpow (le_trans zero_le_one (Work.Kernels.one_le_scale τ)) hs hNhp)
        (le_max_left _ _)
    · refine le_trans (Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ) < 1)
        (Work.Kernels.one_le_scale τ) hNhp.le) ?_
      rw [Real.one_rpow]; exact le_max_right _ _
  refine ⟨chp * Scale + c * Ktot, by positivity, fun τ r hτ => ?_⟩
  have hτcl : τ ∈ ctanCl := ctanRegion_subset_ctanCl hτ
  -- smoothness of the two summands of the body
  have hcd0 : ContDiffOn ℝ (l : ℕ∞ω) (tangPhi ℓ d τ) (Set.Ici (0 : ℝ)) :=
    (contDiffOn_tangPhi l ℓ d hd τ hτ).mono
      (by intro x hx
          rw [Set.mem_Ici] at hx
          exact Set.mem_Ioi.mpr (by linarith))
  have hFdiff : ContDiffOn ℝ (l : ℕ∞ω) (tangPhi ℓ d τ) (Set.Ioi (-1)) :=
    contDiffOn_tangPhi l ℓ d hd τ hτ
  set Fs : ℝ → ℂ := fun s => sinSq s * tangPhi ℓ d τ (s ^ 2) with hFs
  have h2s : ContDiffOn ℝ (l : ℕ∞ω) (fun s : ℝ => tangPhi ℓ d τ (s ^ 2)) Set.univ := by
    have h := hcd0.comp_contDiff (n := (l : ℕ∞ω)) (f := fun r : ℝ => r ^ 2) (by fun_prop)
      (fun r => sq_nonneg r)
    simpa [Function.comp_def] using h.contDiffOn
  have hAcc : ContDiffAt ℝ (l : ℕ∞) Fs r := by
    have h1 : ContDiff ℝ (l : ℕ∞ω) (fun s : ℝ => sinSq s) := contDiff_omega_sinSq.of_le le_top
    have hcd : ContDiffOn ℝ (l : ℕ∞ω) Fs Set.univ := by
      rw [hFs]
      exact h1.contDiffOn.mul h2s
    exact hcd.contDiffAt (by simp)
  have hBc : ContDiffAt ℝ (l : ℕ∞) (fun s : ℝ => highPart (Gcusp ℓ d) τ s) r :=
    ((contDiff_omega_highPart (Gcusp ℓ d) τ).contDiffAt).of_le le_top
  have hbodyeq : iteratedDeriv l (tangBody ℓ d τ) r
      = iteratedDeriv l Fs r + iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) τ s) r := by
    have hfe : tangBody ℓ d τ = Fs + fun s : ℝ => highPart (Gcusp ℓ d) τ s := by
      funext s
      show sinSq s * tangPhi ℓ d τ (s ^ 2) + highPart (Gcusp ℓ d) τ s
        = Fs s + (fun s : ℝ => highPart (Gcusp ℓ d) τ s) s
      rw [hFs]
    rw [hfe]
    exact iteratedDeriv_add hAcc hBc
  have hcompFs : ∀ s : ℝ, (|s| ^ k) * ‖iteratedDeriv l Fs s‖ ≤ c * Ktot := by
    intro s
    have h := hcomp (tangPhi ℓ d τ) Ktot hKtot0 hFdiff
      (fun m hm x hx => hKtotb m hm τ hτ x hx) s
    have hfun : (fun y : ℝ => (2 - 2 * Real.cos (Real.pi * y ^ 2) : ℂ) * tangPhi ℓ d τ (y ^ 2))
        = Fs := by
      funext y
      show (2 - 2 * Real.cos (Real.pi * y ^ 2) : ℂ) * tangPhi ℓ d τ (y ^ 2)
        = sinSq y * tangPhi ℓ d τ (y ^ 2)
      rw [sinSq_eq_two_sub_two_cos y]
      push_cast
      ring
    rwa [hfun] at h
  rcases eq_or_ne r 0 with hr0 | hr0
  · subst hr0
    rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl
      have hz : tangLayer ℓ d τ 0 = 0 := by rw [tangLayer]; simp
      rw [iteratedDeriv_zero, hz, norm_zero, mul_zero]
      positivity
    · have hfun : (fun s : ℝ => tangLayer ℓ d τ s)
          = fun s : ℝ => if s = 0 then 0 else tangBody ℓ d τ s := by
        funext s
        rw [tangLayer]
        by_cases hs : s = 0
        · rw [if_pos hs, if_pos hs]
        · rw [if_neg hs, if_neg hs]
          rfl
      rw [hfun, punctured_iteratedDeriv (tangBody_neg ℓ d τ)
        (differentiable_tangBody ℓ d hd τ hτ) l hl, hbodyeq]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · rw [hk, pow_zero, one_mul]
        have hB := hhpb τ 0 hτ.1
        simp only [hk, abs_zero, pow_zero, one_mul] at hB
        have hB' : ‖iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) τ s) 0‖ ≤ chp * Scale :=
          le_trans hB (mul_le_mul_of_nonneg_left (hscale τ hτ) hchp)
        have hA' : ‖iteratedDeriv l Fs 0‖ ≤ c * Ktot := by
          simpa [hk] using hcompFs 0
        calc ‖iteratedDeriv l Fs 0
              + iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) τ s) 0‖
            ≤ ‖iteratedDeriv l Fs 0‖
              + ‖iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) τ s) 0‖ := norm_add_le _ _
          _ ≤ c * Ktot + chp * Scale := add_le_add hA' hB'
          _ = chp * Scale + c * Ktot := by ring
      · rw [abs_zero, zero_pow hk.ne', zero_mul]
        positivity
  · have hev : (fun s : ℝ => tangLayer ℓ d τ s) =ᶠ[𝓝 r] (fun s : ℝ => tangBody ℓ d τ s) := by
      filter_upwards [isOpen_ne.mem_nhds hr0] with s hs
      rw [tangLayer, if_neg hs]
      rfl
    have hA := hcompFs r
    have hB := hhpb τ r hτ.1
    calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => tangLayer ℓ d τ s) r‖
        = (|r| ^ k) * ‖iteratedDeriv l (tangBody ℓ d τ) r‖ := by
          rw [iteratedDeriv_congr_of_eventuallyEq hev l]
      _ = (|r| ^ k) * ‖iteratedDeriv l Fs r
            + iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) τ s) r‖ := by rw [hbodyeq]
      _ ≤ (|r| ^ k) * (‖iteratedDeriv l Fs r‖
            + ‖iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) τ s) r‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ = (|r| ^ k) * ‖iteratedDeriv l Fs r‖
            + (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => highPart (Gcusp ℓ d) τ s) r‖ := by ring
      _ ≤ c * Ktot + chp * Scale :=
          add_le_add hA (le_trans hB (mul_le_mul_of_nonneg_left (hscale τ hτ) hchp))
      _ = chp * Scale + c * Ktot := by ring

end Work.HFN.HalfFunnel
