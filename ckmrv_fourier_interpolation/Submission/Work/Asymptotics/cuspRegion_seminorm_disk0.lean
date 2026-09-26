/-
# The `r`-seminorm bound on the cusp-`0` disk `E = {w ∈ 𝒟 : 2 ≤ Im (S • w)}`

This is exactly the CKMRV (Ann. of Math. 196 (2022)) moderate-growth assertion for the `r`-seminorms
of the naive contour transform `Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d)` at the cusp
`0` of the `Γ(2)`-fundamental domain `𝒟`.  It is literally `Work.Asymptotics.SeminormK_E ℓ d`.

## The route used here

The split of the contour integral is taken at the `w`-dependent threshold
`T w = Im (S • w) + 1 = Work.Asymptotics.E_T w`, where

* the *window* `1 ≤ t ≤ T w` is controlled by the plain polynomial window
  `Work.Asymptotics.EpolyWindowE_clean_far` (`0 < t ≤ scale w`, and `E_T w ≤ scale w`);
* the *tail* `t ≥ T w` is controlled by the sharp deviation `Work.Asymptotics.E_deviation_sharp`
  (rate `e^{-π (t - Im (S • w))}`, i.e. `e^{-π(t - E_T w)}` up to `e^{-π}`).

The layer is `layerLow + E_WinT + E_DevT + E_TailClosed (Gcusp ℓ d) (E_T w)` — the workspace's
`Work.Asymptotics.E_ExprT` — and the seminorm bounds of its four pieces are
`Work.Asymptotics.E_layerLow_seminorm`, `Work.Asymptotics.SKEC.E_WinT_seminorm`,
`Work.Asymptotics.E_DevT_seminorm` (proved here) and
`Work.Asymptotics.SKEC.E_TailClosed_seminorm_T`.  The transfer to the naive contour integral is
`Work.Asymptotics.E_kernelTransform_seminorm_of_layer0`.
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.EBase
import Submission.Work.Asymptotics.E_seminorm
import Submission.Work.Asymptotics.Epoint_Kfun
import Submission.Work.Asymptotics.E_deviation_sharp
import Submission.Work.Asymptotics.E_TailClosed
import Submission.Work.Asymptotics.E_TailClosed_seminorm
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.GcuspInP
import Submission.Work.Asymptotics.paperLayer_smooth
import Submission.Work.Asymptotics.SKEC.Defs
import Submission.Work.Asymptotics.SKEC.E_WinT_seminorm
import Submission.Work.Asymptotics.SKEC.E_TailClosed_seminorm_T
import Submission.Work.Asymptotics.SKEC.FarWindowClean
import Submission.Work.Asymptotics.EWindow_far
import Submission.Work.Kernels.All

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane ContDiff Topology

namespace Work.Asymptotics

open Work.Kernels

/-! ## Elementary helpers -/

/-- `(1 + u)^r ≤ 2^r (1 + u^r)` for `u ≥ 0`, `r ≥ 0`. -/
private lemma one_add_rpow_le (r u : ℝ) (hr : 0 ≤ r) (hu : 0 ≤ u) :
    (1 + u) ^ r ≤ 2 ^ r * (1 + u ^ r) := by
  rcases le_or_gt u 1 with h | h
  · have h1 : (1 + u) ^ r ≤ 2 ^ r := Real.rpow_le_rpow (by linarith) (by linarith) hr
    have h2 : (1 : ℝ) ≤ 1 + u ^ r := by
      have := Real.rpow_nonneg hu r; linarith
    have h3 : (0 : ℝ) ≤ 2 ^ r := Real.rpow_nonneg (by norm_num) r
    calc (1 + u) ^ r ≤ 2 ^ r := h1
      _ = 2 ^ r * 1 := by ring
      _ ≤ 2 ^ r * (1 + u ^ r) := mul_le_mul_of_nonneg_left h2 h3
  · have h1 : (1 + u) ^ r ≤ (2 * u) ^ r := Real.rpow_le_rpow (by linarith) (by linarith) hr
    have h2 : (2 * u) ^ r = 2 ^ r * u ^ r := Real.mul_rpow (by norm_num) hu
    have h3 : 2 ^ r * u ^ r ≤ 2 ^ r * (1 + u ^ r) :=
      mul_le_mul_of_nonneg_left (by have := Real.rpow_nonneg hu r; linarith)
        (Real.rpow_nonneg (by norm_num) r)
    linarith [h1, h2, h3]

/-- `u ↦ (1 + u)^r e^{-cu}` is integrable on `(0,∞)` for `r ≥ 0`, `c > 0`. -/
private lemma integrableOn_one_add_rpow_mul_exp_neg (r : ℝ) (hr : 0 ≤ r) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => (1 + u) ^ r * Real.exp (-(c * u))) (Set.Ioi 0) := by
  have hbase : IntegrableOn (fun u : ℝ => u ^ r * Real.exp (-(c * u))) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := r) (b := c)
      (by linarith) one_pos hc
    simpa only [Real.rpow_one, neg_mul] using h
  have hexp : IntegrableOn (fun u : ℝ => Real.exp (-(c * u))) (Set.Ioi 0) := by
    have h := integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0
    simpa only [neg_mul] using h
  have hdom : Integrable (fun u : ℝ => 2 ^ r * (1 + u ^ r) * Real.exp (-(c * u)))
      (volume.restrict (Set.Ioi 0)) := by
    have hsum : Integrable (fun u : ℝ => (1 : ℝ) * Real.exp (-(c * u))
        + u ^ r * Real.exp (-(c * u))) (volume.restrict (Set.Ioi 0)) :=
      (hexp.const_mul (1 : ℝ)).add hbase
    have h2 := hsum.const_mul (2 ^ r)
    refine h2.congr ?_
    filter_upwards with u
    ring
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · exact (by fun_prop : Continuous fun u : ℝ =>
      (1 + u) ^ r * Real.exp (-(c * u))).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := le_of_lt hu
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) r) (Real.exp_nonneg _))]
    have h := one_add_rpow_le r u hr hu0
    have h2 : (0 : ℝ) ≤ 2 ^ r * (1 + u ^ r) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) r) (by have := Real.rpow_nonneg hu0 r; linarith)
    calc (1 + u) ^ r * Real.exp (-(c * u))
        ≤ (2 ^ r * (1 + u ^ r)) * Real.exp (-(c * u)) :=
          mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)
      _ = 2 ^ r * (1 + u ^ r) * Real.exp (-(c * u)) := by ring

/-- **Substitution for `∫_{Ici a}`**: if `f` vanishes strictly below `b ≥ a`, then
`∫_{t ≥ a} f t = ∫_{t ≥ b} f t`. -/
private lemma setIntegral_Ici_eq_of_eq_zero_below {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ t : ℝ, t < b → f t = 0) :
    ∫ t in Set.Ici a, f t = ∫ t in Set.Ici b, f t := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ici,
    ← MeasureTheory.integral_indicator measurableSet_Ici]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  show (Set.Ici a).indicator f t = (Set.Ici b).indicator f t
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases ht : t ∈ Set.Ici b
  · have h1 : t ∈ Set.Ici a := Set.mem_Ici.mpr (le_trans hab (Set.mem_Ici.mp ht))
    rw [if_pos h1, if_pos ht]
  · have hlt : t < b := not_le.mp (by simpa [Set.mem_Ici] using ht)
    rw [h t hlt]
    by_cases h1 : t ∈ Set.Ici a
    · rw [if_pos h1, if_neg ht]
    · rw [if_neg h1, if_neg ht]

/-- **Substitution for `∫_{Ioi a}`**: `∫_{t > a} f t = ∫_{u > 0} f (u + a)`. -/
private lemma setIntegral_Ioi_add_eq (f : ℝ → ℝ) (a : ℝ) :
    ∫ t in Set.Ioi a, f t = ∫ u in Set.Ioi 0, f (u + a) := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← MeasureTheory.integral_add_right_eq_self
      ((Set.Ioi 0).indicator (fun u => f (u + a))) (-a)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  show (Set.Ioi a).indicator f x = (Set.Ioi 0).indicator (fun u => f (u + a)) (x + -a)
  have hx : (x + -a ∈ Set.Ioi 0) ↔ x ∈ Set.Ioi a := by
    simp only [Set.mem_Ioi]; constructor <;> intro h <;> linarith
  by_cases h : x ∈ Set.Ioi a
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hx.mpr h)]
    congr 1
    ring
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h (hx.mp hc))]

/-- `∫_{t ≥ a} (Ioc a b).indicator F t = ∫_{t ∈ (a,b]} F t`. -/
private lemma setIntegral_Ici_indicator_Ioc_eq (F : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Set.Ici a, (Set.Ioc a b).indicator F t = ∫ t in Set.Ioc a b, F t := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ici,
    ← MeasureTheory.integral_indicator measurableSet_Ioc]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  show (Set.Ici a).indicator ((Set.Ioc a b).indicator F) t = (Set.Ioc a b).indicator F t
  rw [Set.indicator_apply]
  by_cases ht : t ∈ Set.Ici a
  · rw [if_pos ht]
  · rw [if_neg ht]
    exact (Set.indicator_of_notMem (fun hc => ht (Set.mem_Ici.mpr hc.1.le)) F).symm

/-! ## Analyticity in `r` of the window and deviation pieces -/

/-- **Analyticity of the window piece `E_WinT`** — an integral over the compact interval `[1,T w]`
with a bounded amplitude, so it is an entire function of `r²`. -/
theorem E_contDiff_omega_E_WinT (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (C N M : ℝ) (hC : 0 < C) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hwin : ∀ (w : ℍ) (t : ℝ), w ∈ KEpsilon → 1 ≤ t → t ≤ E_T w →
      ‖Kaxis (Kfun ℓ d) w t‖ ≤ C * (scale w) ^ N * (1 + t) ^ M)
    {w : ℍ} (hw : w ∈ KEpsilon) :
    ContDiff ℝ ω (fun s : ℝ => E_WinT ℓ d w s) := by
  have hT1 : (1 : ℝ) ≤ E_T w := one_le_E_T hw
  have hspos : 0 < scale w := scale_pos w
  have hmeasK : Measurable (fun t : ℝ => Kaxis (Kfun ℓ d) w t) :=
    measurable_Kaxis_of_measurable (Kfun ℓ d) w (measurable_Kfun_snd_all ℓ d hd w)
  set ψ : ℝ → ℂ := (Set.Ioc (1 : ℝ) (E_T w)).indicator
    (fun t => Kaxis (Kfun ℓ d) w t) with hψ
  have hB0 : 0 ≤ C * (scale w) ^ N * (1 + E_T w) ^ M :=
    mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hspos.le N))
      (Real.rpow_nonneg (by linarith) M)
  have hCpos : 0 < max (C * (scale w) ^ N * (1 + E_T w) ^ M * Real.exp (Real.pi * E_T w)) 1 :=
    lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hψmeas : AEStronglyMeasurable ψ (volume.restrict (Set.Ici (1 : ℝ))) := by
    rw [hψ]
    exact ((hmeasK.indicator measurableSet_Ioc)).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ici (1 : ℝ))),
      ‖ψ t‖ ≤ max (C * (scale w) ^ N * (1 + E_T w) ^ M * Real.exp (Real.pi * E_T w)) 1
        * t ^ (0 : ℝ) * Real.exp (-(Real.pi * t)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
    have ht1 : (1 : ℝ) ≤ t := Set.mem_Ici.mp ht
    rw [Real.rpow_zero, mul_one]
    by_cases hmem : t ∈ Set.Ioc (1 : ℝ) (E_T w)
    · rw [hψ, Set.indicator_of_mem hmem]
      refine le_trans (hwin w t hw hmem.1.le hmem.2) ?_
      have h1 : (1 : ℝ) ≤ Real.exp (Real.pi * E_T w) * Real.exp (-(Real.pi * t)) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by nlinarith [Real.pi_pos, hmem.2])
      calc C * (scale w) ^ N * (1 + t) ^ M
          ≤ C * (scale w) ^ N * (1 + E_T w) ^ M := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC.le (Real.rpow_nonneg hspos.le N))
            exact Real.rpow_le_rpow (by linarith [ht1]) (by linarith [hmem.2]) hM
        _ = C * (scale w) ^ N * (1 + E_T w) ^ M * 1 := by ring
        _ ≤ C * (scale w) ^ N * (1 + E_T w) ^ M
              * (Real.exp (Real.pi * E_T w) * Real.exp (-(Real.pi * t))) :=
            mul_le_mul_of_nonneg_left h1 hB0
        _ ≤ max (C * (scale w) ^ N * (1 + E_T w) ^ M * Real.exp (Real.pi * E_T w)) 1
              * Real.exp (-(Real.pi * t)) := by
            have h2 : C * (scale w) ^ N * (1 + E_T w) ^ M
                * (Real.exp (Real.pi * E_T w) * Real.exp (-(Real.pi * t)))
                = (C * (scale w) ^ N * (1 + E_T w) ^ M * Real.exp (Real.pi * E_T w))
                  * Real.exp (-(Real.pi * t)) := by ring
            rw [h2]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
    · rw [hψ, Set.indicator_of_notMem hmem]
      simp only [norm_zero]
      exact mul_nonneg (le_trans (by norm_num) (le_max_right _ _)) (Real.exp_nonneg _)
  have hcd : ContDiff ℝ ω (fun r : ℝ => ∫ t in Set.Ici (1 : ℝ),
      ψ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) :=
    contDiff_omega_integral_Ici_exp hCpos le_rfl hψmeas hbound
  have hfun : (fun s : ℝ => E_WinT ℓ d w s)
      = fun s : ℝ => sinSq s * ∫ t in Set.Ici (1 : ℝ),
          ψ t * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ))) := by
    funext s
    rw [E_WinT, intervalIntegral.integral_of_le hT1]
    congr 1
    have hpt : ∀ t : ℝ, ψ t * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))
        = (Set.Ioc (1 : ℝ) (E_T w)).indicator
            (fun t => Kaxis (Kfun ℓ d) w t * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) t := by
      intro t
      rw [hψ, Set.indicator_apply, Set.indicator_apply]
      by_cases h : t ∈ Set.Ioc (1 : ℝ) (E_T w) <;> simp [h]
    have key : (∫ t in Set.Ici (1 : ℝ), ψ t * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ))))
        = ∫ t in Set.Ioc (1 : ℝ) (E_T w),
            Kaxis (Kfun ℓ d) w t * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ))) := by
      rw [show (∫ t in Set.Ici (1 : ℝ),
            ψ t * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ))))
          = ∫ t in Set.Ici (1 : ℝ), (Set.Ioc (1 : ℝ) (E_T w)).indicator
              (fun t => Kaxis (Kfun ℓ d) w t
                * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))) t
          from MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun t _ => hpt t)]
      exact setIntegral_Ici_indicator_Ioc_eq _ hT1
    exact key.symm
  rw [hfun]
  exact contDiff_omega_sinSq.mul hcd

/-- **Analyticity of the deviation piece `E_DevT`** — the tail integral of an exponentially small
amplitude. -/
theorem E_contDiff_omega_E_DevT (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (C N M : ℝ) (hC : 0 < C) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (htail : ∀ (w : ℍ) (t : ℝ), w ∈ KEpsilon → E_T w ≤ t →
      ‖Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖
        ≤ C * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * (t - E_T w))))
    {w : ℍ} (hw : w ∈ KEpsilon) :
    ContDiff ℝ ω (fun s : ℝ => E_DevT ℓ d w s) := by
  have hT1 : (1 : ℝ) ≤ E_T w := one_le_E_T hw
  have hmeasK : Measurable (fun t : ℝ => Kaxis (Kfun ℓ d) w t) :=
    measurable_Kaxis_of_measurable (Kfun ℓ d) w (measurable_Kfun_snd_all ℓ d hd w)
  have hmeasA : Measurable (fun t : ℝ => Aexp (Gcusp ℓ d) w t) := by unfold Aexp; fun_prop
  have hspos : 0 < scale w := scale_pos w
  set g : ℝ → ℂ := fun t => if t < E_T w then 0
    else Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t with hg
  have hCg0 : 0 < C * (scale w) ^ N * Real.exp (Real.pi * E_T w) * 2 ^ M := by positivity
  have hglob : ∀ᵐ t ∂(volume.restrict (Set.Ici (1 : ℝ))), ‖g t‖
      ≤ (C * (scale w) ^ N * Real.exp (Real.pi * E_T w) * 2 ^ M) * t ^ M
        * Real.exp (-(Real.pi * t)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
    have ht1 : (1 : ℝ) ≤ t := Set.mem_Ici.mp ht
    have hgte : g t = if t < E_T w then 0 else Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t := rfl
    rw [hgte]
    rcases lt_or_ge t (E_T w) with hlt | hge
    · rw [if_pos hlt]
      simp only [norm_zero]
      exact mul_nonneg (mul_nonneg (by positivity)
        (Real.rpow_nonneg (by linarith [ht1] : (0 : ℝ) ≤ t) M)) (Real.exp_nonneg _)
    · rw [if_neg (not_lt.mpr hge)]
      have hb := htail w t hw hge
      have h1 : Real.exp (-(Real.pi * (t - E_T w)))
          = Real.exp (Real.pi * E_T w) * Real.exp (-(Real.pi * t)) := by
        rw [← Real.exp_add]; congr 1; ring
      have h2 : (1 + t) ^ M ≤ (2 * t) ^ M := Real.rpow_le_rpow (by linarith) (by linarith) hM
      have h3 : (2 * t) ^ M = 2 ^ M * t ^ M := Real.mul_rpow (by norm_num) (by linarith)
      have hb' := htail w t hw hge
      calc ‖Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖
          ≤ C * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * (t - E_T w))) := hb'
        _ = C * (scale w) ^ N * (1 + t) ^ M
              * (Real.exp (Real.pi * E_T w) * Real.exp (-(Real.pi * t))) := by rw [h1]
        _ ≤ C * (scale w) ^ N * (2 ^ M * t ^ M)
              * (Real.exp (Real.pi * E_T w) * Real.exp (-(Real.pi * t))) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
              (by positivity)
            rw [← h3]; exact h2
        _ = (C * (scale w) ^ N * Real.exp (Real.pi * E_T w) * 2 ^ M) * t ^ M
              * Real.exp (-(Real.pi * t)) := by ring
  have hmeasg : AEStronglyMeasurable g (volume.restrict (Set.Ici (1 : ℝ))) := by
    rw [hg]
    exact (Measurable.ite measurableSet_Iio measurable_const
      (hmeasK.sub hmeasA)).aestronglyMeasurable
  have hcd : ContDiff ℝ ω (fun r : ℝ => ∫ t in Set.Ici (1 : ℝ),
      g t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) :=
    contDiff_omega_integral_Ici_exp hCg0 hM hmeasg hglob
  have hfun : (fun s : ℝ => E_DevT ℓ d w s)
      = fun s : ℝ => sinSq s * ∫ t in Set.Ici (1 : ℝ),
          g t * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ))) := by
    funext s
    rw [E_DevT, tailIntegral]
    congr 1
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun t _ => ?_)
    show g t * (Real.exp (-(Real.pi * s ^ 2 * t)) : ℂ)
        = g t * Complex.exp (-(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)))
    rw [show -(Real.pi * (s : ℂ) ^ 2 * (t : ℂ)) = ((-(Real.pi * s ^ 2 * t) : ℝ) : ℂ) by
      push_cast; ring, ← Complex.ofReal_exp]
  rw [hfun]
  exact contDiff_omega_sinSq.mul hcd


/-- `∫_{x ∈ s} c * f x = c * ∫_{x ∈ s} f x` for a measurable `s`. -/
private lemma setIntegral_const_mul' {s : Set ℝ} (hs : MeasurableSet s) (c : ℝ) (f : ℝ → ℝ) :
    ∫ x in s, c * f x = c * ∫ x in s, f x := by
  classical
  rw [← MeasureTheory.integral_indicator hs, ← MeasureTheory.integral_indicator hs]
  rw [show (fun x => s.indicator (fun x => c * f x) x) = fun x => c * s.indicator f x from by
    funext x
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : x ∈ s <;> simp [h]]
  rw [MeasureTheory.integral_const_mul]

/-- **The `r`-seminorm bound for the deviation piece `E_DevT`.**

The amplitude `g w t = [t < E_T w] · (K(w,it) - Aexp(Gcusp ℓ d)(w,t))` is supported on
`[E_T w, ∞)` and decays there like `e^{-π(t - E_T w)}`; its tail integral therefore satisfies
`‖∂^m (tailIntegral g) x‖ ≤ C (scale w)^N π^l (1 + E_T w)^{M+l} D e^{-πx}` with
`D = ∫_{u>0} (1+u)^{M+l} e^{-πu} du`, which gives the bound for
`E_DevT = sinSq r · tailIntegral g (r²)` through
`Work.Asymptotics.exists_seminorm_bound_of_iteratedDeriv_bound`. -/
theorem E_DevT_seminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (C N M : ℝ) (hC : 0 < C) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (htail : ∀ (w : ℍ) (t : ℝ), w ∈ KEpsilon → E_T w ≤ t →
      ‖Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖
        ≤ C * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * (t - E_T w)))) :
    ∀ k l : ℕ, ∃ c N' : ℝ, 0 ≤ c ∧ 0 ≤ N' ∧
      ∀ (w : ℍ), w ∈ KEpsilon → ∀ r : ℝ,
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => E_DevT ℓ d w s) r‖
          ≤ c * (scale w) ^ N' := by
  intro k l
  obtain ⟨c₀, hc₀, hbound⟩ := exists_seminorm_bound_of_iteratedDeriv_bound k l
  set D : ℝ := ∫ u in Set.Ioi (0 : ℝ),
    (1 + u) ^ (M + (l : ℝ)) * Real.exp (-(Real.pi * u)) with hD
  have hDrpow : (fun u : ℝ => (1 + u) ^ (M + (l : ℝ)) * Real.exp (-(Real.pi * u)))
      = fun u : ℝ => (1 + u) ^ (M + (l : ℝ)) * Real.exp (-(Real.pi * u)) := rfl
  have hDint : IntegrableOn (fun u : ℝ =>
      (1 + u) ^ (M + (l : ℝ)) * Real.exp (-(Real.pi * u))) (Set.Ioi 0) :=
    integrableOn_one_add_rpow_mul_exp_neg _ (by positivity) Real.pi_pos
  have hD0 : 0 ≤ D := by
    rw [hD]
    exact setIntegral_nonneg measurableSet_Ioi
      (fun u hu => mul_nonneg
        (Real.rpow_nonneg (by have := Set.mem_Ioi.mp hu; linarith : (0 : ℝ) ≤ 1 + u) _)
        (Real.exp_nonneg _))
  refine ⟨c₀ * (C * Real.pi ^ l * 2 ^ (M + (l : ℝ)) * D), N + M + l,
    by positivity, by positivity, ?_⟩
  intro w hw r
  have hT1 : (1 : ℝ) ≤ E_T w := one_le_E_T hw
  have hTle : E_T w ≤ scale w := E_T_le_scale hw
  have hspos : 0 < scale w := scale_pos w
  have hmeasK : Measurable (fun t : ℝ => Kaxis (Kfun ℓ d) w t) :=
    measurable_Kaxis_of_measurable (Kfun ℓ d) w (measurable_Kfun_snd_all ℓ d hd w)
  have hmeasA : Measurable (fun t : ℝ => Aexp (Gcusp ℓ d) w t) := by unfold Aexp; fun_prop
  set g : ℝ → ℂ := fun t => if t < E_T w then 0
    else Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t with hg
  have hg_apply : ∀ t : ℝ, g t = if t < E_T w then 0
      else Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t := fun t => rfl
  have hg0 : ∀ t : ℝ, t < E_T w → g t = 0 := fun t ht => by rw [hg_apply t, if_pos ht]
  have hgm : ∀ t : ℝ, E_T w ≤ t →
      ‖g t‖ ≤ C * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * (t - E_T w))) :=
    fun t ht => by rw [hg_apply t, if_neg (not_lt.mpr ht)]; exact htail w t hw ht
  have hCg0 : 0 < C * (scale w) ^ N * Real.exp (Real.pi * E_T w) * 2 ^ M := by positivity
  have hglob : ∀ᵐ t ∂(volume.restrict (Set.Ici (1 : ℝ))), ‖g t‖
      ≤ (C * (scale w) ^ N * Real.exp (Real.pi * E_T w) * 2 ^ M) * t ^ M
        * Real.exp (-(Real.pi * t)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
    have ht1 : (1 : ℝ) ≤ t := Set.mem_Ici.mp ht
    rw [hg_apply t]
    rcases lt_or_ge t (E_T w) with hlt | hge
    · rw [if_pos hlt]
      simp only [norm_zero]
      exact mul_nonneg (mul_nonneg (by positivity)
        (Real.rpow_nonneg (by linarith [ht1] : (0 : ℝ) ≤ t) M)) (Real.exp_nonneg _)
    · rw [if_neg (not_lt.mpr hge)]
      have hb := htail w t hw hge
      have h1 : Real.exp (-(Real.pi * (t - E_T w)))
          = Real.exp (Real.pi * E_T w) * Real.exp (-(Real.pi * t)) := by
        rw [← Real.exp_add]; congr 1; ring
      have h2 : (1 + t) ^ M ≤ (2 * t) ^ M := Real.rpow_le_rpow (by linarith) (by linarith) hM
      have h3 : (2 * t) ^ M = 2 ^ M * t ^ M := Real.mul_rpow (by norm_num) (by linarith)
      calc ‖Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖
          ≤ C * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * (t - E_T w))) := hb
        _ = C * (scale w) ^ N * (1 + t) ^ M
              * (Real.exp (Real.pi * E_T w) * Real.exp (-(Real.pi * t))) := by rw [h1]
        _ ≤ C * (scale w) ^ N * (2 ^ M * t ^ M)
              * (Real.exp (Real.pi * E_T w) * Real.exp (-(Real.pi * t))) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
              (by positivity)
            rw [← h3]; exact h2
        _ = (C * (scale w) ^ N * Real.exp (Real.pi * E_T w) * 2 ^ M) * t ^ M
              * Real.exp (-(Real.pi * t)) := by ring
  have hmeasg : AEStronglyMeasurable g (volume.restrict (Set.Ici (1 : ℝ))) := by
    rw [hg]
    exact (Measurable.ite measurableSet_Iio measurable_const
      (hmeasK.sub hmeasA)).aestronglyMeasurable
  have hcont : ContDiffOn ℝ ((l : ℕ∞ω)) (tailIntegral g) (Set.Ioi (-1)) :=
    tailIntegral_contDiffOn l g hmeasg hCg0.le hM hglob
  -- the key pointwise bound on the iterated derivatives of the tail integral
  have hderiv : ∀ m : ℕ, m ≤ l → ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv m (tailIntegral g) x‖
        ≤ (C * (scale w) ^ N * Real.pi ^ l * (1 + E_T w) ^ (M + (l : ℝ)) * D)
            * Real.exp (-(Real.pi * x)) := by
    intro m hm x hx
    rw [tailIntegral_iteratedDeriv g hmeasg hCg0.le hM hglob m x (by linarith)]
    set φ : ℝ → ℂ := fun t => (g t * (((-(Real.pi * t)) : ℝ) : ℂ) ^ m)
      * (Real.exp (-(Real.pi * x * t)) : ℂ) with hφ
    have hφ_apply : ∀ t : ℝ, φ t = (g t * (((-(Real.pi * t)) : ℝ) : ℂ) ^ m)
        * (Real.exp (-(Real.pi * x * t)) : ℂ) := fun t => rfl
    change ‖∫ t in Set.Ici (1 : ℝ), φ t‖
        ≤ (C * (scale w) ^ N * Real.pi ^ l * (1 + E_T w) ^ (M + (l : ℝ)) * D)
            * Real.exp (-(Real.pi * x))
    -- Step A: the integral over `Ici 1` is the integral over `Ici (E_T w)`
    have hz : ∫ t in Set.Ici (1 : ℝ), φ t = ∫ t in Set.Ici (E_T w), φ t := by
      refine setIntegral_Ici_eq_of_eq_zero_below hT1 (fun t ht => ?_)
      show φ t = 0
      rw [hφ_apply t, hg0 t ht]; ring
    rw [hz]
    -- Step B: bound the norm of the set integral by the integral of the norm
    have hle1 : ‖∫ t in Set.Ici (E_T w), φ t‖ ≤ ∫ t in Set.Ici (E_T w), ‖φ t‖ := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ici,
        ← MeasureTheory.integral_indicator measurableSet_Ici]
      rw [show (∫ t, (Set.Ici (E_T w)).indicator (fun t => ‖φ t‖) t)
            = ∫ t, ‖(Set.Ici (E_T w)).indicator φ t‖ from by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
        show (Set.Ici (E_T w)).indicator (fun t => ‖φ t‖) t
            = ‖(Set.Ici (E_T w)).indicator φ t‖
        by_cases h : t ∈ Set.Ici (E_T w)
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; simp]
      exact MeasureTheory.norm_integral_le_integral_norm _
    -- the pointwise comparison function
    set Ψ : ℝ → ℝ := fun t => C * (scale w) ^ N * Real.pi ^ m
      * (1 + t) ^ (M + (l : ℝ)) * Real.exp (-(Real.pi * (t - E_T w)))
      * Real.exp (-(Real.pi * x * t)) with hΨ
    have hΨ_apply : ∀ t : ℝ, Ψ t = C * (scale w) ^ N * Real.pi ^ m
        * (1 + t) ^ (M + (l : ℝ)) * Real.exp (-(Real.pi * (t - E_T w)))
        * Real.exp (-(Real.pi * x * t)) := fun t => rfl
    have hΨ_nn : ∀ t : ℝ, 0 ≤ t → 0 ≤ Ψ t := fun t ht => by
      rw [hΨ_apply t]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le
        (Real.rpow_nonneg hspos.le N)) (pow_nonneg Real.pi_pos.le m))
        (Real.rpow_nonneg (by linarith) _)) (Real.exp_nonneg _)) (Real.exp_nonneg _)
    have hpt : ∀ t ∈ Set.Ici (E_T w), ‖φ t‖ ≤ Ψ t := by
      intro t ht
      have htT : E_T w ≤ t := Set.mem_Ici.mp ht
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (by linarith) htT
      have ht0' : (0 : ℝ) ≤ t := ht0.le
      rw [hφ_apply t, hΨ_apply t]
      rw [show ‖(g t * (((-(Real.pi * t)) : ℝ) : ℂ) ^ m)
              * (Real.exp (-(Real.pi * x * t)) : ℂ)‖
            = ‖g t‖ * ((Real.pi * t) ^ m * Real.exp (-(Real.pi * x * t))) from by
        rw [norm_mul, norm_mul, norm_pow, norm_ofReal_eq_abs,
          abs_of_neg (by nlinarith [Real.pi_pos, ht0]), norm_ofReal_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        ring]
      have hb := hgm t htT
      have hle : (1 + t) ^ M * (Real.pi * t) ^ m
          ≤ (1 + t) ^ (M + (l : ℝ)) * Real.pi ^ m := by
        have hbase : t ^ m ≤ (1 + t) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
        calc (1 + t) ^ M * (Real.pi * t) ^ m
            = Real.pi ^ m * ((1 + t) ^ M * t ^ m) := by rw [mul_pow]; ring
          _ ≤ Real.pi ^ m * ((1 + t) ^ M * (1 + t) ^ m) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbase
                (Real.rpow_nonneg (by linarith) M)) (pow_nonneg Real.pi_pos.le m)
          _ = Real.pi ^ m * (1 + t) ^ (M + (m : ℝ)) := by
              rw [← Real.rpow_natCast (1 + t) m,
                ← Real.rpow_add (by linarith : (0 : ℝ) < 1 + t)]
          _ ≤ Real.pi ^ m * (1 + t) ^ (M + (l : ℝ)) := by
              refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg Real.pi_pos.le m)
              exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by
                have : (m : ℝ) ≤ (l : ℝ) := by exact_mod_cast hm
                linarith)
          _ = (1 + t) ^ (M + (l : ℝ)) * Real.pi ^ m := by ring
      calc ‖g t‖ * ((Real.pi * t) ^ m * Real.exp (-(Real.pi * x * t)))
          ≤ (C * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * (t - E_T w))))
              * ((Real.pi * t) ^ m * Real.exp (-(Real.pi * x * t))) :=
            mul_le_mul_of_nonneg_right hb (mul_nonneg (pow_nonneg (by positivity) m)
              (Real.exp_nonneg _))
        _ = (C * (scale w) ^ N * Real.exp (-(Real.pi * (t - E_T w))))
              * ((1 + t) ^ M * (Real.pi * t) ^ m) * Real.exp (-(Real.pi * x * t)) := by ring
        _ ≤ (C * (scale w) ^ N * Real.exp (-(Real.pi * (t - E_T w))))
              * ((1 + t) ^ (M + (l : ℝ)) * Real.pi ^ m) * Real.exp (-(Real.pi * x * t)) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hle (by positivity)) (Real.exp_nonneg _)
        _ = C * (scale w) ^ N * Real.pi ^ m * (1 + t) ^ (M + (l : ℝ))
              * Real.exp (-(Real.pi * (t - E_T w))) * Real.exp (-(Real.pi * x * t)) := by ring
    -- integrability of the dominating function `Ψ` on `Ici (E_T w)`
    have hΨint : IntegrableOn Ψ (Set.Ici (E_T w)) := by
      have hbase : IntegrableOn (fun t : ℝ => t ^ (M + (l : ℝ)) * Real.exp (-(Real.pi * t)))
          (Set.Ici (E_T w)) :=
        (Work.Asymptotics.integrableOn_rpow_mul_exp_neg (M + (l : ℝ)) Real.pi
          (by positivity) Real.pi_pos).mono_set
          (fun t ht => by simp only [Set.mem_Ici] at ht ⊢; linarith)
      refine MeasureTheory.Integrable.mono'
        (hbase.const_mul (C * (scale w) ^ N * Real.pi ^ m * 2 ^ (M + (l : ℝ))
          * Real.exp (Real.pi * E_T w))) ?_ ?_
      · have hcont : Continuous Ψ := by
          rw [show Ψ = fun t : ℝ => C * (scale w) ^ N * Real.pi ^ m
              * (1 + t) ^ (M + (l : ℝ)) * Real.exp (-(Real.pi * (t - E_T w)))
              * Real.exp (-(Real.pi * x * t)) from funext (fun t => hΨ_apply t)]
          have hpow : Continuous fun t : ℝ => (1 + t) ^ (M + (l : ℝ)) :=
            (continuous_const.add continuous_id).rpow_const
              (fun t => Or.inr (by positivity))
          have he1 : Continuous fun t : ℝ => Real.exp (-(Real.pi * (t - E_T w))) :=
            Real.continuous_exp.comp (by fun_prop)
          have he2 : Continuous fun t : ℝ => Real.exp (-(Real.pi * x * t)) :=
            Real.continuous_exp.comp (by fun_prop)
          exact ((Continuous.mul (Continuous.mul (Continuous.mul (Continuous.mul
            continuous_const continuous_const) continuous_const) hpow) he1).mul he2)
        exact hcont.aestronglyMeasurable
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
        have htT : E_T w ≤ t := Set.mem_Ici.mp ht
        have ht1 : (1 : ℝ) ≤ t := le_trans hT1 htT
        rw [hΨ_apply t, Real.norm_of_nonneg (hΨ_nn t (by linarith))]
        have hpow : (1 + t) ^ (M + (l : ℝ)) ≤ 2 ^ (M + (l : ℝ)) * t ^ (M + (l : ℝ)) := by
          rw [← Real.mul_rpow (by norm_num) (by linarith : (0 : ℝ) ≤ t)]
          exact Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
        have h2 : Real.exp (-(Real.pi * (t - E_T w)))
            ≤ Real.exp (Real.pi * E_T w) * Real.exp (-(Real.pi * t)) := by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (by ring_nf; linarith)
        have h3 : Real.exp (-(Real.pi * x * t)) ≤ 1 := by
          rw [← Real.exp_zero]
          refine Real.exp_le_exp.mpr ?_
          have h0 : (0 : ℝ) ≤ x * t := mul_nonneg hx (by linarith)
          nlinarith [Real.pi_pos, h0]
        calc C * (scale w) ^ N * Real.pi ^ m * (1 + t) ^ (M + (l : ℝ))
              * Real.exp (-(Real.pi * (t - E_T w))) * Real.exp (-(Real.pi * x * t))
            ≤ C * (scale w) ^ N * Real.pi ^ m * (2 ^ (M + (l : ℝ)) * t ^ (M + (l : ℝ)))
              * (Real.exp (Real.pi * E_T w) * Real.exp (-(Real.pi * t))) * 1 := by
              gcongr
          _ = (C * (scale w) ^ N * Real.pi ^ m * 2 ^ (M + (l : ℝ)) * Real.exp (Real.pi * E_T w))
                * (t ^ (M + (l : ℝ)) * Real.exp (-(Real.pi * t))) := by ring
    have hφint : IntegrableOn (fun t => ‖φ t‖) (Set.Ici (E_T w)) := by
      refine MeasureTheory.Integrable.mono' hΨint ?_ ?_
      · have hmg : Measurable g := by
          rw [hg]
          exact Measurable.ite measurableSet_Iio measurable_const (hmeasK.sub hmeasA)
        have hmφ : Measurable φ := by
          rw [hφ]
          exact (hmg.mul ((by fun_prop : Continuous fun t : ℝ =>
            (((-(Real.pi * t)) : ℝ) : ℂ) ^ m).measurable)).mul
            (by fun_prop : Continuous fun t : ℝ =>
              (Real.exp (-(Real.pi * x * t)) : ℂ)).measurable
        exact hmφ.norm.aestronglyMeasurable
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hpt t ht
    have hle2 : ∫ t in Set.Ici (E_T w), ‖φ t‖ ≤ ∫ t in Set.Ici (E_T w), Ψ t :=
      MeasureTheory.setIntegral_mono_on hφint hΨint measurableSet_Ici hpt
    -- the value of `∫ Ψ`
    have hval : ∫ t in Set.Ici (E_T w), Ψ t
        ≤ C * (scale w) ^ N * Real.pi ^ m * (1 + E_T w) ^ (M + (l : ℝ))
            * Real.exp (-(Real.pi * x)) * D := by
      set K0 : ℝ := C * (scale w) ^ N * Real.pi ^ m * (1 + E_T w) ^ (M + (l : ℝ))
        * Real.exp (-(Real.pi * x)) with hK0
      have hK00 : 0 ≤ K0 := by rw [hK0]; positivity
      set f : ℝ → ℝ := fun u =>
        (1 + u) ^ (M + (l : ℝ)) * Real.exp (-(Real.pi * (1 + x) * u)) with hf
      have hf_apply : ∀ u : ℝ, f u = (1 + u) ^ (M + (l : ℝ))
          * Real.exp (-(Real.pi * (1 + x) * u)) := fun u => rfl
      have hsh : ∫ t in Set.Ici (E_T w), Ψ t = ∫ u in Set.Ioi 0, Ψ (u + E_T w) := by
        rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
        exact setIntegral_Ioi_add_eq Ψ (E_T w)
      rw [hsh]
      have hpt2 : ∀ u ∈ Set.Ioi 0, Ψ (u + E_T w) ≤ K0 * f u := by
        intro u hu
        have hu0 : (0 : ℝ) < u := hu
        have hw0 : (0 : ℝ) ≤ E_T w := le_of_lt (E_T_pos hw)
        have hK0def : K0 = C * (scale w) ^ N * Real.pi ^ m * (1 + E_T w) ^ (M + (l : ℝ))
            * Real.exp (-(Real.pi * x)) := hK0
        rw [hΨ_apply (u + E_T w), hK0def, hf_apply u]
        have hbase : (1 + (u + E_T w)) ≤ (1 + E_T w) * (1 + u) := by nlinarith
        have h1 : (1 + (u + E_T w)) ^ (M + (l : ℝ))
            ≤ (1 + E_T w) ^ (M + (l : ℝ)) * (1 + u) ^ (M + (l : ℝ)) := by
          rw [← Real.mul_rpow (by positivity) (by linarith : (0 : ℝ) ≤ 1 + u)]
          exact Real.rpow_le_rpow (by linarith) hbase (by positivity)
        have h2 : Real.exp (-(Real.pi * (u + E_T w - E_T w))) = Real.exp (-(Real.pi * u)) := by
          congr 1; ring
        have h3 : Real.exp (-(Real.pi * x * (u + E_T w)))
            = Real.exp (-(Real.pi * x * E_T w)) * Real.exp (-(Real.pi * x * u)) := by
          rw [← Real.exp_add]; congr 1; ring
        have h4 : Real.exp (-(Real.pi * x * E_T w)) ≤ Real.exp (-(Real.pi * x)) := by
          rw [Real.exp_le_exp]
          have h0 : (0 : ℝ) ≤ Real.pi * x := mul_nonneg Real.pi_pos.le hx
          nlinarith [mul_le_mul_of_nonneg_left hT1 h0]
        rw [h2, h3]
        calc C * (scale w) ^ N * Real.pi ^ m * (1 + (u + E_T w)) ^ (M + (l : ℝ))
              * Real.exp (-(Real.pi * u))
              * (Real.exp (-(Real.pi * x * E_T w)) * Real.exp (-(Real.pi * x * u)))
            ≤ C * (scale w) ^ N * Real.pi ^ m
                * ((1 + E_T w) ^ (M + (l : ℝ)) * (1 + u) ^ (M + (l : ℝ)))
              * Real.exp (-(Real.pi * u))
              * (Real.exp (-(Real.pi * x)) * Real.exp (-(Real.pi * x * u))) := by
              gcongr
          _ = (C * (scale w) ^ N * Real.pi ^ m * (1 + E_T w) ^ (M + (l : ℝ))
                * Real.exp (-(Real.pi * x)))
              * ((1 + u) ^ (M + (l : ℝ)) * Real.exp (-(Real.pi * (1 + x) * u))) := by
              have hsplit : Real.exp (-(Real.pi * (1 + x) * u))
                  = Real.exp (-(Real.pi * u)) * Real.exp (-(Real.pi * x * u)) := by
                rw [← Real.exp_add]; congr 1; ring
              rw [hsplit]; ring
      have hfint : IntegrableOn f (Set.Ioi 0) :=
        integrableOn_one_add_rpow_mul_exp_neg _ (by positivity)
          (by positivity : (0:ℝ) < Real.pi * (1 + x))
      have h1int : IntegrableOn (fun u : ℝ => Ψ (u + E_T w)) (Set.Ioi 0) := by
        refine MeasureTheory.Integrable.mono' (hfint.const_mul K0) ?_ ?_
        · have hcont : Continuous (fun u : ℝ => Ψ (u + E_T w)) := by
            rw [show (fun u : ℝ => Ψ (u + E_T w)) = fun u : ℝ =>
                C * (scale w) ^ N * Real.pi ^ m
                * (1 + (u + E_T w)) ^ (M + (l : ℝ))
                * Real.exp (-(Real.pi * ((u + E_T w) - E_T w)))
                * Real.exp (-(Real.pi * x * (u + E_T w))) from funext (fun u => hΨ_apply _)]
            have hpow : Continuous fun u : ℝ => (1 + (u + E_T w)) ^ (M + (l : ℝ)) :=
              (continuous_const.add (continuous_id.add continuous_const)).rpow_const
                (fun u => Or.inr (by positivity))
            have he1 : Continuous fun u : ℝ =>
                Real.exp (-(Real.pi * ((u + E_T w) - E_T w))) :=
              Real.continuous_exp.comp (by fun_prop)
            have he2 : Continuous fun u : ℝ =>
                Real.exp (-(Real.pi * x * (u + E_T w))) :=
              Real.continuous_exp.comp (by fun_prop)
            exact ((Continuous.mul (Continuous.mul (Continuous.mul (Continuous.mul
              continuous_const continuous_const) continuous_const) hpow) he1).mul he2)
          exact hcont.aestronglyMeasurable
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
          rw [Real.norm_of_nonneg (hΨ_nn _ (by linarith [Set.mem_Ioi.mp hu]))]
          exact hpt2 u hu
      have hstep := MeasureTheory.setIntegral_mono_on h1int (hfint.const_mul K0)
        measurableSet_Ioi hpt2
      rw [setIntegral_const_mul' measurableSet_Ioi K0 f] at hstep
      refine hstep.trans ?_
      have hleD : ∫ u in Set.Ioi (0 : ℝ), f u ≤ D := by
        rw [hD]
        refine MeasureTheory.setIntegral_mono_on hfint hDint measurableSet_Ioi (fun u hu => ?_)
        rw [hf_apply u]
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg
          (by linarith [Set.mem_Ioi.mp hu]) _)
        refine Real.exp_le_exp.mpr ?_
        have h0 : (0 : ℝ) ≤ u := (Set.mem_Ioi.mp hu).le
        have h2 : (0 : ℝ) ≤ Real.pi * x * u := mul_nonneg (mul_nonneg Real.pi_pos.le hx) h0
        rw [show -(Real.pi * (1 + x) * u) = -(Real.pi * u) - Real.pi * x * u from by ring]
        linarith [h2]
      exact mul_le_mul_of_nonneg_left hleD hK00
    refine le_trans hle1 (le_trans hle2 (le_trans hval ?_))
    -- replace `π^m` by `π^l`
    have hpi : Real.pi ^ m ≤ Real.pi ^ l := pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) hm
    calc C * (scale w) ^ N * Real.pi ^ m * (1 + E_T w) ^ (M + (l : ℝ))
            * Real.exp (-(Real.pi * x)) * D
        ≤ C * (scale w) ^ N * Real.pi ^ l * (1 + E_T w) ^ (M + (l : ℝ))
            * Real.exp (-(Real.pi * x)) * D := by
          gcongr
      _ = (C * (scale w) ^ N * Real.pi ^ l * (1 + E_T w) ^ (M + (l : ℝ)) * D)
            * Real.exp (-(Real.pi * x)) := by ring
  -- apply the parametric-differentiation-composition bound
  have hK0 : (0 : ℝ) ≤ C * (scale w) ^ N * Real.pi ^ l * (1 + E_T w) ^ (M + (l : ℝ)) * D := by
    positivity
  have key := hbound (tailIntegral g)
    (C * (scale w) ^ N * Real.pi ^ l * (1 + E_T w) ^ (M + (l : ℝ)) * D) hK0 hcont hderiv r
  have heq : (fun s : ℝ => E_DevT ℓ d w s)
      = fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ) * (tailIntegral g) (s ^ 2) := by
    funext s
    rw [E_DevT, sinSq_eq]
  rw [heq]
  refine le_trans key ?_
  have hTle2 : (1 + E_T w) ≤ 2 * scale w := by linarith [hTle]
  have hpow : (1 + E_T w) ^ (M + (l : ℝ)) ≤ 2 ^ (M + (l : ℝ)) * (scale w) ^ (M + (l : ℝ)) := by
    rw [← Real.mul_rpow (by norm_num) hspos.le]
    exact Real.rpow_le_rpow (by linarith) hTle2 (by positivity)
  have hsw : (scale w) ^ N * (scale w) ^ (M + (l : ℝ)) = (scale w) ^ (N + M + (l : ℝ)) := by
    rw [← Real.rpow_add hspos N (M + (l : ℝ))]; congr 1; ring
  calc c₀ * (C * (scale w) ^ N * Real.pi ^ l * (1 + E_T w) ^ (M + (l : ℝ)) * D)
      ≤ c₀ * (C * (scale w) ^ N * Real.pi ^ l
          * (2 ^ (M + (l : ℝ)) * (scale w) ^ (M + (l : ℝ))) * D) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by positivity)) (le_trans hD0 le_rfl)) hc₀
    _ = c₀ * (C * Real.pi ^ l * 2 ^ (M + (l : ℝ)) * D) * (scale w) ^ (N + M + (l : ℝ)) := by
        rw [← hsw]; ring


/-- Analyticity of `E_ExprT` in `r`. -/
theorem E_contDiff_omega_E_ExprT (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hflat : EFlat ℓ d) {C N M : ℝ} (hC : 0 < C) (hN : 0 ≤ N) (hM : 0 ≤ M)
    {w : ℍ} (hw : w ∈ KEpsilon)
    (hwin : ∀ (w : ℍ) (t : ℝ), w ∈ KEpsilon → 1 ≤ t → t ≤ E_T w →
      ‖Kaxis (Kfun ℓ d) w t‖ ≤ C * (scale w) ^ N * (1 + t) ^ M)
    (htail : ∀ (w : ℍ) (t : ℝ), w ∈ KEpsilon → E_T w ≤ t →
      ‖Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖
        ≤ C * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * (t - E_T w)))) :
    ContDiff ℝ ω (fun s : ℝ => E_ExprT ℓ d w s) := by
  have h1 := E_contDiff_omega_layerLow ℓ d hd hflat hw
  have h2 := E_contDiff_omega_E_WinT ℓ d hd C N M hC hN hM hwin hw
  have h3 := E_contDiff_omega_E_DevT ℓ d hd C N M hC hN hM htail hw
  have h4 := contDiff_E_TailClosed (Gcusp ℓ d) (E_T w) w
  exact ((h1.add h2).add h3).add h4

/-- **The seminorm bound for the layer `E_ExprT` on the convergence region.** -/
lemma E_ExprT_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hflat : EFlat ℓ d) {C N M : ℝ} (hC : 0 < C) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hwin : ∀ (w : ℍ) (t : ℝ), w ∈ KEpsilon → 1 ≤ t → t ≤ E_T w →
      ‖Kaxis (Kfun ℓ d) w t‖ ≤ C * (scale w) ^ N * (1 + t) ^ M)
    (htail : ∀ (w : ℍ) (t : ℝ), w ∈ KEpsilon → E_T w ≤ t →
      ‖Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖
        ≤ C * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * (t - E_T w))))
    (hGcusp : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn KEpsilon (Gcusp ℓ d i j))
    (k l : ℕ) :
    ∃ c N' : ℝ, 0 ≤ c ∧ ∀ (w : ℍ) (r : ℝ), w ∈ KEpsilon → E_R ℓ d w r →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => E_ExprT ℓ d w s) r‖
        ≤ c * (scale w) ^ N' := by
  obtain ⟨c1, N1, hc1, hb1⟩ := E_layerLow_seminorm ℓ d hd hflat k l
  obtain ⟨c2, N2, hc2, hN2, hb2⟩ := E_WinT_seminorm ℓ d hd C N M hC hN hM hwin k l
  obtain ⟨c3, N3, hc3, hN3, hb3⟩ := E_DevT_seminorm ℓ d hd C N M hC hN hM htail k l
  obtain ⟨c4, N4, hc4, hN4, hb4⟩ := E_TailClosed_seminorm_T (Gcusp ℓ d) hGcusp k l
  set Nc : ℝ := max (max (max N1 N2) N3) N4 with hNcdef
  refine ⟨c1 + c2 + c3 + c4, Nc, by linarith, ?_⟩
  intro w r hw hR
  have hlow_cd : ContDiffAt ℝ ((l : ℕ∞ω)) (fun s : ℝ => layerLow ℓ d w s) r :=
    ((E_contDiff_omega_layerLow ℓ d hd hflat hw).contDiffAt).of_le le_top
  have hwin_cd : ContDiffAt ℝ ((l : ℕ∞ω)) (fun s : ℝ => E_WinT ℓ d w s) r :=
    ((E_contDiff_omega_E_WinT ℓ d hd C N M hC hN hM hwin hw).contDiffAt).of_le le_top
  have hdev_cd : ContDiffAt ℝ ((l : ℕ∞ω)) (fun s : ℝ => E_DevT ℓ d w s) r :=
    ((E_contDiff_omega_E_DevT ℓ d hd C N M hC hN hM htail hw).contDiffAt).of_le le_top
  have htc_cd : ContDiffAt ℝ ((l : ℕ∞ω))
      (fun s : ℝ => E_TailClosed (Gcusp ℓ d) (E_T w) w s) r :=
    ((contDiff_E_TailClosed (Gcusp ℓ d) (E_T w) w).contDiffAt).of_le le_top
  have hsplit : iteratedDeriv l (fun s : ℝ => E_ExprT ℓ d w s) r
      = iteratedDeriv l (fun s : ℝ => layerLow ℓ d w s) r
        + iteratedDeriv l (fun s : ℝ => E_WinT ℓ d w s) r
        + iteratedDeriv l (fun s : ℝ => E_DevT ℓ d w s) r
        + iteratedDeriv l (fun s : ℝ => E_TailClosed (Gcusp ℓ d) (E_T w) w s) r := by
    have hsplit1 : iteratedDeriv l (fun s : ℝ => layerLow ℓ d w s + E_WinT ℓ d w s) r
        = iteratedDeriv l (fun s : ℝ => layerLow ℓ d w s) r
          + iteratedDeriv l (fun s : ℝ => E_WinT ℓ d w s) r := by
      change iteratedDeriv l ((fun s : ℝ => layerLow ℓ d w s)
        + fun s : ℝ => E_WinT ℓ d w s) r = _
      exact iteratedDeriv_add hlow_cd hwin_cd
    have hsplit2 : iteratedDeriv l
          (fun s : ℝ => layerLow ℓ d w s + E_WinT ℓ d w s + E_DevT ℓ d w s) r
        = iteratedDeriv l (fun s : ℝ => layerLow ℓ d w s + E_WinT ℓ d w s) r
          + iteratedDeriv l (fun s : ℝ => E_DevT ℓ d w s) r := by
      change iteratedDeriv l (((fun s : ℝ => layerLow ℓ d w s)
        + fun s : ℝ => E_WinT ℓ d w s) + fun s : ℝ => E_DevT ℓ d w s) r = _
      exact iteratedDeriv_add (hlow_cd.add hwin_cd) hdev_cd
    have hsplit3 : iteratedDeriv l (fun s : ℝ => E_ExprT ℓ d w s) r
        = iteratedDeriv l
            (fun s : ℝ => layerLow ℓ d w s + E_WinT ℓ d w s + E_DevT ℓ d w s) r
          + iteratedDeriv l (fun s : ℝ => E_TailClosed (Gcusp ℓ d) (E_T w) w s) r := by
      change iteratedDeriv l ((((fun s : ℝ => layerLow ℓ d w s)
        + fun s : ℝ => E_WinT ℓ d w s) + fun s : ℝ => E_DevT ℓ d w s)
        + fun s : ℝ => E_TailClosed (Gcusp ℓ d) (E_T w) w s) r = _
      exact iteratedDeriv_add (hlow_cd.add hwin_cd |>.add hdev_cd) htc_cd
    rw [hsplit3, hsplit2, hsplit1]
  have h1 : (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d w s) r‖
      ≤ c1 * (scale w) ^ N1 := hb1 w r hw
  have h2 : (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => E_WinT ℓ d w s) r‖
      ≤ c2 * (scale w) ^ N2 := hb2 w hw r
  have h3 : (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => E_DevT ℓ d w s) r‖
      ≤ c3 * (scale w) ^ N3 := hb3 w hw r
  have h4 : (|r| ^ k) * ‖iteratedDeriv l
      (fun s : ℝ => E_TailClosed (Gcusp ℓ d) (E_T w) w s) r‖
      ≤ c4 * (scale w) ^ N4 := hb4 w hw r ((E_R_iff ℓ d w r).mp hR)
  rw [hsplit]
  have hs1 : 1 ≤ scale w := one_le_scale w
  have hN1 : N1 ≤ Nc := by
    rw [hNcdef]
    exact le_max_of_le_left (le_max_of_le_left (le_max_of_le_left le_rfl))
  have hN2 : N2 ≤ Nc := by
    rw [hNcdef]
    exact le_max_of_le_left (le_max_of_le_left (le_max_of_le_right le_rfl))
  have hN3 : N3 ≤ Nc := by
    rw [hNcdef]
    exact le_max_of_le_left (le_max_of_le_right le_rfl)
  have hN4 : N4 ≤ Nc := by
    rw [hNcdef]
    exact le_max_of_le_right le_rfl
  have e1 : c1 * (scale w) ^ N1 ≤ c1 * (scale w) ^ Nc :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs1 hN1) hc1
  have e2 : c2 * (scale w) ^ N2 ≤ c2 * (scale w) ^ Nc :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs1 hN2) hc2
  have e3 : c3 * (scale w) ^ N3 ≤ c3 * (scale w) ^ Nc :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs1 hN3) hc3
  have e4 : c4 * (scale w) ^ N4 ≤ c4 * (scale w) ^ Nc :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs1 hN4) hc4
  calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d w s) r
        + iteratedDeriv l (fun s : ℝ => E_WinT ℓ d w s) r
        + iteratedDeriv l (fun s : ℝ => E_DevT ℓ d w s) r
        + iteratedDeriv l (fun s : ℝ => E_TailClosed (Gcusp ℓ d) (E_T w) w s) r‖
      ≤ (|r| ^ k) * (‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d w s) r‖
          + ‖iteratedDeriv l (fun s : ℝ => E_WinT ℓ d w s) r‖
          + ‖iteratedDeriv l (fun s : ℝ => E_DevT ℓ d w s) r‖
          + ‖iteratedDeriv l (fun s : ℝ => E_TailClosed (Gcusp ℓ d) (E_T w) w s) r‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith [norm_add_le (iteratedDeriv l (fun s : ℝ => layerLow ℓ d w s) r
            + iteratedDeriv l (fun s : ℝ => E_WinT ℓ d w s) r
            + iteratedDeriv l (fun s : ℝ => E_DevT ℓ d w s) r)
          (iteratedDeriv l (fun s : ℝ => E_TailClosed (Gcusp ℓ d) (E_T w) w s) r),
          norm_add_le (iteratedDeriv l (fun s : ℝ => layerLow ℓ d w s) r
            + iteratedDeriv l (fun s : ℝ => E_WinT ℓ d w s) r)
            (iteratedDeriv l (fun s : ℝ => E_DevT ℓ d w s) r),
          norm_add_le (iteratedDeriv l (fun s : ℝ => layerLow ℓ d w s) r)
            (iteratedDeriv l (fun s : ℝ => E_WinT ℓ d w s) r)]
    _ = (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => layerLow ℓ d w s) r‖
          + (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => E_WinT ℓ d w s) r‖
          + (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => E_DevT ℓ d w s) r‖
          + (|r| ^ k) * ‖iteratedDeriv l
              (fun s : ℝ => E_TailClosed (Gcusp ℓ d) (E_T w) w s) r‖ := by ring
    _ ≤ c1 * (scale w) ^ N1 + c2 * (scale w) ^ N2 + c3 * (scale w) ^ N3
          + c4 * (scale w) ^ N4 := by linarith
    _ ≤ (c1 + c2 + c3 + c4) * (scale w) ^ Nc := by
        have hsum : c1 * (scale w) ^ Nc + c2 * (scale w) ^ Nc + c3 * (scale w) ^ Nc
            + c4 * (scale w) ^ Nc = (c1 + c2 + c3 + c4) * (scale w) ^ Nc := by ring
        linarith [e1, e2, e3, e4]



/-- If the contour integrand `Kaxis·e^{-πr²t}` is integrable on `(0,∞)` and the deviation
`K - Aexp` decays like `e^{-π(t - E_T w)}` beyond the threshold `E_T w`, then the model part
`Aexp·e^{-πr²t}` is integrable on `(E_T w, ∞)`. -/
theorem E_integrableOn_Aexp_exp_T (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {C N M : ℝ} (hC : 0 < C) (hN : 0 ≤ N) (hM : 0 ≤ M) {w : ℍ} (hw : w ∈ KEpsilon) {r : ℝ}
    (htail : ∀ t : ℝ, E_T w ≤ t →
      ‖Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖
        ≤ C * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * (t - E_T w))))
    (hInt : MeasureTheory.IntegrableOn (fun t : ℝ => Kaxis (Kfun ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Aexp (Gcusp ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi (E_T w)) := by
  set L : ℝ := Real.pi * r ^ 2 with hLdef
  have hT1 : (1 : ℝ) ≤ E_T w := one_le_E_T hw
  have hT0 : 0 < E_T w := lt_of_lt_of_le zero_lt_one hT1
  have hspos : 0 < scale w := scale_pos w
  have hFeq : (fun t : ℝ => Kaxis (Kfun ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      = fun t : ℝ => Kaxis (Kfun ℓ d) w t * Complex.exp (-(L : ℂ) * (t : ℂ)) := by
    funext t
    congr 2
    rw [hLdef]; push_cast; ring
  rw [hFeq] at hInt
  have hF_intT : MeasureTheory.IntegrableOn (fun t : ℝ => Kaxis (Kfun ℓ d) w t
      * Complex.exp (-(L : ℂ) * (t : ℂ))) (Set.Ioi (E_T w)) :=
    hInt.mono_set (fun t ht => lt_trans hT0 (Set.mem_Ioi.mp ht))
  have hmeasK : Measurable (fun t : ℝ => Kaxis (Kfun ℓ d) w t) :=
    measurable_Kaxis_of_measurable (Kfun ℓ d) w (measurable_Kfun_snd_all ℓ d hd w)
  have hmeasA : Measurable (fun t : ℝ => Aexp (Gcusp ℓ d) w t) := by unfold Aexp; fun_prop
  have hmeasE : Measurable (fun t : ℝ => Complex.exp (-(L : ℂ) * (t : ℂ))) := by fun_prop
  have hD_intT : MeasureTheory.IntegrableOn (fun t : ℝ =>
      (Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t)
      * Complex.exp (-(L : ℂ) * (t : ℂ))) (Set.Ioi (E_T w)) := by
    have hbase : MeasureTheory.IntegrableOn
        (fun t : ℝ => C * (scale w) ^ N * 2 ^ M * Real.exp (Real.pi * E_T w)
          * (t ^ M * Real.exp (-(Real.pi * t)))) (Set.Ioi (E_T w)) :=
      (Work.Asymptotics.integrableOn_rpow_mul_exp_neg M Real.pi hM Real.pi_pos).mono_set
        (fun t ht => le_trans hT1 (le_of_lt ht)) |>.const_mul _
    refine Integrable.mono' hbase ((hmeasK.sub hmeasA).mul hmeasE).aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have htT : E_T w ≤ t := le_of_lt ht
    have ht1 : (1 : ℝ) ≤ t := le_trans hT1 htT
    have hb := htail t htT
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(L : ℂ) * (t : ℂ)).re = -(L * t) := by
      rw [Complex.mul_re, Complex.neg_re, Complex.neg_im]
      simp
    rw [hre]
    have hLt : 0 ≤ L * t := mul_nonneg (by rw [hLdef]; positivity) (le_of_lt (lt_of_lt_of_le zero_lt_one ht1))
    have he1 : Real.exp (-(L * t)) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    have hexp_split : Real.exp (-(Real.pi * (t - E_T w)))
        = Real.exp (Real.pi * E_T w) * Real.exp (-(Real.pi * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc ‖Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖ * Real.exp (-(L * t))
        ≤ (C * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * (t - E_T w)))) * 1 :=
          mul_le_mul hb he1 (Real.exp_nonneg _) (by positivity)
      _ = C * (scale w) ^ N * (1 + t) ^ M
            * (Real.exp (Real.pi * E_T w) * Real.exp (-(Real.pi * t))) := by rw [mul_one, hexp_split]
      _ ≤ C * (scale w) ^ N * (2 ^ M * t ^ M)
            * (Real.exp (Real.pi * E_T w) * Real.exp (-(Real.pi * t))) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
            (by positivity)
          have h2 : (1 + t) ^ M ≤ (2 * t) ^ M := Real.rpow_le_rpow (by linarith) (by linarith) hM
          have h3 : (2 * t) ^ M = 2 ^ M * t ^ M := Real.mul_rpow (by norm_num) (by linarith)
          rw [← h3]; exact h2
      _ = C * (scale w) ^ N * 2 ^ M * Real.exp (Real.pi * E_T w)
            * (t ^ M * Real.exp (-(Real.pi * t))) := by ring
  have hsub := hF_intT.sub hD_intT
  refine MeasureTheory.IntegrableOn.congr_fun hsub (fun t _ => ?_) measurableSet_Ioi
  have harg : -(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)) = -(L : ℂ) * (t : ℂ) := by
    rw [hLdef]; push_cast; ring
  rw [harg]
  simp only [Pi.sub_apply]
  ring

/-- **The seminorm bound for the punctured layer `E_F2T`, in `scale`-form.** -/
lemma E_F2T_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hflat : EFlat ℓ d) {C N M : ℝ} (hC : 0 < C) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hwin : ∀ (w : ℍ) (t : ℝ), w ∈ KEpsilon → 1 ≤ t → t ≤ E_T w →
      ‖Kaxis (Kfun ℓ d) w t‖ ≤ C * (scale w) ^ N * (1 + t) ^ M)
    (htail : ∀ (w : ℍ) (t : ℝ), w ∈ KEpsilon → E_T w ≤ t →
      ‖Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖
        ≤ C * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * (t - E_T w))))
    (hGcusp : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn KEpsilon (Gcusp ℓ d i j))
    (k l : ℕ) :
    ∃ c N' : ℝ, 0 ≤ c ∧ ∀ (w : ℍ), w ∈ KEpsilon → ∀ r : ℝ,
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => E_F2T ℓ d w s) r‖
        ≤ c * (scale w) ^ N' := by
  obtain ⟨c, Nc, hc, hb⟩ := E_ExprT_bound ℓ d hd hflat hC hN hM hwin htail hGcusp k l
  refine ⟨c, Nc, hc, ?_⟩
  intro w hw r
  have hcN : (0 : ℝ) ≤ c * (scale w) ^ Nc :=
    mul_nonneg hc (Real.rpow_nonneg (scale_pos w).le Nc)
  by_cases hR : r ≠ 0 ∧ E_R ℓ d w r
  · rcases hR with ⟨hr0, hRw⟩
    have hev : (fun s : ℝ => E_F2T ℓ d w s) =ᶠ[𝓝 r] (fun s : ℝ => E_ExprT ℓ d w s) := by
      rcases hRw with hlt | hz
      · have hnb : ∀ᶠ s in 𝓝 r, 2 < s ^ 2 :=
          (isOpen_lt continuous_const (by fun_prop : Continuous fun s : ℝ => s ^ 2)).mem_nhds hlt
        filter_upwards [hnb, isOpen_ne.mem_nhds hr0] with s hs2 hs0
        exact E_F2T_of_R ℓ d w s ⟨hs0, Or.inl hs2⟩
      · filter_upwards [isOpen_ne.mem_nhds hr0] with s hs0
        exact E_F2T_of_R ℓ d w s ⟨hs0, Or.inr hz⟩
    rw [iteratedDeriv_congr_of_eventuallyEq hev l]
    exact hb w r hw hRw
  · rcases eq_or_ne r 0 with h0 | hr0
    · subst h0
      by_cases hz : E_R ℓ d w 0
      · -- the contact point `r = 0` with `G 1 j = 0`: puncture argument
        have hz' : Gcusp ℓ d 1 0 w = 0 ∧ Gcusp ℓ d 1 1 w = 0 := by
          rcases hz with h | h
          · exact absurd h (by norm_num)
          · exact h
        rcases l with _ | l'
        · rw [iteratedDeriv_zero, E_F2T_of_not_R ℓ d w 0 hR, norm_zero, mul_zero]
          exact hcN
        · have hF₂eq : (fun s : ℝ => E_F2T ℓ d w s)
              = fun s : ℝ => if s = 0 then 0 else E_ExprT ℓ d w s := by
            funext s
            by_cases hs : s = 0
            · subst hs; rw [E_F2T_of_not_R ℓ d w 0 hR]; simp
            · rw [E_F2T_of_R ℓ d w s ⟨hs, Or.inr hz'⟩]; simp [hs]
          rw [hF₂eq]
          rw [punctured_iteratedDeriv (E_ExprT_neg ℓ d w)
            ((E_contDiff_omega_E_ExprT ℓ d hd hflat hC hN hM hw hwin htail).differentiable
              (by simp)) (l' + 1) (by omega)]
          exact hb w 0 hw hz
      · -- `G 1 j ≠ 0`: the layer vanishes on a neighbourhood of `0`
        have hnb : ∀ᶠ s in 𝓝 (0 : ℝ), ¬ (s ≠ 0 ∧ E_R ℓ d w s) := by
          have hnb2 : ∀ᶠ s in 𝓝 (0 : ℝ), s ^ 2 < 2 :=
            (isOpen_lt (by fun_prop : Continuous fun s : ℝ => s ^ 2) continuous_const).mem_nhds
              (by norm_num)
          filter_upwards [hnb2] with s hs
          rintro ⟨_, hsR⟩
          rcases hsR with h | h
          · exact absurd hs (not_lt.mpr (le_of_lt h))
          · exact hz (Or.inr h)
        have hev : (fun s : ℝ => E_F2T ℓ d w s) =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℂ)) := by
          filter_upwards [hnb] with s hs
          exact E_F2T_of_not_R ℓ d w s hs
        rw [iteratedDeriv_congr_of_eventuallyEq hev l, iteratedDeriv_zeroFun]
        simp only [norm_zero, mul_zero]
        exact hcN
    · have hRw : ¬ E_R ℓ d w r := fun hE => hR ⟨hr0, hE⟩
      rw [E_R_iff] at hRw
      obtain ⟨hnot2, hz⟩ := not_or.mp hRw
      have hr2 : r ^ 2 ≤ 2 := not_lt.mp hnot2
      rcases lt_or_eq_of_le hr2 with hlt2 | heq2
      · have hnb : ∀ᶠ s in 𝓝 r, ¬ (s ≠ 0 ∧ E_R ℓ d w s) := by
          have hnb2 : ∀ᶠ s in 𝓝 r, s ^ 2 < 2 :=
            (isOpen_lt (by fun_prop : Continuous fun s : ℝ => s ^ 2) continuous_const).mem_nhds hlt2
          filter_upwards [hnb2] with s hs
          rintro ⟨_, hsR⟩
          rcases hsR with h | h
          · exact absurd hs (not_lt.mpr (le_of_lt h))
          · exact hz h
        have hev : (fun s : ℝ => E_F2T ℓ d w s) =ᶠ[𝓝 r] (fun _ => (0 : ℂ)) := by
          filter_upwards [hnb] with s hs
          exact E_F2T_of_not_R ℓ d w s hs
        rw [iteratedDeriv_congr_of_eventuallyEq hev l, iteratedDeriv_zeroFun]
        simp only [norm_zero, mul_zero]
        exact hcN
      · -- the threshold points `r = ±√2`
        rcases l with _ | l'
        · rw [iteratedDeriv_zero, E_F2T_of_not_R ℓ d w r hR, norm_zero, mul_zero]
          exact hcN
        · have h2sq : r ^ 2 = (Real.sqrt 2) ^ 2 := by
            rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; exact heq2
          have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
          rcases (sq_eq_sq_iff_eq_or_eq_neg (a := r) (b := Real.sqrt 2)).mp h2sq with hsq | hsq
          · subst hsq
            have hzero : ∀ y ∈ Set.Ioo (0 : ℝ) (Real.sqrt 2), E_F2T ℓ d w y = 0 := by
              intro y hy
              refine E_F2T_of_not_R ℓ d w y ?_
              rintro ⟨_, hyR⟩
              rcases hyR with h | h
              · have hy2 : y ^ 2 < 2 := by
                  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hy.1, hy.2]
                exact absurd hy2 (not_lt.mpr (le_of_lt h))
              · exact hz h
            rw [iteratedDeriv_succ_eq_zero_of_eqOn_Ioo_left hsqrt2 hzero l']
            simp only [norm_zero, mul_zero]
            exact hcN
          · subst hsq
            have hzero : ∀ y ∈ Set.Ioo (-Real.sqrt 2) (0 : ℝ), E_F2T ℓ d w y = 0 := by
              intro y hy
              refine E_F2T_of_not_R ℓ d w y ?_
              rintro ⟨_, hyR⟩
              rcases hyR with h | h
              · have hy2 : y ^ 2 < 2 := by
                  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hy.1, hy.2]
                exact absurd hy2 (not_lt.mpr (le_of_lt h))
              · exact hz h
            rw [iteratedDeriv_succ_eq_zero_of_eqOn_Ioo_right
              (by linarith [hsqrt2] : -Real.sqrt 2 < (0 : ℝ)) hzero l']
            simp only [norm_zero, mul_zero]
            exact hcN


/-- **Agreement of the layer `E_ExprT` with the naive contour transform** on the convergence
region.  The four pieces telescope:
`layerLow + ∫_1^{T} K + ∫_{t ≥ T}(K - Aexp) + E_TailClosed(Gcusp) T = sinSq r · ∫_0^∞ K`. -/
theorem E_F2T_agreement (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (C N M : ℝ) (hC : 0 < C) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (htail : ∀ (w : ℍ) (t : ℝ), w ∈ KEpsilon → E_T w ≤ t →
      ‖Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖
        ≤ C * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * (t - E_T w)))) :
    ∀ (w : ℍ) (r : ℝ), w ∈ KEpsilon → r ≠ 0 →
      MeasureTheory.IntegrableOn (fun t : ℝ =>
        Kaxis (Kfun ℓ d) w t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) →
      E_ExprT ℓ d w r = kernelTransform (Kfun ℓ d) w r := by
  intro w r hw hr hInt
  have hT1 : (1 : ℝ) ≤ E_T w := one_le_E_T hw
  set F : ℝ → ℂ := fun t => Kaxis (Kfun ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hF
  set G : ℝ → ℂ := fun t => Aexp (Gcusp ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hG
  have hEeq : ∀ t : ℝ, (Real.exp (-(Real.pi * r ^ 2 * t)) : ℂ)
      = Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
    intro t
    rw [show -(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)) = ((-(Real.pi * r ^ 2 * t) : ℝ) : ℂ) by
      push_cast; ring, ← Complex.ofReal_exp]
  have hFint0 : MeasureTheory.IntegrableOn F (Set.Ioi 0) := hInt
  have hFintIoi1 : MeasureTheory.IntegrableOn F (Set.Ioi 1) :=
    hFint0.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  have hFintIoc1 : MeasureTheory.IntegrableOn F (Set.Ioc 1 (E_T w)) :=
    hFint0.mono_set (fun t ht =>
      Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one ht.1.le))
  have hFintIoiT : MeasureTheory.IntegrableOn F (Set.Ioi (E_T w)) :=
    hFint0.mono_set (fun t ht =>
      Set.mem_Ioi.mpr (lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hT1) ht.le))
  have hFintIoc01 : MeasureTheory.IntegrableOn F (Set.Ioc 0 1) :=
    hFint0.mono_set Set.Ioc_subset_Ioi_self
  -- splitting `∫_{Ioi 0} F = ∫_{0..1} F + ∫_{Ioi 1} F`
  have hsplit0 : ∫ t in Set.Ioi (0 : ℝ), F t
      = (∫ t in (0 : ℝ)..1, F t) + ∫ t in Set.Ioi 1, F t := by
    have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi 1) :=
      Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2 (not_lt.mpr hx1.2))
    have hunion : ∫ t in Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ), F t
        = (∫ t in Set.Ioc (0 : ℝ) 1, F t) + ∫ t in Set.Ioi (1 : ℝ), F t :=
      setIntegral_union hdisj measurableSet_Ioi hFintIoc01 hFintIoi1
    have hset : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi (0 : ℝ) := by
      ext x; simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · rintro (⟨h1, _⟩ | h3)
        · exact h1
        · exact lt_trans zero_lt_one h3
      · intro h1
        by_cases h2 : x ≤ 1
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (lt_of_not_ge h2)
    rw [hset] at hunion
    rw [hunion, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  -- splitting `∫_{Ioi 1} F = ∫_{1..T} F + ∫_{Ioi T} F`
  have hsplit1 : ∫ t in Set.Ioi (1 : ℝ), F t
      = (∫ t in (1 : ℝ)..(E_T w), F t) + ∫ t in Set.Ioi (E_T w), F t := by
    have hdisj : Disjoint (Set.Ioc (1 : ℝ) (E_T w)) (Set.Ioi (E_T w)) :=
      Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2 (not_lt.mpr hx1.2))
    have hunion : ∫ t in Set.Ioc (1 : ℝ) (E_T w) ∪ Set.Ioi (E_T w), F t
        = (∫ t in Set.Ioc (1 : ℝ) (E_T w), F t) + ∫ t in Set.Ioi (E_T w), F t :=
      setIntegral_union hdisj measurableSet_Ioi hFintIoc1 hFintIoiT
    have hset : Set.Ioc (1 : ℝ) (E_T w) ∪ Set.Ioi (E_T w) = Set.Ioi (1 : ℝ) :=
      Set.Ioc_union_Ioi_eq_Ioi hT1
    rw [hset] at hunion
    rw [hunion, intervalIntegral.integral_of_le hT1]
  -- integrability of the model part
  have hGintT : MeasureTheory.IntegrableOn G (Set.Ioi (E_T w)) :=
    E_integrableOn_Aexp_exp_T ℓ d hd hC hN hM hw (fun t ht => htail w t hw ht) hInt
  have hFsubG : MeasureTheory.IntegrableOn (F - G) (Set.Ioi (E_T w)) := hFintIoiT.sub hGintT
  -- the closed form of the model tail
  have hTC : E_TailClosed (Gcusp ℓ d) (E_T w) w r = sinSq r * ∫ t in Set.Ioi (E_T w), G t := by
    rw [E_F2_E_TailClosed_eq_integral (G := Gcusp ℓ d) (B := E_T w) (w := w) (r := r)
      hT1 hr hGintT]
  -- the deviation piece as an integral over `(E_T w, ∞)`
  have hdev : E_DevT ℓ d w r = sinSq r * ∫ t in Set.Ioi (E_T w), (F - G) t := by
    rw [E_DevT, tailIntegral]
    congr 1
    rw [setIntegral_Ici_eq_of_eq_zero_below hT1
      (f := fun t : ℝ => (if t < E_T w then 0
        else Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t)
          * (Real.exp (-(Real.pi * r ^ 2 * t)) : ℂ))
      (by intro t ht; rw [if_pos ht, zero_mul])]
    rw [setIntegral_congr_set (Ioi_ae_eq_Ici' (by simp : volume ({(E_T w)} : Set ℝ) = 0)).symm]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have htT : E_T w ≤ t := le_of_lt ht
    rw [if_neg (not_lt.mpr htT), hF, hG, hEeq t]
    simp only [Pi.sub_apply]
    ring
  -- the window and low pieces
  have hwin_id : E_WinT ℓ d w r = sinSq r * ∫ t in (1 : ℝ)..(E_T w), F t := rfl
  have hlow_id : layerLow ℓ d w r = sinSq r * ∫ t in (0 : ℝ)..1, F t := rfl
  have hkernel_id : kernelTransform (Kfun ℓ d) w r = sinSq r * ∫ t in Set.Ioi (0 : ℝ), F t := rfl
  -- the telescoping identity
  have hgoal : (∫ t in (0 : ℝ)..1, F t) + (∫ t in (1 : ℝ)..(E_T w), F t)
        + (∫ t in Set.Ioi (E_T w), (F - G) t) + (∫ t in Set.Ioi (E_T w), G t)
      = ∫ t in Set.Ioi (0 : ℝ), F t := by
    have hsub : (∫ t in Set.Ioi (E_T w), F t)
        = (∫ t in Set.Ioi (E_T w), (F - G) t) + (∫ t in Set.Ioi (E_T w), G t) := by
      have h := MeasureTheory.integral_add hFsubG hGintT
      have hcongr : (∫ t, ((F - G) t + G t) ∂(volume.restrict (Set.Ioi (E_T w))))
          = ∫ t in Set.Ioi (E_T w), F t :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun t => by
          simp only [Pi.add_apply, Pi.sub_apply]; ring))
      rw [hcongr] at h
      exact h
    rw [hsplit0, hsplit1, hsub]
    ring
  rw [E_ExprT, hlow_id, hwin_id, hdev, hTC, hkernel_id]
  calc sinSq r * (∫ t in (0 : ℝ)..1, F t) + sinSq r * (∫ t in (1 : ℝ)..(E_T w), F t)
        + sinSq r * (∫ t in Set.Ioi (E_T w), (F - G) t)
        + sinSq r * (∫ t in Set.Ioi (E_T w), G t)
      = sinSq r * ((∫ t in (0 : ℝ)..1, F t) + (∫ t in (1 : ℝ)..(E_T w), F t)
        + (∫ t in Set.Ioi (E_T w), (F - G) t) + (∫ t in Set.Ioi (E_T w), G t)) := by ring
    _ = sinSq r * ∫ t in Set.Ioi (0 : ℝ), F t := by rw [hgoal]

/-- **The seminorm bound for `K` on the cusp-`0` neighbourhood `E = KEpsilon`**, from the two
regimes at the threshold `E_T w`. -/
theorem SeminormK_E_of_assembled (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hflat : EFlat ℓ d)
    (C N M : ℝ) (hC : 0 < C) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hwin : ∀ (w : ℍ) (t : ℝ), w ∈ KEpsilon → 1 ≤ t → t ≤ E_T w →
      ‖Kaxis (Kfun ℓ d) w t‖ ≤ C * (scale w) ^ N * (1 + t) ^ M)
    (htail : ∀ (w : ℍ) (t : ℝ), w ∈ KEpsilon → E_T w ≤ t →
      ‖Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖
        ≤ C * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * (t - E_T w)))) :
    SeminormK_E ℓ d := by
  have hGcusp : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn KEpsilon (Gcusp ℓ d i j) :=
    fun i j => (GcuspInP ℓ d i j).mono KEpsilon_subset_DomainD
  refine E_kernelTransform_seminorm_of_layer0 ℓ d hd (E_F2T ℓ d) ?_ ?_ ?_
  · -- agreement at `r = 0`
    intro w hw
    rw [E_F2T_of_not_R ℓ d w 0 (fun h => h.1 rfl), Work.Kernels.kernelTransform]
    simp
  · -- agreement on the convergence region
    intro w r hw hInt
    by_cases hr : r = 0
    · subst hr
      rw [E_F2T_of_not_R ℓ d w 0 (fun h => h.1 rfl), Work.Kernels.kernelTransform]
      simp
    · by_cases hR : E_R ℓ d w r
      · rw [E_F2T_of_R ℓ d w r ⟨hr, hR⟩]
        exact E_F2T_agreement ℓ d hd C N M hC hN hM htail w r hw hr hInt
      · exfalso
        rw [E_R_iff] at hR
        obtain ⟨hnot, hz⟩ := not_or.mp hR
        have hLpos : 0 < Real.pi * r ^ 2 := by positivity
        have hmu : Real.pi * r ^ 2 - 2 * Real.pi ≤ 0 := by
          nlinarith [Real.pi_pos, not_lt.mp hnot]
        have hAexp_int := E_integrableOn_Aexp_exp_T ℓ d hd hC hN hM hw
          (fun t ht => htail w t hw ht) hInt
        set L : ℝ := Real.pi * r ^ 2 with hLdef
        have hAexp_int' : MeasureTheory.IntegrableOn (fun t : ℝ => Aexp (Gcusp ℓ d) w t
            * Complex.exp (-(L : ℂ) * (t : ℂ))) (Set.Ioi (E_T w)) := by
          refine MeasureTheory.IntegrableOn.congr_fun hAexp_int (fun t _ => ?_) measurableSet_Ioi
          have harg : -(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)) = -(L : ℂ) * (t : ℂ) := by
            rw [hLdef]; push_cast; ring
          rw [← harg]
        have hP_int : MeasureTheory.IntegrableOn (fun t : ℝ =>
            (Gcusp ℓ d 0 0 w + (t : ℂ) * Complex.I * Gcusp ℓ d 0 1 w)
              * Complex.exp (-(L : ℂ) * (t : ℂ))) (Set.Ioi (E_T w)) := by
          refine (integrableOn_affine_mul_exp_neg_mul_complex L hLpos _ _).mono_set
            (Set.Ioi_subset_Ioi (by linarith [one_le_E_T hw]))
        have hPQ := MeasureTheory.IntegrableOn.congr_fun hAexp_int'
          (fun t _ => (E_Aexp_exp_decomp (Gcusp ℓ d) w L t)) measurableSet_Ioi
        have hQ_int := hPQ.sub hP_int
        have hQ_int' : MeasureTheory.IntegrableOn (fun t : ℝ =>
            (Gcusp ℓ d 1 0 w + (t : ℂ) * Complex.I * Gcusp ℓ d 1 1 w)
              * Complex.exp (-((L - 2 * Real.pi : ℝ) : ℂ) * (t : ℂ)))
            (Set.Ioi (E_T w)) :=
          MeasureTheory.IntegrableOn.congr_fun hQ_int (fun t _ => by
            simp only [Pi.sub_apply]; ring) measurableSet_Ioi
        exact hz (E_eq_zero_of_integrableOn_affine_exp_Ioi hmu (E_T w) hQ_int')
  · -- the seminorm bound
    intro k l
    obtain ⟨c, N', hc, hb⟩ := E_F2T_bound ℓ d hd hflat hC hN hM hwin htail hGcusp k l
    refine ⟨c * 3 ^ max N' 0, max N' 0, c * 3 ^ max N' 0, max N' 0,
      by positivity, le_max_right _ _, by positivity, le_max_right _ _, ?_⟩
    intro w r hw
    have h1 := hb w hw r
    have hM0 : (0 : ℝ) ≤ max N' 0 := le_max_right _ _
    have hle : N' ≤ max N' 0 := le_max_left _ _
    have e1 : (scale w) ^ N' ≤ (scale w) ^ (max N' 0) :=
      Real.rpow_le_rpow_of_exponent_le (one_le_scale w) hle
    have e2 : c * (scale w) ^ N' ≤ c * (scale w) ^ (max N' 0) :=
      mul_le_mul_of_nonneg_left e1 hc
    have e3 := paperLayer_scale_rpow_le (τ := w) hM0
    refine le_trans h1 ?_
    calc c * (scale w) ^ N' ≤ c * (scale w) ^ (max N' 0) := e2
      _ ≤ c * (3 ^ (max N' 0) * ((w.im) ^ (-(max N' 0)) + ‖(w : ℂ)‖ ^ (max N' 0))) :=
          mul_le_mul_of_nonneg_left e3 hc
      _ = c * 3 ^ (max N' 0) * (w.im) ^ (-(max N' 0))
          + c * 3 ^ (max N' 0) * ‖(w : ℂ)‖ ^ (max N' 0) := by ring

/-- The `r`-seminorm bound for the contour transform on the cusp-`0` disk
`E = {w ∈ 𝒟 : 2 ≤ Im (S • w)}`: this is the CKMRV moderate-growth assertion at the cusp `0`. -/
theorem cuspRegion_seminorm_disk0 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ Work.Asymptotics.DomainD →
        2 ≤ (ModularGroup.S • τ).im →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ s) r‖
          ≤ α * (τ.im) ^ (-β) + γ * (‖(τ : ℂ)‖) ^ δ := by
  have hflat : EFlat ℓ d := (Epoint_Kfun ℓ d hd).1
  obtain ⟨Cw, Nw, Mw, hCw, hNw, hMw, hwin_far⟩ := EpolyWindowE_clean_far ℓ d hd
  obtain ⟨Cd, Nd, Md, hCd, hNd, hMd, hdev⟩ := E_deviation_sharp ℓ d hd
  set C : ℝ := max Cw (Cd * Real.exp (-(Real.pi))) with hCdef
  set N : ℝ := max Nw Nd with hNdef
  set M : ℝ := max Mw Md with hMdef
  have hCpos : 0 < C := by rw [hCdef]; exact lt_max_of_lt_left hCw
  have hN0 : 0 ≤ N := by rw [hNdef]; exact le_max_of_le_left hNw
  have hM0 : 0 ≤ M := by rw [hMdef]; exact le_max_of_le_left hMw
  have hwin : ∀ (w : ℍ) (t : ℝ), w ∈ KEpsilon → 1 ≤ t → t ≤ E_T w →
      ‖Kaxis (Kfun ℓ d) w t‖ ≤ C * (scale w) ^ N * (1 + t) ^ M := by
    intro w t hw ht1 htT
    have hb := hwin_far w t hw (lt_of_lt_of_le zero_lt_one ht1) (le_trans htT (E_T_le_scale hw))
    refine le_trans hb ?_
    have e1 : Cw ≤ C := by rw [hCdef]; exact le_max_left _ _
    have e2 : (scale w) ^ Nw ≤ (scale w) ^ N := Real.rpow_le_rpow_of_exponent_le
      (one_le_scale w) (by rw [hNdef]; exact le_max_left _ _)
    have e3 : (1 + t) ^ Mw ≤ (1 + t) ^ M := Real.rpow_le_rpow_of_exponent_le
      (by linarith) (by rw [hMdef]; exact le_max_left _ _)
    calc Cw * (scale w) ^ Nw * (1 + t) ^ Mw
        = Cw * ((scale w) ^ Nw * (1 + t) ^ Mw) := by ring
      _ ≤ C * ((scale w) ^ N * (1 + t) ^ M) :=
          mul_le_mul e1 (mul_le_mul e2 e3 (Real.rpow_nonneg (by linarith) Mw)
            (Real.rpow_nonneg (scale_pos w).le N))
            (mul_nonneg (Real.rpow_nonneg (scale_pos w).le Nw)
              (Real.rpow_nonneg (by linarith) Mw)) hCpos.le
      _ = C * (scale w) ^ N * (1 + t) ^ M := by ring
  have htail : ∀ (w : ℍ) (t : ℝ), w ∈ KEpsilon → E_T w ≤ t →
      ‖Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖
        ≤ C * (scale w) ^ N * (1 + t) ^ M
            * Real.exp (-(Real.pi * (t - E_T w))) := by
    intro w t hw htT
    have hT1 : (1 : ℝ) ≤ E_T w := one_le_E_T hw
    have him : (ModularGroup.S • w).im + 1 ≤ t := by
      rw [show (ModularGroup.S • w).im + 1 = E_T w from rfl]; exact htT
    have hb := hdev w t hw him
    have hsplit : t - (ModularGroup.S • w).im = (t - E_T w) + 1 := by
      rw [show E_T w = (ModularGroup.S • w).im + 1 from rfl]; ring
    rw [hsplit] at hb
    rw [show -(Real.pi * ((t - E_T w) + 1)) = -(Real.pi * (t - E_T w)) + -Real.pi from by ring,
      Real.exp_add] at hb
    calc ‖Kaxis (Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖
        ≤ Cd * (scale w) ^ Nd * (1 + t) ^ Md
            * (Real.exp (-(Real.pi * (t - E_T w))) * Real.exp (-Real.pi)) := hb
      _ = Cd * Real.exp (-(Real.pi)) * (scale w) ^ Nd * (1 + t) ^ Md
            * Real.exp (-(Real.pi * (t - E_T w))) := by ring
      _ ≤ C * (scale w) ^ N * (1 + t) ^ M * Real.exp (-(Real.pi * (t - E_T w))) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
          have e1 : Cd * Real.exp (-(Real.pi)) ≤ C := by
            rw [hCdef]; exact le_max_right _ _
          have e2 : (scale w) ^ Nd ≤ (scale w) ^ N := Real.rpow_le_rpow_of_exponent_le
            (one_le_scale w) (by rw [hNdef]; exact le_max_right _ _)
          have e3 : (1 + t) ^ Md ≤ (1 + t) ^ M := Real.rpow_le_rpow_of_exponent_le
            (by linarith) (by rw [hMdef]; exact le_max_right _ _)
          calc Cd * Real.exp (-(Real.pi)) * (scale w) ^ Nd * (1 + t) ^ Md
              = (Cd * Real.exp (-(Real.pi))) * ((scale w) ^ Nd * (1 + t) ^ Md) := by ring
            _ ≤ C * ((scale w) ^ N * (1 + t) ^ M) :=
                mul_le_mul e1 (mul_le_mul e2 e3 (Real.rpow_nonneg (by linarith) Md)
                  (Real.rpow_nonneg (scale_pos w).le N))
                  (mul_nonneg (Real.rpow_nonneg (scale_pos w).le Nd)
                    (Real.rpow_nonneg (by linarith) Md)) hCpos.le
            _ = C * (scale w) ^ N * (1 + t) ^ M := by ring
  have hmain := SeminormK_E_of_assembled ℓ d hd hflat C N M hCpos hN0 hM0 hwin htail
  intro k l
  obtain ⟨α, β, γ, δ, h1, h2, h3, h4, hb⟩ := hmain k l
  exact ⟨α, β, γ, δ, h1, h2, h3, h4, fun τ r hτD hτim => hb τ r ⟨hτD, hτim⟩⟩

end Work.Asymptotics
