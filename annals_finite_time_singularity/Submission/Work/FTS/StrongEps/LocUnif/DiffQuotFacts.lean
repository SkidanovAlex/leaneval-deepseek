import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Facts for `diffQuot_backward_lintegral_le`

Three elementary facts used by `Work.FTS.StrongEps.LocUnif.diffQuot_backward_lintegral_le`:

* `ofReal_interval_integral_sq_le` — Cauchy–Schwarz with the constant weight `1`, in the
  unconditional `ℝ≥0∞`-valued form: `(∫_a^b f)² ≤ (b - a) · ∫⁻_a^b f²`.  (Adapted from
  `Work.FTS.EllipticEst.DzAmgm.OfRealIntervalIntegralSqLe`, which carries the weight `(b - t)`.)
* `setLIntegral_Icc_comp_sub` — translation invariance of a set integral over an interval
  (substituting `x ↦ x - c`).
* `integral_deriv_slice_sub` — the fundamental theorem of calculus for a `C¹` slice of `u`,
  in the backward form `∫_0^h ∂_zu(z - s, θ) ds = u z θ - u (z - h) θ`.
-/

noncomputable section

open scoped ENNReal
open MeasureTheory Set

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false

/-- **Cauchy–Schwarz with constant weight**, `ℝ≥0∞`-valued (no integrability needed):

`(∫_a^b f)² ≤ (b - a) · ∫⁻_{t ∈ (a,b]} f t ^ 2` for `a ≤ b` and `f` a.e. strongly measurable. -/
theorem ofReal_interval_integral_sq_le {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioc a b))) :
    ENNReal.ofReal ((∫ t in a..b, f t) ^ 2)
      ≤ ENNReal.ofReal (b - a) * ∫⁻ t in Set.Ioc a b, ENNReal.ofReal ((f t) ^ 2) := by
  rw [intervalIntegral.integral_of_le hab]
  set F : ℝ → ℝ≥0∞ := fun _ => 1 with hF
  set H : ℝ → ℝ≥0∞ := fun t => ‖f t‖ₑ with hH
  have hFmeas : AEMeasurable F (volume.restrict (Set.Ioc a b)) := aemeasurable_const
  have hHmeas : AEMeasurable H (volume.restrict (Set.Ioc a b)) := by
    rw [hH]; exact hf.enorm
  have hF2 : ∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ) = ENNReal.ofReal (b - a) := by
    have hpt : ∀ t : ℝ, (F t) ^ (2 : ℝ) = (1 : ℝ≥0∞) := by
      intro t; simp [hF]
    simp_rw [hpt]
    rw [MeasureTheory.setLIntegral_const, one_mul, Real.volume_Ioc]
  have hH2 : ∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)
      = ∫⁻ t in Set.Ioc a b, ENNReal.ofReal ((f t) ^ 2) := by
    refine lintegral_congr fun t => ?_
    simp only [hH]
    rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (abs_nonneg (f t)) 2, sq_abs]
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hCS : ∫⁻ t in Set.Ioc a b, F t * H t
      ≤ (∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        * (∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Set.Ioc a b)) hpq hFmeas hHmeas
  have hrpow : ((∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        * (∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) ^ (2 : ℝ)
      = (∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ)) * (∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)) := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (show (0 : ℝ) ≤ 1 / 2 by norm_num),
      ← ENNReal.rpow_mul,
      show (1 : ℝ) / 2 * 2 = 1 by norm_num, ENNReal.rpow_one]
  have hCSsq : (∫⁻ t in Set.Ioc a b, F t * H t) ^ (2 : ℝ)
      ≤ (∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ))
        * (∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)) := by
    have h2 := ENNReal.rpow_le_rpow hCS (show (0 : ℝ) ≤ 2 by norm_num)
    rwa [hrpow] at h2
  have hInt : ENNReal.ofReal |∫ t in Set.Ioc a b, f t|
      ≤ ∫⁻ t in Set.Ioc a b, F t * H t := by
    have h1 : ‖∫ t in Set.Ioc a b, f t‖ₑ ≤ ∫⁻ t in Set.Ioc a b, ‖f t‖ₑ :=
      enorm_integral_le_lintegral_enorm (fun t => f t)
    rw [Real.enorm_eq_ofReal_abs] at h1
    refine h1.trans (le_of_eq ?_)
    refine lintegral_congr fun t => ?_
    simp only [hF, hH, one_mul]
  have hleft : ENNReal.ofReal ((∫ t in Set.Ioc a b, f t) ^ 2)
      ≤ (∫⁻ t in Set.Ioc a b, F t * H t) ^ (2 : ℝ) := by
    have h1 : ENNReal.ofReal ((∫ t in Set.Ioc a b, f t) ^ 2)
        = (ENNReal.ofReal |∫ t in Set.Ioc a b, f t|) ^ 2 := by
      rw [← sq_abs (∫ t in Set.Ioc a b, f t)]
      exact ENNReal.ofReal_pow (abs_nonneg _) 2
    rw [h1, ← ENNReal.rpow_two]
    exact ENNReal.rpow_le_rpow hInt (show (0 : ℝ) ≤ 2 by norm_num)
  calc ENNReal.ofReal ((∫ t in Set.Ioc a b, f t) ^ 2)
      ≤ (∫⁻ t in Set.Ioc a b, F t * H t) ^ (2 : ℝ) := hleft
    _ ≤ (∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ))
        * (∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)) := hCSsq
    _ = ENNReal.ofReal (b - a) * ∫⁻ t in Set.Ioc a b, ENNReal.ofReal ((f t) ^ 2) := by
        rw [hF2, hH2]

/-- Translation invariance of the set integral over an interval: substituting `x ↦ x - c`. -/
theorem setLIntegral_Icc_comp_sub (f : ℝ → ℝ≥0∞) (c s t : ℝ) :
    ∫⁻ x in Set.Icc s t, f (x - c) = ∫⁻ x in Set.Icc (s - c) (t - c), f x := by
  rw [← lintegral_indicator measurableSet_Icc (fun x => f (x - c)),
    ← lintegral_indicator measurableSet_Icc (fun x => f x)]
  have hfun : (fun x => (Set.Icc s t).indicator (fun x => f (x - c)) x)
      = fun x => (Set.Icc (s - c) (t - c)).indicator f (x - c) := by
    funext x
    by_cases hx : x ∈ Set.Icc s t
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (by
        simp only [Set.mem_Icc] at hx ⊢; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (by
        simp only [Set.mem_Icc] at hx ⊢
        exact fun h => hx ⟨by linarith [h.1], by linarith [h.2]⟩)]
  rw [hfun, lintegral_sub_right_eq_self _ c]

/-- The fundamental theorem of calculus for a `C¹` slice of `u`, backward form. -/
theorem integral_deriv_slice_sub {a b : ℝ} {u : ℝ → ℝ → ℝ} {h z θ : ℝ} (hh : 0 ≤ h)
    (hsub : Set.Icc (z - h) z ⊆ Set.Ioo a b)
    (hu : ContDiffOn ℝ 1 (fun z' => u z' θ) (Set.Ioo a b)) :
    ∫ s in (0 : ℝ)..h, deriv (fun z' => u z' θ) (z - s) = u z θ - u (z - h) θ := by
  rw [intervalIntegral.integral_comp_sub_left (fun y => deriv (fun z' => u z' θ) y) z]
  simp only [sub_zero]
  have hIcc : Set.Icc (z - h) z ⊆ Set.Ioo a b := hsub
  have hcont : ContinuousOn (fun z' => u z' θ) (Set.Icc (z - h) z) :=
    hu.continuousOn.mono hIcc
  have hderiv : ∀ x ∈ Set.Ioo (z - h) z, HasDerivAt (fun z' => u z' θ)
      (deriv (fun z' => u z' θ) x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo a b := hIcc (Set.Ioo_subset_Icc_self hx)
    exact ((hu.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hx')).hasDerivAt
  have hcont_d : ContinuousOn (deriv (fun z' => u z' θ)) (Set.uIcc (z - h) z) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact (hu.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hIcc
  have hint : IntervalIntegrable (deriv (fun z' => u z' θ)) volume (z - h) z :=
    hcont_d.intervalIntegrable
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith) hcont hderiv hint

end Work.FTS.StrongEps.LocUnif
