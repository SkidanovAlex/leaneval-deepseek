import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.c_bounds
import Submission.Work.EllipticEst.ModalSolution.angular_ibp_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

local notation "Iθ" => Work.Spaces.Iθ
local notation "Idm" => Work.FTS.EllipticEst.Lzero1
local notation "eF" => Work.FTS.PhiStar.Gegenbauer.eFam
local notation "GB" => Work.FTS.VocabO.GamBar
local notation "λm" => Work.FTS.PhiStar.Gegenbauer.lam

theorem measurableSet_Iθ : MeasurableSet Iθ := measurableSet_Icc

theorem isFiniteMeasure_Iθ : IsFiniteMeasure (volume.restrict Iθ) := by
  rw [show Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl,
    MeasureTheory.isFiniteMeasure_restrict, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

theorem integrableOn_Iθ_of_bound {f : ℝ → ℝ}
    (hm : AEStronglyMeasurable f (volume.restrict Iθ)) {C : ℝ}
    (hC : ∀ θ ∈ Iθ, |f θ| ≤ C) : IntegrableOn f Iθ := by
  haveI : IsFiniteMeasure (volume.restrict Iθ) := isFiniteMeasure_Iθ
  have hb : ∀ᵐ θ ∂(volume.restrict Iθ), ‖f θ‖ ≤ C := by
    rw [ae_restrict_iff' measurableSet_Iθ]
    exact Eventually.of_forall fun θ hθ => by rw [Real.norm_eq_abs]; exact hC θ hθ
  exact Integrable.of_bound hm C hb

theorem iota_eq (F : ℝ → ℝ) :
    (∫ θ in (0 : ℝ)..(Real.pi / 2), F θ) = ∫ θ in Iθ, F θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (f := F) (by positivity : (0 : ℝ) ≤ Real.pi / 2)]

theorem integral_nonneg_Iθ {g : ℝ → ℝ} (hg : ∀ θ, 0 ≤ g θ) : 0 ≤ ∫ θ in Iθ, g θ := by
  rw [← iota_eq]
  exact intervalIntegral.integral_nonneg_of_forall (by positivity) hg

theorem eF_zero (m : ℕ) : eF m 0 = 0 := by
  rw [Work.FTS.PhiStar.Gegenbauer.eFam]
  simp [Work.FTS.PhiStar.Gegenbauer.gC_odd_zero m]

theorem eF_pi (m : ℕ) : eF m (Real.pi / 2) = 0 := by
  rw [Work.FTS.PhiStar.Gegenbauer.eFam]
  simp

theorem contDiff_eF (m : ℕ) : ContDiff ℝ 2 (eF m) := by
  rw [show eF m = fun θ => Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)
    from rfl]
  exact (Real.contDiff_cos.mul
    ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).comp Real.contDiff_sin)).of_le
      (by norm_num)

theorem Gam_abs_le_one {α : ℝ} (hα : 0 ≤ α) {θ : ℝ} (hθ : θ ∈ Iθ) :
    |Work.Spaces.Gam α θ| ≤ 1 := by
  show |(Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)| ≤ 1
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hb0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := mul_nonneg hsin (sq_nonneg _)
  have hb1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [hsin, Real.sin_le_one θ, sq_nonneg (Real.cos θ), Real.sin_sq_add_cos_sq θ]
  rw [abs_of_nonneg (Real.rpow_nonneg hb0 _)]
  exact Real.rpow_le_one hb0 hb1 (by positivity)

theorem GamBar_abs_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Iθ) :
    |GB α θ| ≤ 45 / 4 := by
  show |Work.Spaces.Gam α θ / Work.Spaces.c α - 5 / 4 * Real.sin (2 * θ)| ≤ 45 / 4
  have hGam : |Work.Spaces.Gam α θ| ≤ 1 := Gam_abs_le_one (by positivity) hθ
  have hca : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := lt_of_lt_of_le (by norm_num) hca
  have h1 : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 := by
    rw [abs_div, abs_of_pos hcpos, div_le_iff₀ hcpos]
    nlinarith [hGam, hca]
  have h2 : |(5 / 4) * Real.sin (2 * θ)| ≤ 5 / 4 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4)]
    have := (abs_le.mpr (Real.sin_mem_Icc (2 * θ)) : |Real.sin (2 * θ)| ≤ 1)
    linarith
  calc |Work.Spaces.Gam α θ / Work.Spaces.c α - 5 / 4 * Real.sin (2 * θ)|
      ≤ |Work.Spaces.Gam α θ / Work.Spaces.c α| + |5 / 4 * Real.sin (2 * θ)| := abs_sub _ _
    _ ≤ 10 + 5 / 4 := add_le_add h1 h2
    _ = 45 / 4 := by norm_num

theorem Gam_zero {α : ℝ} (hα : 0 < α) : Work.Spaces.Gam α 0 = 0 := by
  show (Real.sin (0 : ℝ) * Real.cos (0 : ℝ) ^ 2) ^ (α / 3) = 0
  rw [show Real.sin (0 : ℝ) * Real.cos (0 : ℝ) ^ 2 = 0 from by simp,
    Real.zero_rpow (by positivity : α / 3 ≠ 0)]

theorem Gam_pi_div_two {α : ℝ} (hα : 0 < α) : Work.Spaces.Gam α (Real.pi / 2) = 0 := by
  show (Real.sin (Real.pi / 2) * Real.cos (Real.pi / 2) ^ 2) ^ (α / 3) = 0
  rw [show Real.sin (Real.pi / 2) * Real.cos (Real.pi / 2) ^ 2 = 0 from by simp,
    Real.zero_rpow (by positivity : α / 3 ≠ 0)]

theorem GamBar_zero {α : ℝ} (hα : 0 < α) : GB α 0 = 0 := by
  show Work.Spaces.Gam α 0 / Work.Spaces.c α - 5 / 4 * Real.sin (2 * 0) = 0
  rw [Gam_zero hα]
  simp

theorem GamBar_pi_div_two {α : ℝ} (hα : 0 < α) : GB α (Real.pi / 2) = 0 := by
  show Work.Spaces.Gam α (Real.pi / 2) / Work.Spaces.c α
      - 5 / 4 * Real.sin (2 * (Real.pi / 2)) = 0
  rw [Gam_pi_div_two hα]
  have h2 : 2 * (Real.pi / 2) = Real.pi := by ring
  rw [h2, Real.sin_pi]
  ring

theorem continuousOn_GamBar (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ContinuousOn (fun θ => GB α θ) Iθ := by
  have hcne : Work.Spaces.c α ≠ 0 := by
    have := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  show ContinuousOn (fun θ => Work.Spaces.Gam α θ / Work.Spaces.c α
    - 5 / 4 * Real.sin (2 * θ)) Iθ
  refine ContinuousOn.sub ?_ ?_
  · refine ContinuousOn.div ?_ continuousOn_const (fun θ _ => hcne)
    · show ContinuousOn (fun θ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)) Iθ
      exact ((Real.continuous_rpow_const (by positivity : (0 : ℝ) ≤ α / 3)).comp
        (Real.continuous_sin.mul (Real.continuous_cos.pow 2))).continuousOn
  · exact (continuous_const.mul (Real.continuous_sin.comp
      (continuous_const.mul continuous_id))).continuousOn

theorem sq_integral_mul_le (f g : ℝ → ℝ)
    (hf : IntegrableOn (fun θ => f θ ^ 2) Iθ)
    (hfg : IntegrableOn (fun θ => f θ * g θ) Iθ)
    (hg : IntegrableOn (fun θ => g θ ^ 2) Iθ) :
    (∫ θ in Iθ, f θ * g θ) ^ 2 ≤ (∫ θ in Iθ, f θ ^ 2) * (∫ θ in Iθ, g θ ^ 2) := by
  set A : ℝ := ∫ θ in Iθ, f θ ^ 2 with hA
  set B : ℝ := ∫ θ in Iθ, f θ * g θ with hB
  set C : ℝ := ∫ θ in Iθ, g θ ^ 2 with hC
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact integral_nonneg_Iθ (fun θ => sq_nonneg (f θ))
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact integral_nonneg_Iθ (fun θ => sq_nonneg (g θ))
  have hquad : ∀ t : ℝ, 0 ≤ A - 2 * t * B + t ^ 2 * C := by
    intro t
    have hsub : IntegrableOn (fun θ => f θ ^ 2 - 2 * t * (f θ * g θ)) Iθ :=
      hf.sub (hfg.const_mul (2 * t))
    have hfull : IntegrableOn
        (fun θ => f θ ^ 2 - 2 * t * (f θ * g θ) + t ^ 2 * g θ ^ 2) Iθ :=
      hsub.add (hg.const_mul (t ^ 2))
    have hcongr : (∫ θ in Iθ, (f θ - t * g θ) ^ 2)
        = ∫ θ in Iθ, (f θ ^ 2 - 2 * t * (f θ * g θ) + t ^ 2 * g θ ^ 2) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (fun θ _ => ?_)
      ring
    have hval : (∫ θ in Iθ, (f θ ^ 2 - 2 * t * (f θ * g θ) + t ^ 2 * g θ ^ 2))
        = A - 2 * t * B + t ^ 2 * C := by
      have e1 : (∫ θ in Iθ, (f θ ^ 2 - 2 * t * (f θ * g θ) + t ^ 2 * g θ ^ 2))
          = (∫ θ in Iθ, (f θ ^ 2 - 2 * t * (f θ * g θ))) + (∫ θ in Iθ, t ^ 2 * g θ ^ 2) :=
        integral_add hsub (hg.const_mul (t ^ 2))
      have e2 : (∫ θ in Iθ, (f θ ^ 2 - 2 * t * (f θ * g θ)))
          = (∫ θ in Iθ, f θ ^ 2) - (∫ θ in Iθ, 2 * t * (f θ * g θ)) :=
        integral_sub hf (hfg.const_mul (2 * t))
      have e3 : (∫ θ in Iθ, 2 * t * (f θ * g θ)) = 2 * t * (∫ θ in Iθ, f θ * g θ) :=
        integral_const_mul (2 * t) (fun θ => f θ * g θ)
      have e4 : (∫ θ in Iθ, t ^ 2 * g θ ^ 2) = t ^ 2 * (∫ θ in Iθ, g θ ^ 2) :=
        integral_const_mul (t ^ 2) (fun θ => g θ ^ 2)
      rw [e1, e2, e3, e4, ← hA, ← hB, ← hC]
    have hnonneg : (∫ θ in Iθ, (f θ - t * g θ) ^ 2) = A - 2 * t * B + t ^ 2 * C :=
      hcongr.trans hval
    rw [← hnonneg]
    exact integral_nonneg_Iθ (fun θ => by
      have h : (f θ - t * g θ) ^ 2 = f θ ^ 2 - 2 * t * (f θ * g θ) + t ^ 2 * g θ ^ 2 := by ring
      rw [h]; nlinarith [sq_nonneg (f θ - t * g θ)])
  rcases eq_or_lt_of_le hC0 with h | h
  · have hB0 : B = 0 := by
      by_contra hBne
      have hmul : (A + 1) / B * B = A + 1 := div_mul_cancel₀ _ hBne
      have h2 : 2 * ((A + 1) / B) * B = 2 * (A + 1) := by
        rw [show 2 * ((A + 1) / B) * B = 2 * (((A + 1) / B) * B) from by ring, hmul]
      have ht := hquad ((A + 1) / B)
      rw [← h] at ht
      rw [h2] at ht
      simp only [mul_zero, add_zero] at ht
      nlinarith [ht, hA0]
    rw [hB0, ← h]
    norm_num
  · have hCpos : 0 < C := h
    have hx : 2 * (B / C) * B = 2 * (B ^ 2 / C) := by
      rw [show 2 * (B / C) * B = 2 * ((B / C) * B) from by ring]
      congr 1
      field_simp
    have hy : (B / C) ^ 2 * C = B ^ 2 / C := by
      field_simp
    have ht := hquad (B / C)
    rw [hx, hy] at ht
    have ht' : B ^ 2 / C ≤ A := by linarith [ht]
    rw [div_le_iff₀ hCpos] at ht'
    exact ht'

theorem deriv_eq_zero_of_eventuallyEq_zero {v : ℝ → ℝ} {θ : ℝ}
    (h : v =ᶠ[𝓝 θ] (fun _ : ℝ => 0)) : deriv v θ = 0 := by
  have hh : deriv (fun _ : ℝ => (0 : ℝ)) θ = deriv v θ := Filter.EventuallyEq.deriv_eq h.symm
  rw [deriv_const] at hh
  exact hh.symm

theorem Lzero1_eq_zero_of_eventuallyEq_zero {v : ℝ → ℝ} {θ : ℝ}
    (h : v =ᶠ[𝓝 θ] (fun _ : ℝ => 0)) : Idm v θ = 0 := by
  obtain ⟨U, hUsub, hUopen, hθU⟩ := mem_nhds_iff.mp h
  have hU : U ∈ 𝓝 θ := hUopen.mem_nhds hθU
  have hvθ : v θ = 0 := h.self_of_nhds
  have hdv : deriv v =ᶠ[𝓝 θ] (fun _ : ℝ => 0) := by
    filter_upwards [hU] with t ht
    exact deriv_eq_zero_of_eventuallyEq_zero
      (by filter_upwards [hUopen.mem_nhds ht] with s hs; exact hUsub hs)
  have hd2 : deriv (fun t => deriv v t) θ = 0 := by
    have hh : deriv (fun t => deriv v t) θ = deriv (fun _ : ℝ => (0 : ℝ)) θ :=
      Filter.EventuallyEq.deriv_eq hdv
    rw [deriv_const] at hh
    exact hh
  have hd3 : deriv (fun t => Real.tan t * v t) θ = 0 :=
    deriv_eq_zero_of_eventuallyEq_zero (by
      filter_upwards [hU] with t ht
      have h1 : v t = 0 := hUsub ht
      simp [h1])
  simp only [Work.FTS.EllipticEst.Lzero1]
  rw [hd2, hd3, hvθ]
  ring

theorem lzero1_mul_eq {χ e : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) (he : ContDiff ℝ 2 e)
    {θ : ℝ} (hcos : Real.cos θ ≠ 0) :
    Idm (fun t => χ t * e t) θ
      = χ θ * Idm e θ
        + (-(deriv (deriv χ) θ * e θ) - 2 * (deriv χ θ * deriv e θ)
            + Real.tan θ * deriv χ θ * e θ) := by
  have hdχ : ∀ t, HasDerivAt χ (deriv χ t) t := fun t =>
    ((hχ.contDiffAt (x := t)).differentiableAt (by norm_num)).hasDerivAt
  have hde : ∀ t, HasDerivAt e (deriv e t) t := fun t =>
    ((he.contDiffAt (x := t)).differentiableAt (by norm_num)).hasDerivAt
  have hdχ' : ∀ t, HasDerivAt (deriv χ) (deriv (deriv χ) t) t := fun t =>
    (((hχ.contDiffAt (x := t)).derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt
  have hde' : ∀ t, HasDerivAt (deriv e) (deriv (deriv e) t) t := fun t =>
    (((he.contDiffAt (x := t)).derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt
  have hχe : deriv (fun t => χ t * e t) = fun t => χ t * deriv e t + deriv χ t * e t := by
    funext t
    have h : deriv (fun s => χ s * e s) t = deriv χ t * e t + χ t * deriv e t :=
      ((hdχ t).mul (hde t)).deriv
    rw [h]; ring
  have hA : deriv (fun t => deriv (fun s => χ s * e s) t) θ
      = deriv (deriv χ) θ * e θ + 2 * (deriv χ θ * deriv e θ) + χ θ * deriv (deriv e) θ := by
    rw [hχe]
    have h1 : HasDerivAt (fun t => χ t * deriv e t)
        (deriv χ θ * deriv e θ + χ θ * deriv (deriv e) θ) θ := (hdχ θ).mul (hde' θ)
    have h2 : HasDerivAt (fun t => deriv χ t * e t)
        (deriv (deriv χ) θ * e θ + deriv χ θ * deriv e θ) θ := (hdχ' θ).mul (hde θ)
    have hfun : (fun t => χ t * deriv e t + deriv χ t * e t)
        = (fun t => χ t * deriv e t) + (fun t => deriv χ t * e t) := by
      funext t
      simp
    rw [hfun]
    have h := (h1.add h2).deriv
    rw [h]
    ring
  have hB : deriv (fun t => Real.tan t * (χ t * e t)) θ
      = 1 / Real.cos θ ^ 2 * (χ θ * e θ)
        + Real.tan θ * (χ θ * deriv e θ + deriv χ θ * e θ) := by
    have h : deriv (fun t => Real.tan t * (χ t * e t)) θ
        = 1 / Real.cos θ ^ 2 * (χ θ * e θ)
          + Real.tan θ * (deriv χ θ * e θ + χ θ * deriv e θ) :=
      ((Real.hasDerivAt_tan hcos).mul ((hdχ θ).mul (hde θ))).deriv
    rw [h]; ring
  have hC : deriv (fun t => Real.tan t * e t) θ
      = 1 / Real.cos θ ^ 2 * e θ + Real.tan θ * deriv e θ := by
    have h : deriv (fun t => Real.tan t * e t) θ
        = 1 / Real.cos θ ^ 2 * e θ + Real.tan θ * deriv e θ :=
      ((Real.hasDerivAt_tan hcos).mul (hde θ)).deriv
    exact h
  have hD : deriv (fun t => deriv e t) θ = deriv (deriv e) θ := rfl
  simp only [Work.FTS.EllipticEst.Lzero1]
  rw [hA, hB, hC, hD]
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  ring

theorem ibp_Iθ {u v : ℝ → ℝ} {c d : ℝ} (hc : 0 < c) (hcd : c < d) (hd : d < Real.pi / 2)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hv : ContDiffOn ℝ 2 v (Set.Ioo 0 (Real.pi / 2)))
    (hv0 : ∀ θ, θ ∉ Set.Icc c d → v θ = 0) :
    ∫ θ in Iθ, (u θ * Idm v θ - Idm u θ * v θ) * Real.cos θ = 0 := by
  have h := Work.EllipticEst.ModalSolution.angular_ibp_zero hc hcd hd hu hv hv0
  have hsub : Set.Icc c d ⊆ Iθ := fun θ hθ =>
    ⟨le_of_lt (lt_of_lt_of_le hc hθ.1), le_of_lt (lt_of_le_of_lt hθ.2 hd)⟩
  have hstep : (∫ θ in Iθ, (u θ * Idm v θ - Idm u θ * v θ) * Real.cos θ)
      = ∫ θ in Set.Icc c d, (u θ * Idm v θ - Idm u θ * v θ) * Real.cos θ := by
    refine MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      measurableSet_Iθ hsub (fun θ hθ => ?_)
    have hvz : v θ = 0 := hv0 θ hθ.2
    have hLz : Idm v θ = 0 := by
      rcases lt_or_ge θ c with hlt | hge
      · refine Lzero1_eq_zero_of_eventuallyEq_zero ?_
        filter_upwards [isOpen_Iio.mem_nhds hlt] with t ht
        exact hv0 t (fun hmem => absurd hmem.1 (not_le.mpr ht))
      · have hgt : d < θ := by
          by_contra hcon
          exact hθ.2 ⟨hge, le_of_not_gt hcon⟩
        refine Lzero1_eq_zero_of_eventuallyEq_zero ?_
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with t ht
        exact hv0 t (fun hmem => absurd hmem.2 (not_le.mpr ht))
    rw [hvz, hLz]
    ring
  rw [hstep]
  exact h

theorem tan_mul_cos_eq (a θ : ℝ) (h : Real.cos θ ≠ 0) :
    Real.tan θ * a * Real.cos θ = Real.sin θ * a := by
  rw [Real.tan_eq_sin_div_cos]
  field_simp

theorem abs_tan_mul_cos_le (a θ : ℝ) : |Real.tan θ * a * Real.cos θ| ≤ |a| := by
  rcases eq_or_ne (Real.cos θ) 0 with h | h
  · rw [h, mul_zero, abs_zero]
    exact abs_nonneg a
  · rw [tan_mul_cos_eq a θ h, abs_mul]
    have h1 : |Real.sin θ| ≤ 1 := abs_le.mpr (Real.sin_mem_Icc θ)
    calc |Real.sin θ| * |a| ≤ 1 * |a| := mul_le_mul_of_nonneg_right h1 (abs_nonneg a)
      _ = |a| := one_mul _

end Work.FTS.PhiStar.Series
