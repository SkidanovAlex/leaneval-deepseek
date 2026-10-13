import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.remov.coerc.weak_poincare_second

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

/-- Interval integrals over `[0, π/2]` agree with set integrals over the closed angular slice
`Iθ = [0, π/2]`. -/
private lemma integral_of_le_pi2 (g : ℝ → ℝ) :
    (∫ t in (0 : ℝ)..(Real.pi / 2), g t) = ∫ t in Work.Spaces.Iθ, g t := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rw [intervalIntegral.integral_of_le hle, Work.Spaces.Iθ,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- The Lebesgue measure of the angular slice `Iθ = [0, π/2]` is `π/2`. -/
private lemma volume_real_Iθ : volume.real Work.Spaces.Iθ = Real.pi / 2 := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rw [Work.Spaces.Iθ, Real.volume_real_Icc_of_le hle, sub_zero]

/-- The measure `volume.restrict Iθ` equals `volume.restrict (Ioo 0 (π/2))`: the two endpoints
of the slice form a null set. -/
private lemma restrict_Iθ_eq_restrict_Ioo :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
  rw [Work.Spaces.Iθ]
  exact (Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2) (μ := volume))).symm

/-- The integral of a constant over the angular slice. -/
private lemma setIntegral_const_Iθ (c : ℝ) :
    (∫ _ in Work.Spaces.Iθ, c) = (Real.pi / 2) * c := by
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, volume_real_Iθ]

/-- A constant is integrable over the angular slice. -/
private lemma integrableOn_const_Iθ (c : ℝ) : IntegrableOn (fun _ : ℝ => c) Work.Spaces.Iθ :=
  MeasureTheory.integrableOn_const (s := Work.Spaces.Iθ) (μ := volume) (C := c)
    (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)

/-- A constant is integrable over the open interval. -/
private lemma integrableOn_const_Ioo (c : ℝ) :
    Integrable (fun _ : ℝ => c) (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
  MeasureTheory.integrableOn_const (s := Set.Ioo (0 : ℝ) (Real.pi / 2)) (μ := volume) (C := c)
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)

/-- An everywhere-true-on-`(0, π/2)` statement is true almost everywhere on the slice. -/
private lemma ae_Iθ_of_Ioo {p : ℝ → Prop}
    (h : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), p x) :
    ∀ᵐ x ∂(volume.restrict Work.Spaces.Iθ), p x := by
  rw [restrict_Iθ_eq_restrict_Ioo]
  exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall h)

/-- **Boundedness criterion.** A function that is continuous on `(0, π/2)` and bounded there by
a constant is integrable over the angular slice `Iθ`. -/
private lemma integrableOn_Iθ_of_bound {g : ℝ → ℝ} {C : ℝ}
    (hg : ContinuousOn g (Set.Ioo 0 (Real.pi / 2)))
    (hbd : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), |g x| ≤ C) :
    IntegrableOn g Work.Spaces.Iθ := by
  show Integrable g (volume.restrict Work.Spaces.Iθ)
  rw [restrict_Iθ_eq_restrict_Ioo]
  refine Integrable.mono' (integrableOn_const_Ioo C)
    (hg.aestronglyMeasurable measurableSet_Ioo) ?_
  exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2
    (Eventually.of_forall (fun x hx => by rw [Real.norm_eq_abs]; exact hbd x hx))

theorem sliceWirtinger :
    ∀ (f : ℝ → ℝ), ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      ContinuousOn f (Set.Icc 0 (Real.pi / 2)) → f 0 = 0 → f (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn (fun θ => (deriv (deriv f) θ) ^ 2) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2) ≤ 4 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2)
        ∧ (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2)
            ≤ 4 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2) := by
  intro f hC2 hcont hf0 hfL hint
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  -- ## regularity facts
  have hd1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
    hC2.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hcont2 : ContinuousOn (deriv (deriv f)) (Set.Ioo 0 (Real.pi / 2)) :=
    hd1.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hdiff : DifferentiableOn ℝ f (Set.Ioo 0 (Real.pi / 2)) := hC2.differentiableOn (by norm_num)
  have hd2diff : DifferentiableOn ℝ (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
    hd1.differentiableOn (by norm_num)
  have hdiffAt : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt f (deriv f x) x :=
    fun x hx => (hdiff.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have hd2At : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt (deriv f) (deriv (deriv f) x) x :=
    fun x hx => (hd2diff.differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  -- ## integrability of `f''` (from the integrability of its square), and of `|f''|`
  have hintf2 : IntegrableOn (fun θ => deriv (deriv f) θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.remov.coerc.integrableOn_of_integrableOn_sq hpi hcont2 hint
  have hintabs : IntegrableOn (fun θ => |deriv (deriv f) θ|) Work.Spaces.Iθ := by
    show Integrable (fun θ => |deriv (deriv f) θ|) (volume.restrict Work.Spaces.Iθ)
    simpa only [Real.norm_eq_abs] using hintf2.abs
  -- ## Rolle: `f'` vanishes somewhere in the open interval
  obtain ⟨c, hc, hczslope⟩ := exists_deriv_eq_slope f hpi hcont hdiff
  have hcz : deriv f c = 0 := by
    rw [hczslope, hfL, hf0]
    simp
  -- ## the pointwise bound for `f'`
  have hf'bd : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |deriv f θ| ≤ ∫ s in Work.Spaces.Iθ, |deriv (deriv f) s| :=
    Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv hd1 hc hcz hintabs
  -- ## notation
  set M : ℝ := ∫ s in Work.Spaces.Iθ, |deriv (deriv f) s| with hMdef
  set B : ℝ := ∫ s in Work.Spaces.Iθ, (deriv f s) ^ 2 with hBdef
  set C : ℝ := ∫ s in Work.Spaces.Iθ, (deriv (deriv f) s) ^ 2 with hCdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact setIntegral_nonneg measurableSet_Icc (fun x _ => abs_nonneg _)
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    exact MeasureTheory.integral_nonneg (f := fun θ => (deriv (deriv f) θ) ^ 2) (fun _ => sq_nonneg _)
  -- ## integrability of `(f')²` on the slice
  have hBsq_int : IntegrableOn (fun θ => (deriv f θ) ^ 2) Work.Spaces.Iθ :=
    integrableOn_Iθ_of_bound ((hd1.continuousOn).pow 2) (fun x hx => by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hf'bd x hx) 2)
  -- ## `B ≤ (π/2) * M²`
  have hB_le : B ≤ (Real.pi / 2) * M ^ 2 := by
    have hae : (fun θ => (deriv f θ) ^ 2) ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun _ : ℝ => M ^ 2) :=
      ae_Iθ_of_Ioo (fun x hx => by
        have h := pow_le_pow_left₀ (abs_nonneg (deriv f x)) (hf'bd x hx) 2
        rwa [sq_abs] at h)
    have hmono := MeasureTheory.integral_mono_ae hBsq_int (integrableOn_const_Iθ (M ^ 2)) hae
    calc B = ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 := hBdef.symm
      _ ≤ ∫ _ in Work.Spaces.Iθ, M ^ 2 := hmono
      _ = (Real.pi / 2) * M ^ 2 := setIntegral_const_Iθ (M ^ 2)
  -- ## Cauchy–Schwarz: `M² ≤ (π/2) * C`
  have hM2_le : M ^ 2 ≤ (Real.pi / 2) * C := by
    have h1 : IntervalIntegrable (fun t => |deriv (deriv f) t|) volume 0 (Real.pi / 2) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hpi.le).mpr hintabs
    have h2 : IntervalIntegrable (fun t => (|deriv (deriv f) t|) ^ 2) volume 0 (Real.pi / 2) := by
      have e : (fun t => (|deriv (deriv f) t|) ^ 2) = (fun t => (deriv (deriv f) t) ^ 2) := by
        funext t
        rw [sq_abs]
      rw [e]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hpi.le).mpr hint
    have hcs := Work.FTS.EllipticEst.remov.coerc.sq_intervalIntegral_le hpi.le h1 h2
    have e1 : (∫ t in (0 : ℝ)..(Real.pi / 2), |deriv (deriv f) t|) = M := by
      rw [integral_of_le_pi2, ← hMdef]
    have e2 : (∫ t in (0 : ℝ)..(Real.pi / 2), (|deriv (deriv f) t|) ^ 2) = C := by
      have e : (fun t => (|deriv (deriv f) t|) ^ 2) = (fun t => (deriv (deriv f) t) ^ 2) := by
        funext t
        rw [sq_abs]
      rw [e, integral_of_le_pi2, ← hCdef]
    rw [e1, e2, sub_zero] at hcs
    exact hcs
  -- ## integrability of `f'` and of `|f'|`
  have hderivf_int : IntegrableOn (fun θ => deriv f θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.remov.coerc.integrableOn_of_integrableOn_sq hpi hd1.continuousOn hBsq_int
  have hderivf_abs : IntegrableOn (fun θ => |deriv f θ|) Work.Spaces.Iθ := by
    show Integrable (fun θ => |deriv f θ|) (volume.restrict Work.Spaces.Iθ)
    simpa only [Real.norm_eq_abs] using hderivf_int.abs
  -- ## the two-sided fundamental-theorem bound for `f`
  have hfbd : ∀ x ∈ Set.Ioo 0 (Real.pi / 2),
      |f x| ≤ (1 / 2) * ∫ s in Work.Spaces.Iθ, |deriv f s| := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have hxL : x < Real.pi / 2 := hx.2
    have hI0x : IntervalIntegrable (deriv f) volume 0 x :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hx0.le).mpr
        (hderivf_int.mono_set (Set.Icc_subset_Icc le_rfl hxL.le))
    have hIxL : IntervalIntegrable (deriv f) volume x (Real.pi / 2) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hxL.le).mpr
        (hderivf_int.mono_set (Set.Icc_subset_Icc hx0.le le_rfl))
    have hFTC1 : (∫ t in (0 : ℝ)..x, deriv f t) = f x - f 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx0.le
        (hcont.mono (Set.Icc_subset_Icc le_rfl hxL.le))
        (fun t ht => hdiffAt t (Set.Ioo_subset_Ioo le_rfl hxL.le ht)) hI0x
    have hFTC2 : (∫ t in x..(Real.pi / 2), deriv f t) = f (Real.pi / 2) - f x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxL.le
        (hcont.mono (Set.Icc_subset_Icc hx0.le le_rfl))
        (fun t ht => hdiffAt t (Set.Ioo_subset_Ioo hx0.le le_rfl ht)) hIxL
    have hA : |f x| ≤ ∫ t in (0 : ℝ)..x, |deriv f t| := by
      have hgoal : f x = ∫ t in (0 : ℝ)..x, deriv f t := by rw [hFTC1, hf0, sub_zero]
      calc |f x| = |∫ t in (0 : ℝ)..x, deriv f t| := by rw [hgoal]
        _ ≤ ∫ t in (0 : ℝ)..x, |deriv f t| :=
            intervalIntegral.abs_integral_le_integral_abs hx0.le
    have hA' : |f x| ≤ ∫ t in x..(Real.pi / 2), |deriv f t| := by
      have hgoal : f x = -(∫ t in x..(Real.pi / 2), deriv f t) := by
        rw [hFTC2, hfL]
        ring
      calc |f x| = |∫ t in x..(Real.pi / 2), deriv f t| := by rw [hgoal, abs_neg]
        _ ≤ ∫ t in x..(Real.pi / 2), |deriv f t| :=
            intervalIntegral.abs_integral_le_integral_abs hxL.le
    have hIabs0x : IntervalIntegrable (fun t => |deriv f t|) volume 0 x :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hx0.le).mpr
        (hderivf_abs.mono_set (Set.Icc_subset_Icc le_rfl hxL.le))
    have hIabsxL : IntervalIntegrable (fun t => |deriv f t|) volume x (Real.pi / 2) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hxL.le).mpr
        (hderivf_abs.mono_set (Set.Icc_subset_Icc hx0.le le_rfl))
    have hadd := intervalIntegral.integral_add_adjacent_intervals hIabs0x hIabsxL
    have hconv : (∫ t in (0 : ℝ)..(Real.pi / 2), |deriv f t|)
        = ∫ s in Work.Spaces.Iθ, |deriv f s| := integral_of_le_pi2 _
    linarith [hA, hA', hadd, hconv]
  -- ## Cauchy–Schwarz for `A₁ = ∫_{Iθ} |f'|`
  have hA1sq : (∫ s in Work.Spaces.Iθ, |deriv f s|) ^ 2
      ≤ (Real.pi / 2) * B := by
    have h1 : IntervalIntegrable (fun t => |deriv f t|) volume 0 (Real.pi / 2) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hpi.le).mpr hderivf_abs
    have h2 : IntervalIntegrable (fun t => (|deriv f t|) ^ 2) volume 0 (Real.pi / 2) := by
      have e : (fun t => (|deriv f t|) ^ 2) = (fun t => (deriv f t) ^ 2) := by
        funext t
        rw [sq_abs]
      rw [e]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hpi.le).mpr hBsq_int
    have hcs := Work.FTS.EllipticEst.remov.coerc.sq_intervalIntegral_le hpi.le h1 h2
    have e1 : (∫ t in (0 : ℝ)..(Real.pi / 2), |deriv f t|)
        = ∫ s in Work.Spaces.Iθ, |deriv f s| := integral_of_le_pi2 _
    have e2 : (∫ t in (0 : ℝ)..(Real.pi / 2), (|deriv f t|) ^ 2) = B := by
      have e : (fun t => (|deriv f t|) ^ 2) = (fun t => (deriv f t) ^ 2) := by
        funext t
        rw [sq_abs]
      rw [e, integral_of_le_pi2, ← hBdef]
    rw [e1, e2, sub_zero] at hcs
    exact hcs
  -- ## pointwise bound for `f²`
  have hfsq_pt : ∀ x ∈ Set.Ioo 0 (Real.pi / 2),
      (f x) ^ 2 ≤ (Real.pi / 2) * B / 4 := by
    intro x hx
    have h1 : |f x| ≤ (1 / 2) * ∫ s in Work.Spaces.Iθ, |deriv f s| := hfbd x hx
    have h2 : (f x) ^ 2 ≤ ((1 / 2) * ∫ s in Work.Spaces.Iθ, |deriv f s|) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h3 : ((1 / 2) * ∫ s in Work.Spaces.Iθ, |deriv f s|) ^ 2
        = (1 / 4) * (∫ s in Work.Spaces.Iθ, |deriv f s|) ^ 2 := by ring
    have h4 : (1 / 4) * (∫ s in Work.Spaces.Iθ, |deriv f s|) ^ 2
        ≤ (1 / 4) * ((Real.pi / 2) * B) :=
      mul_le_mul_of_nonneg_left hA1sq (by norm_num)
    linarith [h2, h4]
  -- ## integrate the pointwise bound for `f²`
  have hfsq_int : IntegrableOn (fun θ => (f θ) ^ 2) Work.Spaces.Iθ :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hpi.le).mp
      (ContinuousOn.intervalIntegrable (by
        rw [Set.uIcc_of_le hpi.le]
        exact hcont.pow 2))
  have hfsq_le : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2) ≤ (Real.pi / 2) ^ 2 * B / 4 := by
    have hae : (fun θ => (f θ) ^ 2) ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun _ : ℝ => (Real.pi / 2) * B / 4) := ae_Iθ_of_Ioo hfsq_pt
    have hmono := MeasureTheory.integral_mono_ae hfsq_int
      (integrableOn_const_Iθ ((Real.pi / 2) * B / 4)) hae
    calc (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2)
        ≤ ∫ _ in Work.Spaces.Iθ, (Real.pi / 2) * B / 4 := hmono
      _ = (Real.pi / 2) * ((Real.pi / 2) * B / 4) := setIntegral_const_Iθ _
      _ = (Real.pi / 2) ^ 2 * B / 4 := by ring
  -- ## arithmetic
  have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hpi4 : Real.pi ^ 4 ≤ 256 := by nlinarith [Real.pi_pos, hpi2]
  have hB_le' : B ≤ (Real.pi / 2) ^ 2 * C := by
    calc B ≤ (Real.pi / 2) * M ^ 2 := hB_le
      _ ≤ (Real.pi / 2) * ((Real.pi / 2) * C) :=
          mul_le_mul_of_nonneg_left hM2_le hpi.le
      _ = (Real.pi / 2) ^ 2 * C := by ring
  constructor
  · calc (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2) ≤ (Real.pi / 2) ^ 2 * B / 4 := hfsq_le
      _ ≤ (Real.pi / 2) ^ 2 * ((Real.pi / 2) ^ 2 * C) / 4 := by
          have hBnn : 0 ≤ B := by
            rw [hBdef]
            exact MeasureTheory.integral_nonneg (f := fun θ => (deriv f θ) ^ 2)
              (fun _ => sq_nonneg _)
          have : (Real.pi / 2) ^ 2 * B ≤ (Real.pi / 2) ^ 2 * ((Real.pi / 2) ^ 2 * C) :=
            mul_le_mul_of_nonneg_left hB_le' (by positivity)
          linarith
      _ = Real.pi ^ 4 * C / 64 := by ring
      _ ≤ 4 * C := by nlinarith [hCnn, hpi4]
  · calc (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2) ≤ (Real.pi / 2) ^ 2 * C := hB_le'
      _ ≤ 4 * C := by nlinarith [hCnn, hpi2]
      _ = 4 * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2) := by rw [hCdef]

end Work.FTS.EllipticEst.H2W
