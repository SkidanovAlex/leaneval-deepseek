import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.DivSinDefs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.sliceLimitLeftExists
import Submission.Work.Spaces.cs_integral
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Elementary angular facts -/

theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem sEta_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

/-- On the open interval the weight `sEta θ = sin(2θ)^{-η}` is at least `1`. -/
theorem one_le_sEta_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have heta : -(Work.Spaces.eta) ≤ (0 : ℝ) := by rw [Work.Spaces.eta]; norm_num
  have h := Real.rpow_le_rpow_of_exponent_ge hs0 hs1 heta
  simpa [Work.FTS.EllipticEst.sEta] using h

theorem integrableOn_sEta : IntegrableOn Work.FTS.EllipticEst.sEta Work.Spaces.Iθ :=
  Work.FTS.EllipticEst.integrableOn_thEta.1

theorem integral_sEta_le : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ) ≤ 10000 :=
  Work.FTS.EllipticEst.integrableOn_thEta.2

theorem integrableOn_sin_pow_eta :
    IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ Work.Spaces.eta) Work.Spaces.Iθ :=
  (Work.FTS.EllipticEst.integrableOn_sin_two_rpow (p := Work.Spaces.eta)
    (by rw [Work.Spaces.eta]; norm_num)).1

theorem integral_sin_pow_eta_le :
    (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ Work.Spaces.eta) ≤ Real.pi / 2 :=
  (Work.FTS.EllipticEst.integrableOn_sin_two_rpow (p := Work.Spaces.eta)
    (by rw [Work.Spaces.eta]; norm_num)).2

/-- The restricted measures of `Iθ` and of the open interval agree (they differ by the two
endpoints). -/
theorem restrict_Iθ_eq_restrict_Ioo :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo 0 (Real.pi / 2)) :=
  MeasureTheory.Measure.restrict_congr_set (by
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Ioo_ae_eq_Icc).symm)

/-- A function continuous on the open interval is a.e.-strongly measurable for the measure
restricted to `Iθ`. -/
theorem aestronglyMeasurable_of_continuousOn_Ioo {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable f (volume.restrict Work.Spaces.Iθ) := by
  rw [restrict_Iθ_eq_restrict_Ioo]
  exact hf.aestronglyMeasurable measurableSet_Ioo

/-! ## The comparison of the `sGam`-integrand with the `sEta`-integrand -/

/-- Pointwise on `Iθ`, the final integrand `(D_θ u)² · sGam α` equals `u'² sin(2θ)^{2-γ}` and is
dominated by `u'² · sEta = u'² sin(2θ)^{-η}`, since `-η ≤ 2 - γ` (for `α ≤ 1/4`) and
`sin(2θ) ≤ 1`. -/
theorem dth1Iter_one_sq_mul_sGam_le (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (u : ℝ → ℝ) :
    ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ
        ≤ (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  intro θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  rw [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1Iter_zero, Work.Elliptic.Dth1]
  have hmain : (Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rcases eq_or_lt_of_le hs0 with hzero | hpos
    · rw [← hzero,
        Real.zero_rpow (by rw [Work.Spaces.gam]; linarith : -(Work.Spaces.gam α) ≠ 0),
        Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num : -(Work.Spaces.eta) ≠ 0)]
      norm_num
    · have hkey : (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        refine Real.rpow_le_rpow_of_exponent_ge hpos hs1 ?_
        rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
      rw [(Real.rpow_natCast (Real.sin (2 * θ)) 2).symm, ← Real.rpow_add hpos,
        show (((2 : ℕ)) : ℝ) + -(Work.Spaces.gam α) = 2 - Work.Spaces.gam α by ring]
      exact hkey
  calc (Real.sin (2 * θ) * deriv u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ
      = (deriv u θ) ^ 2
          * ((Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
        simp only [Work.FTS.EllipticEst.sGam]; ring
    _ ≤ (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        mul_le_mul_of_nonneg_left hmain (sq_nonneg _)
    _ = (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
        simp only [Work.FTS.EllipticEst.sEta]

/-! ## Integrability and size of the derivatives of a slice with finite weighted second moment -/

theorem integrableOn_deriv2_sq {u : ℝ → ℝ}
    (h2 : IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
  Work.FTS.EllipticEst.sliceLim_integrableOn_sq_of_integrableOn_mul_sEta u h2

theorem integrableOn_deriv2_sq_Iθ {u : ℝ → ℝ}
    (h2 : IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2) Work.Spaces.Iθ :=
  (integrableOn_deriv2_sq h2).congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc).symm

theorem integrableOn_abs_deriv2 {u : ℝ → ℝ}
    (h2 : IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    IntegrableOn (fun θ => |deriv (fun t => deriv u t) θ|) (Set.Ioo 0 (Real.pi / 2)) :=
  Work.FTS.EllipticEst.sliceLim_integrableOn_abs_of_integrableOn_sq u
    (integrableOn_deriv2_sq h2)

theorem integrableOn_abs_deriv2_Iθ {u : ℝ → ℝ}
    (h2 : IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    IntegrableOn (fun θ => |deriv (fun t => deriv u t) θ|) Work.Spaces.Iθ :=
  (integrableOn_abs_deriv2 h2).congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc).symm

/-- `u''` is continuous on the open interval `(0, π/2)`. -/
theorem continuousOn_deriv2 {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (fun θ => deriv (fun t => deriv u t) θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hIoo : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.deriv_of_isOpen hIoo (m := 1) (by norm_num)
  exact contDiffOn_zero.1 (hd1.deriv_of_isOpen hIoo (m := 0) (by norm_num))

/-- `u'` is continuous on the open interval `(0, π/2)`. -/
theorem continuousOn_deriv {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
  (hu.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).continuousOn

theorem integrableOn_deriv2 {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h2 : IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    IntegrableOn (fun θ => deriv (fun t => deriv u t) θ) Work.Spaces.Iθ := by
  have hAbs := integrableOn_abs_deriv2_Iθ h2
  rw [MeasureTheory.IntegrableOn] at hAbs ⊢
  exact (MeasureTheory.integrable_norm_iff
    (aestronglyMeasurable_of_continuousOn_Ioo (continuousOn_deriv2 hu))).mp
    (by simpa [Real.norm_eq_abs] using hAbs)

/-- Since `sEta ≥ 1` a.e. on `Iθ`, the unweighted square of `u''` is dominated by the weighted one. -/
theorem integral_deriv2_sq_le {u : ℝ → ℝ}
    (h2 : IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2)
      ≤ (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) := by
  refine integral_mono_of_nonneg (Eventually.of_forall (fun θ => sq_nonneg _)) h2 ?_
  show ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    (deriv (fun t => deriv u t) θ) ^ 2
      ≤ (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
  have h := Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
    (p := fun θ => (deriv (fun t => deriv u t) θ) ^ 2
      ≤ (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
    (fun θ hθ => by
      have h1 := one_le_sEta_of_mem hθ
      nlinarith [sq_nonneg (deriv (fun t => deriv u t) θ)])
  simpa [Work.Spaces.Iθ] using h

/-- Cauchy–Schwarz on `Iθ`: `(∫ |u''|)² ≤ (π/2) ∫ (u'')² ≤ (π/2) ∫ (u'')² sEta`. -/
theorem abs_deriv2_sq_le {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h2 : IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, |deriv (fun t => deriv u t) θ|) ^ 2
      ≤ (Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) := by
  have hvol : (volume : Measure ℝ).real Work.Spaces.Iθ = Real.pi / 2 := by
    rw [MeasureTheory.measureReal_def,
      show (volume : Measure ℝ) Work.Spaces.Iθ = ENNReal.ofReal (Real.pi / 2) from by
        rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl, Real.volume_Icc,
          sub_zero],
      ENNReal.toReal_ofReal (by positivity)]
  have hsq : IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2) Work.Spaces.Iθ :=
    integrableOn_deriv2_sq_Iθ h2
  have hm1 : MemLp (fun θ => |deriv (fun t => deriv u t) θ|) 2
      (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq
      (aestronglyMeasurable_of_continuousOn_Ioo (continuousOn_deriv2 hu).abs)).2
      (by
        rw [MeasureTheory.IntegrableOn] at hsq
        simpa [sq_abs] using hsq)
  have hm2 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq aestronglyMeasurable_const).2
      (integrableOn_const (by
        rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hcs := Work.Spaces.cs_integral (s := Work.Spaces.Iθ) hm1 hm2
  have hcs' : (∫ θ in Work.Spaces.Iθ, |deriv (fun t => deriv u t) θ|) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2) * (Real.pi / 2) := by
    simpa [mul_one, sq_abs, hvol] using hcs
  have hle := integral_deriv2_sq_le h2
  calc (∫ θ in Work.Spaces.Iθ, |deriv (fun t => deriv u t) θ|) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2) * (Real.pi / 2) := hcs'
    _ ≤ (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) * (Real.pi / 2) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
    _ = (Real.pi / 2) * (∫ θ in Work.Spaces.Iθ,
          (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by ring

/-- The modulus of `u'` is bounded by its value at `π/4` plus the total (unweighted) mass of
`u''`: Newton–Leibniz on the interval joining `s` to `π/4`. -/
theorem deriv_sub_le_abs_deriv2 {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h2 : IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv u s - deriv u (Real.pi / 4)|
        ≤ ∫ θ in Work.Spaces.Iθ, |deriv (fun t => deriv u t) θ| := by
  have hderiv2 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv u) (deriv (fun t : ℝ => deriv u t) x) x := by
    intro x hx
    have h2' : ContDiffAt ℝ 2 u x := hu.contDiffAt (isOpen_Ioo.mem_nhds hx)
    have hd1 : ContDiffAt ℝ 1 (deriv u) x := h2'.derivWithin (by norm_num)
    exact (hd1.differentiableAt (by norm_num)).hasDerivAt
  have hAbsIθ : IntegrableOn (fun θ => |deriv (fun t => deriv u t) θ|) Work.Spaces.Iθ :=
    integrableOn_abs_deriv2_Iθ h2
  have hD2Iθ : IntegrableOn (fun θ => deriv (fun t => deriv u t) θ) Work.Spaces.Iθ :=
    integrableOn_deriv2 hu h2
  intro s hs
  rcases le_total (Real.pi / 4) s with hge | hle
  · have hFTC : ∫ x in (Real.pi / 4)..s, deriv (fun t => deriv u t) x
        = deriv u s - deriv u (Real.pi / 4) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) ?_
      · rw [Set.uIcc_of_le hge] at hx
        exact hderiv2 x ⟨lt_of_lt_of_le (by linarith [Real.pi_pos]) hx.1,
          lt_of_le_of_lt hx.2 hs.2⟩
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hge]
        exact hD2Iθ.mono_set (fun x hx => ⟨le_of_lt (lt_trans (by linarith [Real.pi_pos]) hx.1),
          le_of_lt (lt_of_le_of_lt hx.2 hs.2)⟩)
    have hstep1 : |deriv u s - deriv u (Real.pi / 4)|
        = |∫ x in (Real.pi / 4)..s, deriv (fun t => deriv u t) x| := by rw [hFTC]
    have hstep2 : |∫ x in (Real.pi / 4)..s, deriv (fun t => deriv u t) x|
        ≤ ∫ x in (Real.pi / 4)..s, |deriv (fun t => deriv u t) x| :=
      intervalIntegral.abs_integral_le_integral_abs hge
    have hstep3 : (∫ x in (Real.pi / 4)..s, |deriv (fun t => deriv u t) x|)
        ≤ ∫ θ in Work.Spaces.Iθ, |deriv (fun t => deriv u t) θ| := by
      rw [intervalIntegral.integral_of_le hge]
      exact MeasureTheory.setIntegral_mono_set hAbsIθ
        (Eventually.of_forall fun _ => abs_nonneg _)
        (Eventually.of_forall fun x hx =>
          ⟨le_of_lt (lt_trans (by linarith [Real.pi_pos]) hx.1),
            le_of_lt (lt_of_le_of_lt hx.2 hs.2)⟩)
    exact le_trans (le_of_eq hstep1) (le_trans hstep2 hstep3)
  · have hFTC : ∫ x in s..(Real.pi / 4), deriv (fun t => deriv u t) x
        = deriv u (Real.pi / 4) - deriv u s := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) ?_
      · rw [Set.uIcc_of_le hle] at hx
        exact hderiv2 x ⟨lt_of_lt_of_le hs.1 hx.1,
          lt_of_le_of_lt hx.2 (by linarith [Real.pi_pos])⟩
      · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
        exact hD2Iθ.mono_set (fun x hx => ⟨le_of_lt (lt_trans hs.1 hx.1),
          le_of_lt (lt_of_le_of_lt hx.2 (by linarith [Real.pi_pos]))⟩)
    have hneg : |deriv u s - deriv u (Real.pi / 4)|
        = |∫ x in s..(Real.pi / 4), deriv (fun t => deriv u t) x| := by
      rw [hFTC, abs_sub_comm]
    have hstep2 : |∫ x in s..(Real.pi / 4), deriv (fun t => deriv u t) x|
        ≤ ∫ x in s..(Real.pi / 4), |deriv (fun t => deriv u t) x| :=
      intervalIntegral.abs_integral_le_integral_abs hle
    have hstep3 : (∫ x in s..(Real.pi / 4), |deriv (fun t => deriv u t) x|)
        ≤ ∫ θ in Work.Spaces.Iθ, |deriv (fun t => deriv u t) θ| := by
      rw [intervalIntegral.integral_of_le hle]
      exact MeasureTheory.setIntegral_mono_set hAbsIθ
        (Eventually.of_forall fun _ => abs_nonneg _)
        (Eventually.of_forall fun x hx =>
          ⟨le_of_lt (lt_trans hs.1 hx.1),
            le_of_lt (lt_of_le_of_lt hx.2 (by linarith [Real.pi_pos]))⟩)
    exact le_trans (le_of_eq hneg) (le_trans hstep2 hstep3)

/-! ## Finiteness of the weighted `L²`-norm of the slice itself -/

/-- `sEta` is a.e.-strongly measurable on `Iθ`. -/
theorem aestronglyMeasurable_sEta :
    AEStronglyMeasurable (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ)
      (volume.restrict Work.Spaces.Iθ) := by
  refine aestronglyMeasurable_of_continuousOn_Ioo ?_
  have hsin : Continuous (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hne : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * x) ≠ 0 := fun x hx =>
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
      (by linarith [hx.2, Real.pi_pos]))
  simpa only [Work.FTS.EllipticEst.sEta] using
    hsin.continuousOn.rpow_const (fun x hx => Or.inl (hne x hx))

/-- Lagrange mean-value bound: if `u` is continuous on `[a,b]`, differentiable on `(a,b)` and
`|u'| ≤ M` there, then `|u b - u a| ≤ (b - a) M`. -/
theorem abs_sub_le_mul_of_deriv_bound {u : ℝ → ℝ} {M a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn u (Set.Icc a b)) (hdiff : DifferentiableOn ℝ u (Set.Ioo a b))
    (hbd : ∀ x ∈ Set.Ioo a b, |deriv u x| ≤ M) :
    |u b - u a| ≤ (b - a) * M := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope u hlt hcont hdiff
    have hcb : 0 < b - a := sub_pos.mpr hlt
    have h2 : u b - u a = (b - a) * deriv u c := by rw [hcd]; field_simp
    rw [h2, abs_mul, abs_of_pos hcb]
    exact mul_le_mul_of_nonneg_left (hbd c hc) (le_of_lt hcb)
  · rw [heq]; simp

/-- **Finiteness.**  If `(u'')² sEta` is integrable on `Iθ` for a slice `u` which is `C²` on the
open interval, then `u` is bounded (by `|u (π/4)| + (|u' (π/4)| + ∫|u''|)·(π/2)`) and hence
`u² sEta` is integrable as well. -/
theorem u_sq_mul_sEta_integrable {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h2 : IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  have hAnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, |deriv (fun t => deriv u t) θ| :=
    setIntegral_nonneg measurableSet_Icc (fun θ _ => abs_nonneg _)
  have hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv u s - deriv u (Real.pi / 4)|
        ≤ ∫ θ in Work.Spaces.Iθ, |deriv (fun t => deriv u t) θ| :=
    deriv_sub_le_abs_deriv2 hu h2
  set M : ℝ := |deriv u (Real.pi / 4)| + ∫ θ in Work.Spaces.Iθ,
    |deriv (fun t => deriv u t) θ| with hMdef
  set B : ℝ := |u (Real.pi / 4)| + M * (Real.pi / 2) with hBdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]; exact add_nonneg (abs_nonneg _) hAnn
  have hderiv_bound : ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv u s| ≤ M := by
    intro s hs
    have h1 := hderiv s hs
    have h2' : deriv u s = (deriv u s - deriv u (Real.pi / 4)) + deriv u (Real.pi / 4) := by ring
    rw [h2', hMdef]
    have h3 := abs_add_le (deriv u s - deriv u (Real.pi / 4)) (deriv u (Real.pi / 4))
    linarith [h3, h1]
  have hbound : ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |u s| ≤ B := by
    intro s hs
    have key : ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
        |u b - u a| ≤ (b - a) * M := by
      intro a b hab hsub
      exact abs_sub_le_mul_of_deriv_bound hab (hu.continuousOn.mono hsub)
        ((hu.differentiableOn (by norm_num)).mono (fun x hx => hsub ⟨hx.1.le, hx.2.le⟩))
        (fun x hx => hderiv_bound x (hsub ⟨hx.1.le, hx.2.le⟩))
    rcases le_total s (Real.pi / 4) with hle | hge
    · have hsub : Set.Icc s (Real.pi / 4) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
        ⟨lt_of_lt_of_le hs.1 hx.1, lt_of_le_of_lt hx.2 (by linarith [Real.pi_pos])⟩
      have h := key s (Real.pi / 4) hle hsub
      have h3 : |u s - u (Real.pi / 4)| ≤ (Real.pi / 4 - s) * M := by
        simpa [abs_sub_comm] using h
      have h4 := abs_add_le (u s - u (Real.pi / 4)) (u (Real.pi / 4))
      have h5 : u s = (u s - u (Real.pi / 4)) + u (Real.pi / 4) := by ring
      have hlen : Real.pi / 4 - s ≤ Real.pi / 2 := by linarith [hs.1]
      have h6 := mul_le_mul_of_nonneg_right hlen hMnn
      rw [hBdef, h5]
      linarith [h4, h3, h6]
    · have hsub : Set.Icc (Real.pi / 4) s ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
        ⟨lt_of_lt_of_le (by linarith [Real.pi_pos]) hx.1, lt_of_le_of_lt hx.2 hs.2⟩
      have h := key (Real.pi / 4) s hge hsub
      have h4 := abs_add_le (u s - u (Real.pi / 4)) (u (Real.pi / 4))
      have h5 : u s = (u s - u (Real.pi / 4)) + u (Real.pi / 4) := by ring
      have hlen : s - Real.pi / 4 ≤ Real.pi / 2 := by linarith [hs.2]
      have h6 := mul_le_mul_of_nonneg_right hlen hMnn
      rw [hBdef, h5]
      linarith [h4, h, h6]
  have hcomp : IntegrableOn (fun θ => B ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    integrableOn_sEta.const_mul _
  refine hcomp.mono' ?_ ?_
  · have ru : AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ) :=
      aestronglyMeasurable_of_continuousOn_Ioo hu.continuousOn
    exact (ru.pow 2).mul aestronglyMeasurable_sEta
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · have hse : Work.FTS.EllipticEst.sEta θ = 0 := by
        rw [← h0, Work.FTS.EllipticEst.sEta, show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
        exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
      rw [hse, mul_zero, mul_zero, Real.norm_eq_abs, abs_zero]
    · rcases eq_or_lt_of_le hθ.2 with h1 | h1
      · have hse : Work.FTS.EllipticEst.sEta θ = 0 := by
          rw [h1, Work.FTS.EllipticEst.sEta,
            show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
          exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
        rw [hse, mul_zero, mul_zero, Real.norm_eq_abs, abs_zero]
      · have hs : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h0, h1⟩
        have hsq : (u θ) ^ 2 ≤ B ^ 2 := by
          have h := mul_self_le_mul_self (abs_nonneg (u θ)) (hbound θ hs)
          simpa [sq, sq_abs] using h
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (sq_nonneg _) (sEta_nonneg_of_mem_Iθ hθ))]
        exact mul_le_mul_of_nonneg_right hsq (sEta_nonneg_of_mem_Iθ hθ)

/-! ## The weighted interpolation, given the pivot bound at `π/4` -/

/-- **Weighted interpolation.**  If the pivot bound `(u' (π/4))² ≤ Cp (∫u²sEta + ∫(u'')²sEta)`
holds with a constant `Cp` for every admissible `u`, then `∫u'²sEta` is finite and bounded by a
fixed multiple of `∫u²sEta + ∫(u'')²sEta`.  The point is that `c = u' (π/4)` controls `u'`
everywhere up to `A = ∫|u''| ≤ √(π/2)·√E`. -/
theorem deriv_sq_mul_sEta_le (Cp : ℝ) (hCp : 0 < Cp)
    (hpiv : ∀ (u : ℝ → ℝ), ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) →
      IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      (deriv u (Real.pi / 4)) ^ 2
        ≤ Cp * ((∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)))
    (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h0 : IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ)
    (h2 : IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    IntegrableOn (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ (20000 * Cp + 10000 * Real.pi + 1)
          * ((∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)) := by
  set P : ℝ := ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hPdef
  set E : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
    * Work.FTS.EllipticEst.sEta θ with hEdef
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, |deriv (fun t => deriv u t) θ| with hAdef
  set c : ℝ := deriv u (Real.pi / 4) with hcdef
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_of_mem_Iθ hθ))
  have hEnn : 0 ≤ E := by
    rw [hEdef]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_of_mem_Iθ hθ))
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact setIntegral_nonneg measurableSet_Icc (fun θ _ => abs_nonneg _)
  have hA2 : A ^ 2 ≤ (Real.pi / 2) * E := abs_deriv2_sq_le hu h2
  have hc2 : c ^ 2 ≤ Cp * (P + E) := by
    have h := hpiv u hu h0 h2
    rw [hPdef, hEdef, hcdef]
    exact h
  -- pointwise bound `(u')² ≤ 2A² + 2c²` on the open interval
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (deriv u θ) ^ 2 ≤ 2 * A ^ 2 + 2 * c ^ 2 := by
    intro θ hθ
    have h1 : |deriv u θ - c| ≤ A := by
      rw [hcdef, hAdef]
      exact deriv_sub_le_abs_deriv2 hu h2 θ hθ
    have h2' : (deriv u θ - c) ^ 2 ≤ A ^ 2 := by
      have h := mul_self_le_mul_self (abs_nonneg (deriv u θ - c)) h1
      simpa [sq, sq_abs] using h
    have h3 : (deriv u θ) ^ 2 = ((deriv u θ - c) + c) ^ 2 := by ring
    rw [h3]
    nlinarith [sq_nonneg ((deriv u θ - c) - c), h2']
  have hptae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (deriv u θ) ^ 2 ≤ 2 * A ^ 2 + 2 * c ^ 2 := by
    have h := Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
      (p := fun θ => (deriv u θ) ^ 2 ≤ 2 * A ^ 2 + 2 * c ^ 2) hpt
    simpa [Work.Spaces.Iθ] using h
  have hnn : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (sEta_nonneg_of_mem_Iθ hθ)
  have hgm : (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (2 * A ^ 2 + 2 * c ^ 2) * Work.FTS.EllipticEst.sEta θ) := by
    filter_upwards [hptae, MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ h1 h2'
    exact mul_le_mul_of_nonneg_right h1 (sEta_nonneg_of_mem_Iθ h2')
  have hcomp : IntegrableOn (fun θ => (2 * A ^ 2 + 2 * c ^ 2)
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    integrableOn_sEta.const_mul _
  have hInt : IntegrableOn (fun θ => (deriv u θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    refine hcomp.mono' ?_ ?_
    · have r1 : AEStronglyMeasurable (deriv u) (volume.restrict Work.Spaces.Iθ) :=
        aestronglyMeasurable_of_continuousOn_Ioo (continuousOn_deriv hu)
      have r2 : AEStronglyMeasurable (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ)
          (volume.restrict Work.Spaces.Iθ) := by
        refine aestronglyMeasurable_of_continuousOn_Ioo ?_
        have hsin : Continuous (fun θ : ℝ => Real.sin (2 * θ)) :=
          Real.continuous_sin.comp (continuous_const.mul continuous_id)
        have hne : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * x) ≠ 0 := by
          intro x hx
          exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
            (by linarith [hx.2, Real.pi_pos]))
        simpa only [Work.FTS.EllipticEst.sEta] using
          hsin.continuousOn.rpow_const (fun x hx => Or.inl (hne x hx))
      exact (r1.pow 2).mul r2
    · filter_upwards [hgm, MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ h1 h2'
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sEta_nonneg_of_mem_Iθ h2'))]
      exact h1
  refine ⟨hInt, ?_⟩
  have hIntle : (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ (2 * A ^ 2 + 2 * c ^ 2) * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ) := by
    have h := integral_mono_of_nonneg hnn hcomp hgm
    rwa [MeasureTheory.integral_const_mul] at h
  have hK := integral_sEta_le
  have hKnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => sEta_nonneg_of_mem_Iθ hθ)
  have hcoef : 2 * A ^ 2 + 2 * c ^ 2 ≤ 2 * ((Real.pi / 2) * E) + 2 * (Cp * (P + E)) := by
    nlinarith [hA2, hc2]
  calc (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ (2 * A ^ 2 + 2 * c ^ 2) * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ) :=
        hIntle
    _ ≤ (2 * ((Real.pi / 2) * E) + 2 * (Cp * (P + E))) * 10000 := by
        have hb : 0 ≤ 2 * ((Real.pi / 2) * E) + 2 * (Cp * (P + E)) := by
          refine add_nonneg ?_ ?_
          · exact mul_nonneg (by norm_num) (mul_nonneg (by positivity) hEnn)
          · exact mul_nonneg (by norm_num) (mul_nonneg hCp.le (add_nonneg hPnn hEnn))
        exact mul_le_mul hcoef hK hKnn hb
    _ ≤ (20000 * Cp + 10000 * Real.pi + 1) * (P + E) := by
        have e1 : 2 * ((Real.pi / 2) * E) ≤ Real.pi * (P + E) := by
          nlinarith [hPnn, hEnn, Real.pi_pos]
        have e2 : 2 * (Cp * (P + E)) ≤ 20000 * Cp * (P + E) := by
          nlinarith [hCp, hPnn, hEnn]
        nlinarith [e1, e2, hPnn, hEnn, hCp]

/-! ## Auxiliary lemmas for the pivot bound -/

/-- `sEta` is continuous on any subinterval of the open quadrant. -/
theorem continuousOn_sEta_of_subset {a b : ℝ}
    (hsub : Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ) (Set.Ioo a b) := by
  have hsin : Continuous (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hne : ∀ x ∈ Set.Ioo a b, Real.sin (2 * x) ≠ 0 := fun x hx =>
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [(hsub hx).1])
      (by linarith [(hsub hx).2, Real.pi_pos]))
  simpa only [Work.FTS.EllipticEst.sEta] using
    hsin.continuousOn.rpow_const (fun x hx => Or.inl (hne x hx))

/-- Cauchy–Schwarz for the weighted `L¹`-norm of a slice:
`(∫_s |u| sEta)² ≤ (∫_s u² sEta)·(∫_s sEta)`. -/
theorem abs_mul_sEta_sq_le {s : Set ℝ} (hs : MeasurableSet s) (hsub : s ⊆ Work.Spaces.Iθ)
    {u : ℝ → ℝ}
    (h1 : IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) s)
    (h2 : IntegrableOn Work.FTS.EllipticEst.sEta s)
    (haesm1 : AEStronglyMeasurable
      (fun θ => Real.sqrt ((u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) (volume.restrict s))
    (haesm2 : AEStronglyMeasurable
      (fun θ => Real.sqrt (Work.FTS.EllipticEst.sEta θ)) (volume.restrict s)) :
    (∫ θ in s, |u θ| * Work.FTS.EllipticEst.sEta θ) ^ 2
      ≤ (∫ θ in s, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        * (∫ θ in s, Work.FTS.EllipticEst.sEta θ) := by
  have hσ_nn : ∀ᵐ θ ∂(volume.restrict s), 0 ≤ Work.FTS.EllipticEst.sEta θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem hs] with θ hθ
    exact sEta_nonneg_of_mem_Iθ (hsub hθ)
  have hsq1 : (fun θ => (Real.sqrt ((u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) ^ 2)
      =ᵐ[volume.restrict s] (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    filter_upwards [hσ_nn] with θ hθ
    exact Real.sq_sqrt (mul_nonneg (sq_nonneg _) hθ)
  have hsq2 : (fun θ => (Real.sqrt (Work.FTS.EllipticEst.sEta θ)) ^ 2)
      =ᵐ[volume.restrict s] Work.FTS.EllipticEst.sEta := by
    filter_upwards [hσ_nn] with θ hθ
    exact Real.sq_sqrt hθ
  have hprod : (fun θ => Real.sqrt ((u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        * Real.sqrt (Work.FTS.EllipticEst.sEta θ))
      =ᵐ[volume.restrict s] (fun θ => |u θ| * Work.FTS.EllipticEst.sEta θ) := by
    filter_upwards [hσ_nn] with θ hθ
    have hsq : (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ * Work.FTS.EllipticEst.sEta θ
        = (|u θ| * Work.FTS.EllipticEst.sEta θ) ^ 2 := by
      rw [mul_pow, sq_abs]
      ring
    rw [← Real.sqrt_mul (mul_nonneg (sq_nonneg _) hθ), hsq,
      Real.sqrt_sq (mul_nonneg (abs_nonneg _) hθ)]
  have hm1 : MemLp (fun θ => Real.sqrt ((u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) 2
      (volume.restrict s) :=
    (MeasureTheory.memLp_two_iff_integrable_sq haesm1).2 (h1.congr hsq1.symm)
  have hm2 : MemLp (fun θ => Real.sqrt (Work.FTS.EllipticEst.sEta θ)) 2
      (volume.restrict s) :=
    (MeasureTheory.memLp_two_iff_integrable_sq haesm2).2 (h2.congr hsq2.symm)
  have hcs := Work.Spaces.cs_integral (s := s) hm1 hm2
  rw [MeasureTheory.integral_congr_ae hprod, MeasureTheory.integral_congr_ae hsq1,
    MeasureTheory.integral_congr_ae hsq2] at hcs
  exact hcs

/-! ## The pivot bound -/

/-- **Pivot bound.**  For a slice `u` of class `C²` on the open interval with finite weighted
zeroth and second moments, the value of `u'` at the interior point `π/4` is controlled by
`∫u²sEta + ∫(u'')²sEta`.  The anchor for `u'` has to come from the `u²` term, since without
continuity of `u` at the endpoints the classical Rolle argument is unavailable. -/
theorem pivotBound : ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ → ℝ),
    ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) →
    IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
    IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
    (deriv u (Real.pi / 4)) ^ 2
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)) := by
  refine ⟨10 ^ 9, by norm_num, ?_⟩
  intro u hu h0 h2
  set P : ℝ := ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ with hPdef
  set E : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
    * Work.FTS.EllipticEst.sEta θ with hEdef
  set c : ℝ := deriv u (Real.pi / 4) with hcdef
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, |deriv (fun t => deriv u t) θ| with hAdef
  set Mtot : ℝ := ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ with hMtotdef
  set mL : ℝ := ∫ θ in Set.Ioo (0 : ℝ) (1 / 64), Work.FTS.EllipticEst.sEta θ with hmLdef
  set mR : ℝ := ∫ θ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
    Work.FTS.EllipticEst.sEta θ with hmRdef
  set KL : ℝ := ∫ θ in Set.Ioo (0 : ℝ) (1 / 64),
    |u θ| * Work.FTS.EllipticEst.sEta θ with hKLdef
  set KR : ℝ := ∫ θ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
    |u θ| * Work.FTS.EllipticEst.sEta θ with hKRdef
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_of_mem_Iθ hθ))
  have hEnn : 0 ≤ E := by
    rw [hEdef]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg_of_mem_Iθ hθ))
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact setIntegral_nonneg measurableSet_Icc (fun θ _ => abs_nonneg _)
  have hMtotle : Mtot ≤ 10000 := by rw [hMtotdef]; exact integral_sEta_le
  have hA2 : A ^ 2 ≤ (Real.pi / 2) * E := abs_deriv2_sq_le hu h2
  have hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv u s - c| ≤ A := by
    intro s hs; rw [hcdef, hAdef]; exact deriv_sub_le_abs_deriv2 hu h2 s hs
  -- integrability of `|u| sEta`
  have huσ : IntegrableOn (fun θ => |u θ| * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    have hg : IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
        + Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := h0.add integrableOn_sEta
    refine hg.mono' ?_ ?_
    · refine aestronglyMeasurable_of_continuousOn_Ioo ?_
      exact (hu.continuousOn.abs).mul (continuousOn_sEta_of_subset (fun x hx => hx))
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have hs := sEta_nonneg_of_mem_Iθ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hs)]
      have hsq : |u θ| ≤ ((u θ) ^ 2 + 1) / 2 := by
        nlinarith [sq_nonneg (|u θ| - 1), sq_abs (u θ)]
      nlinarith [hsq, hs, sq_nonneg (u θ)]
  have hσL : IntegrableOn Work.FTS.EllipticEst.sEta (Set.Ioo (0 : ℝ) (1 / 64)) :=
    integrableOn_sEta.mono_set (fun x hx => ⟨hx.1.le, by linarith [hx.2, Real.pi_gt_three]⟩)
  have hσR : IntegrableOn Work.FTS.EllipticEst.sEta
      (Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2)) :=
    integrableOn_sEta.mono_set (fun x hx => ⟨by linarith [hx.1, Real.pi_gt_three], hx.2.le⟩)
  have huσL : IntegrableOn (fun θ => |u θ| * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo (0 : ℝ) (1 / 64)) :=
    huσ.mono_set (fun x hx => ⟨hx.1.le, by linarith [hx.2, Real.pi_gt_three]⟩)
  have huσR : IntegrableOn (fun θ => |u θ| * Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2)) :=
    huσ.mono_set (fun x hx => ⟨by linarith [hx.1, Real.pi_gt_three], hx.2.le⟩)
  -- the two-point Taylor inequality
  have htwo : ∀ θ ∈ Set.Ioo (0 : ℝ) (1 / 64),
      ∀ φ ∈ Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
      |c| ≤ |u θ| + |u φ| + Real.pi * A := by
    intro θ hθ φ hφ
    have hθ2 : θ ≤ 1 / 64 := hθ.2.le
    have hφ1 : Real.pi / 2 - 1 / 64 ≤ φ := hφ.1.le
    have hθφ : θ ≤ φ := by linarith [hθ2, hφ1, Real.pi_gt_three]
    have hgap : 1 ≤ φ - θ := by linarith [hθ2, hφ1, Real.pi_gt_three]
    have hφI : φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨by linarith [hφ1, Real.pi_gt_three], hφ.2⟩
    have hsubseq : Set.Icc θ φ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
      ⟨lt_of_lt_of_le hθ.1 hx.1, lt_of_le_of_lt hx.2 hφI.2⟩
    have hderiv1 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt u (deriv u x) x := fun x hx =>
      ((hu.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt
    have hcont : ContinuousOn (deriv u) (Set.Icc θ φ) :=
      (continuousOn_deriv hu).mono hsubseq
    have hint : IntervalIntegrable (deriv u) volume θ φ :=
      hcont.intervalIntegrable_of_Icc hθφ
    have hFTC : ∫ x in θ..φ, deriv u x = u φ - u θ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => by
          rw [Set.uIcc_of_le hθφ, Set.mem_Icc] at hx
          exact hderiv1 x (hsubseq hx)) hint
    have hsplit : ∫ x in θ..φ, (deriv u x - c) = (u φ - u θ) - c * (φ - θ) := by
      rw [intervalIntegral.integral_sub hint intervalIntegrable_const, hFTC,
        intervalIntegral.integral_const]
      ring
    have hb1 : |∫ x in θ..φ, (deriv u x - c)| ≤ A * (φ - θ) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun x => deriv u x - c) (C := A) (fun x hx => by
          rw [Set.uIoc_of_le hθφ, Set.mem_Ioc] at hx
          exact hderiv x ⟨lt_trans hθ.1 hx.1, lt_of_le_of_lt hx.2 hφI.2⟩)
      simpa [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ φ - θ)] using h
    have hkey : |c| * (φ - θ) ≤ |u θ| + |u φ| + A * (φ - θ) := by
      have h1 : c * (φ - θ) = (u φ - u θ) - ∫ x in θ..φ, (deriv u x - c) := by
        rw [hsplit]; ring
      calc |c| * (φ - θ) = |c * (φ - θ)| := by
            rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ φ - θ)]
        _ = |(u φ - u θ) - ∫ x in θ..φ, (deriv u x - c)| := by rw [h1]
        _ ≤ |u φ - u θ| + |∫ x in θ..φ, (deriv u x - c)| := by
            simpa using abs_sub_le (u φ - u θ) 0 (∫ x in θ..φ, (deriv u x - c))
        _ ≤ (|u φ| + |u θ|) + A * (φ - θ) := by
            refine add_le_add ?_ hb1
            simpa using abs_sub_le (u φ) 0 (u θ)
        _ = |u θ| + |u φ| + A * (φ - θ) := by ring
    have h2' : |c| ≤ |u θ| + |u φ| + A * (φ - θ) := by
      have h3 : |c| * 1 ≤ |c| * (φ - θ) := mul_le_mul_of_nonneg_left hgap (abs_nonneg c)
      linarith [h3, hkey]
    have h4 : A * (φ - θ) ≤ Real.pi * A := by
      have h5 : φ - θ ≤ Real.pi := by linarith [hφ.2, hθ.1]
      nlinarith [h5, hAnn]
    linarith [h2', h4]
  -- mass bounds on the two strips
  have hsubL' : Set.Ioo (0 : ℝ) (1 / 64) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨hx.1, by linarith [hx.2, Real.pi_gt_three]⟩
  have hsubR' : Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨by linarith [hx.1, Real.pi_gt_three], hx.2⟩
  have hsubL : Set.Ioo (0 : ℝ) (1 / 64) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨hx.1.le, by linarith [hx.2, Real.pi_gt_three]⟩
  have hsubR : Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨by linarith [hx.1, Real.pi_gt_three], hx.2.le⟩
  have hmL_ge : 1 / 64 ≤ mL := by
    rw [hmLdef]
    have hone : (∫ θ in Set.Ioo (0 : ℝ) (1 / 64), (1 : ℝ)) = 1 / 64 := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioo]
      norm_num
    have hmono : (∫ θ in Set.Ioo (0 : ℝ) (1 / 64), (1 : ℝ))
        ≤ ∫ θ in Set.Ioo (0 : ℝ) (1 / 64), Work.FTS.EllipticEst.sEta θ := by
      refine integral_mono_of_nonneg (Eventually.of_forall (fun _ => by norm_num)) hσL ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact one_le_sEta_of_mem (hsubL' hθ)
    linarith [hmono, hone]
  have hmLnn : 0 ≤ mL := le_trans (by norm_num) hmL_ge
  have hmR_ge : 1 / 64 ≤ mR := by
    rw [hmRdef]
    have hone : (∫ θ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2), (1 : ℝ)) = 1 / 64 := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioo]
      norm_num
    have hmono : (∫ θ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2), (1 : ℝ))
        ≤ ∫ θ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
            Work.FTS.EllipticEst.sEta θ := by
      refine integral_mono_of_nonneg (Eventually.of_forall (fun _ => by norm_num)) hσR ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact one_le_sEta_of_mem (hsubR' hθ)
    linarith [hmono, hone]
  have hmRnn : 0 ≤ mR := le_trans (by norm_num) hmR_ge
  -- step: integrate the two-point inequality in `θ`
  have hstep2 : ∀ φ ∈ Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
      |c| * mL ≤ |u φ| * mL + KL + Real.pi * A * mL := by
    intro φ hφ
    have hG1 : IntegrableOn (fun θ => |u θ| * Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo (0 : ℝ) (1 / 64)) := huσL
    have hG2 : IntegrableOn (fun θ => |u φ| * Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo (0 : ℝ) (1 / 64)) := hσL.const_mul _
    have hG3 : IntegrableOn (fun θ => Real.pi * A * Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo (0 : ℝ) (1 / 64)) := hσL.const_mul _
    have hG23 : IntegrableOn (fun θ => |u φ| * Work.FTS.EllipticEst.sEta θ
        + Real.pi * A * Work.FTS.EllipticEst.sEta θ) (Set.Ioo (0 : ℝ) (1 / 64)) :=
      hG2.add hG3
    have hcomp : IntegrableOn
        (fun θ => (|u θ| + |u φ| + Real.pi * A) * Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo (0 : ℝ) (1 / 64)) := by
      have heq : (fun θ => (|u θ| + |u φ| + Real.pi * A) * Work.FTS.EllipticEst.sEta θ)
          = fun θ => |u θ| * Work.FTS.EllipticEst.sEta θ
            + (|u φ| * Work.FTS.EllipticEst.sEta θ
              + Real.pi * A * Work.FTS.EllipticEst.sEta θ) := by funext θ; ring
      rw [heq]
      exact hG1.add hG23
    have hle : (∫ θ in Set.Ioo (0 : ℝ) (1 / 64), |c| * Work.FTS.EllipticEst.sEta θ)
        ≤ ∫ θ in Set.Ioo (0 : ℝ) (1 / 64),
            (|u θ| + |u φ| + Real.pi * A) * Work.FTS.EllipticEst.sEta θ := by
      refine integral_mono_of_nonneg ?_ hcomp ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
        exact mul_nonneg (abs_nonneg _) (sEta_nonneg_of_mem_Iθ (hsubL hθ))
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
        exact mul_le_mul_of_nonneg_right (htwo θ hθ φ hφ) (sEta_nonneg_of_mem_Iθ (hsubL hθ))
    have e1 : (∫ θ in Set.Ioo (0 : ℝ) (1 / 64), |c| * Work.FTS.EllipticEst.sEta θ)
        = |c| * mL := by rw [MeasureTheory.integral_const_mul, ← hmLdef]
    have e2 : (∫ θ in Set.Ioo (0 : ℝ) (1 / 64),
          (|u θ| + |u φ| + Real.pi * A) * Work.FTS.EllipticEst.sEta θ)
        = KL + |u φ| * mL + Real.pi * A * mL := by
      have step1 : (∫ θ in Set.Ioo (0 : ℝ) (1 / 64),
            (|u θ| + |u φ| + Real.pi * A) * Work.FTS.EllipticEst.sEta θ)
          = (∫ θ in Set.Ioo (0 : ℝ) (1 / 64), |u θ| * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Set.Ioo (0 : ℝ) (1 / 64), |u φ| * Work.FTS.EllipticEst.sEta θ
                + Real.pi * A * Work.FTS.EllipticEst.sEta θ) := by
        rw [show (fun θ => (|u θ| + |u φ| + Real.pi * A) * Work.FTS.EllipticEst.sEta θ)
            = fun θ => |u θ| * Work.FTS.EllipticEst.sEta θ
              + (|u φ| * Work.FTS.EllipticEst.sEta θ
                + Real.pi * A * Work.FTS.EllipticEst.sEta θ) by funext θ; ring]
        exact MeasureTheory.integral_add hG1 hG23
      have step2 : (∫ θ in Set.Ioo (0 : ℝ) (1 / 64), |u θ| * Work.FTS.EllipticEst.sEta θ)
          = KL := by rw [← hKLdef]
      have step3 : (∫ θ in Set.Ioo (0 : ℝ) (1 / 64), |u φ| * Work.FTS.EllipticEst.sEta θ
            + Real.pi * A * Work.FTS.EllipticEst.sEta θ)
          = |u φ| * mL + Real.pi * A * mL := by
        have hstep : (∫ θ in Set.Ioo (0 : ℝ) (1 / 64), |u φ| * Work.FTS.EllipticEst.sEta θ
              + Real.pi * A * Work.FTS.EllipticEst.sEta θ)
            = (∫ θ in Set.Ioo (0 : ℝ) (1 / 64), |u φ| * Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Set.Ioo (0 : ℝ) (1 / 64),
                  Real.pi * A * Work.FTS.EllipticEst.sEta θ) :=
          MeasureTheory.integral_add hG2 hG3
        rw [hstep, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          ← hmLdef]
      rw [step1, step2, step3]
      ring
    rw [e1, e2] at hle
    linarith [hle]
  -- step: integrate in `φ`
  have hstep3 : |c| * mL * mR ≤ mL * KR + KL * mR + Real.pi * A * mL * mR := by
    have hG1 : IntegrableOn (fun φ => mL * (|u φ| * Work.FTS.EllipticEst.sEta φ))
        (Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2)) := huσR.const_mul mL
    have hG2 : IntegrableOn (fun φ => KL * Work.FTS.EllipticEst.sEta φ)
        (Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2)) := hσR.const_mul _
    have hG3 : IntegrableOn (fun φ => Real.pi * A * mL * Work.FTS.EllipticEst.sEta φ)
        (Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2)) := hσR.const_mul _
    have hG23 : IntegrableOn (fun φ => KL * Work.FTS.EllipticEst.sEta φ
        + Real.pi * A * mL * Work.FTS.EllipticEst.sEta φ)
        (Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2)) := hG2.add hG3
    have hcomp : IntegrableOn
        (fun φ => (|u φ| * mL + KL + Real.pi * A * mL) * Work.FTS.EllipticEst.sEta φ)
        (Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2)) := by
      have heq : (fun φ => (|u φ| * mL + KL + Real.pi * A * mL) * Work.FTS.EllipticEst.sEta φ)
          = fun φ => mL * (|u φ| * Work.FTS.EllipticEst.sEta φ)
            + (KL * Work.FTS.EllipticEst.sEta φ
              + Real.pi * A * mL * Work.FTS.EllipticEst.sEta φ) := by funext φ; ring
      rw [heq]
      exact hG1.add hG23
    have hle : (∫ φ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
          (|c| * mL) * Work.FTS.EllipticEst.sEta φ)
        ≤ ∫ φ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
            (|u φ| * mL + KL + Real.pi * A * mL) * Work.FTS.EllipticEst.sEta φ := by
      refine integral_mono_of_nonneg ?_ hcomp ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with φ hφ
        exact mul_nonneg (mul_nonneg (abs_nonneg _) hmLnn) (sEta_nonneg_of_mem_Iθ (hsubR hφ))
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with φ hφ
        exact mul_le_mul_of_nonneg_right (hstep2 φ hφ) (sEta_nonneg_of_mem_Iθ (hsubR hφ))
    have e1 : (∫ φ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
          (|c| * mL) * Work.FTS.EllipticEst.sEta φ) = |c| * mL * mR := by
      rw [MeasureTheory.integral_const_mul, ← hmRdef]
    have e2 : (∫ φ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
          (|u φ| * mL + KL + Real.pi * A * mL) * Work.FTS.EllipticEst.sEta φ)
        = mL * KR + KL * mR + Real.pi * A * mL * mR := by
      have step1 : (∫ φ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
            (|u φ| * mL + KL + Real.pi * A * mL) * Work.FTS.EllipticEst.sEta φ)
          = (∫ φ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
              mL * (|u φ| * Work.FTS.EllipticEst.sEta φ))
            + (∫ φ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
                KL * Work.FTS.EllipticEst.sEta φ
                + Real.pi * A * mL * Work.FTS.EllipticEst.sEta φ) := by
        rw [show (fun φ => (|u φ| * mL + KL + Real.pi * A * mL) * Work.FTS.EllipticEst.sEta φ)
            = fun φ => mL * (|u φ| * Work.FTS.EllipticEst.sEta φ)
              + (KL * Work.FTS.EllipticEst.sEta φ
                + Real.pi * A * mL * Work.FTS.EllipticEst.sEta φ) by funext φ; ring]
        exact MeasureTheory.integral_add hG1 hG23
      have step2 : (∫ φ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
            mL * (|u φ| * Work.FTS.EllipticEst.sEta φ)) = mL * KR := by
        rw [MeasureTheory.integral_const_mul, ← hKRdef]
      have step3 : (∫ φ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
            KL * Work.FTS.EllipticEst.sEta φ
              + Real.pi * A * mL * Work.FTS.EllipticEst.sEta φ)
          = KL * mR + Real.pi * A * mL * mR := by
        have hstep : (∫ φ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
              KL * Work.FTS.EllipticEst.sEta φ
                + Real.pi * A * mL * Work.FTS.EllipticEst.sEta φ)
            = (∫ φ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
                KL * Work.FTS.EllipticEst.sEta φ)
              + (∫ φ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
                  Real.pi * A * mL * Work.FTS.EllipticEst.sEta φ) :=
          MeasureTheory.integral_add hG2 hG3
        rw [hstep, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
          ← hmRdef]
      rw [step1, step2, step3]
      ring
    rw [e1, e2] at hle
    linarith [hle]
  -- the Cauchy-Schwarz bounds on `KL`, `KR`
  have hMtotnn : 0 ≤ Mtot := by
    rw [hMtotdef]
    exact setIntegral_nonneg measurableSet_Icc (fun θ hθ => sEta_nonneg_of_mem_Iθ hθ)
  have hKLnn : 0 ≤ KL := by
    rw [hKLdef]
    exact setIntegral_nonneg measurableSet_Ioo
      (fun θ hθ => mul_nonneg (abs_nonneg _) (sEta_nonneg_of_mem_Iθ (hsubL hθ)))
  have hKRnn : 0 ≤ KR := by
    rw [hKRdef]
    exact setIntegral_nonneg measurableSet_Ioo
      (fun θ hθ => mul_nonneg (abs_nonneg _) (sEta_nonneg_of_mem_Iθ (hsubR hθ)))
  have hKLsq : KL ^ 2 ≤ P * Mtot := by
    have h1 := abs_mul_sEta_sq_le (s := Set.Ioo (0 : ℝ) (1 / 64)) measurableSet_Ioo hsubL
      (h0.mono_set hsubL) hσL
      (by
        have hucont : ContinuousOn u (Set.Ioo (0 : ℝ) (1 / 64)) := hu.continuousOn.mono hsubL'
        exact (Real.continuous_sqrt.continuousOn.comp
          ((hucont.pow 2).mul (continuousOn_sEta_of_subset hsubL'))
          (fun x hx => mul_nonneg (sq_nonneg _)
            (sEta_nonneg_of_mem_Iθ (hsubL hx)))).aestronglyMeasurable measurableSet_Ioo)
      (by
        exact (Real.continuous_sqrt.continuousOn.comp (continuousOn_sEta_of_subset hsubL')
          (fun x hx => sEta_nonneg_of_mem_Iθ (hsubL hx))).aestronglyMeasurable measurableSet_Ioo)
    have h3 : (∫ θ in Set.Ioo (0 : ℝ) (1 / 64), (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ P := by
      rw [hPdef]
      refine MeasureTheory.setIntegral_mono_set h0 ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact mul_nonneg (sq_nonneg _) (sEta_nonneg_of_mem_Iθ hθ)
      · exact Eventually.of_forall hsubL
    have h4 : (∫ θ in Set.Ioo (0 : ℝ) (1 / 64), Work.FTS.EllipticEst.sEta θ) ≤ Mtot := by
      rw [hMtotdef]
      refine MeasureTheory.setIntegral_mono_set integrableOn_sEta ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact sEta_nonneg_of_mem_Iθ hθ
      · exact Eventually.of_forall hsubL
    have h5 : 0 ≤ ∫ θ in Set.Ioo (0 : ℝ) (1 / 64), Work.FTS.EllipticEst.sEta θ :=
      setIntegral_nonneg measurableSet_Ioo (fun θ hθ => sEta_nonneg_of_mem_Iθ (hsubL hθ))
    calc KL ^ 2 = (∫ θ in Set.Ioo (0 : ℝ) (1 / 64),
          |u θ| * Work.FTS.EllipticEst.sEta θ) ^ 2 := by rw [hKLdef]
      _ ≤ (∫ θ in Set.Ioo (0 : ℝ) (1 / 64), (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            * (∫ θ in Set.Ioo (0 : ℝ) (1 / 64), Work.FTS.EllipticEst.sEta θ) := h1
      _ ≤ P * Mtot := mul_le_mul h3 h4 h5 hPnn
  have hKRsq : KR ^ 2 ≤ P * Mtot := by
    have h1 := abs_mul_sEta_sq_le (s := Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2))
      measurableSet_Ioo hsubR (h0.mono_set hsubR) hσR
      (by
        have hucont : ContinuousOn u (Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2)) :=
          hu.continuousOn.mono hsubR'
        exact (Real.continuous_sqrt.continuousOn.comp
          ((hucont.pow 2).mul (continuousOn_sEta_of_subset hsubR'))
          (fun x hx => mul_nonneg (sq_nonneg _)
            (sEta_nonneg_of_mem_Iθ (hsubR hx)))).aestronglyMeasurable measurableSet_Ioo)
      (by
        exact (Real.continuous_sqrt.continuousOn.comp (continuousOn_sEta_of_subset hsubR')
          (fun x hx => sEta_nonneg_of_mem_Iθ (hsubR hx))).aestronglyMeasurable measurableSet_Ioo)
    have h3 : (∫ θ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
        (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) ≤ P := by
      rw [hPdef]
      refine MeasureTheory.setIntegral_mono_set h0 ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact mul_nonneg (sq_nonneg _) (sEta_nonneg_of_mem_Iθ hθ)
      · exact Eventually.of_forall hsubR
    have h4 : (∫ θ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
        Work.FTS.EllipticEst.sEta θ) ≤ Mtot := by
      rw [hMtotdef]
      refine MeasureTheory.setIntegral_mono_set integrableOn_sEta ?_ ?_
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        exact sEta_nonneg_of_mem_Iθ hθ
      · exact Eventually.of_forall hsubR
    have h5 : 0 ≤ ∫ θ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
        Work.FTS.EllipticEst.sEta θ :=
      setIntegral_nonneg measurableSet_Ioo (fun θ hθ => sEta_nonneg_of_mem_Iθ (hsubR hθ))
    calc KR ^ 2 = (∫ θ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
          |u θ| * Work.FTS.EllipticEst.sEta θ) ^ 2 := by rw [hKRdef]
      _ ≤ (∫ θ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
            (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            * (∫ θ in Set.Ioo (Real.pi / 2 - 1 / 64) (Real.pi / 2),
              Work.FTS.EllipticEst.sEta θ) := h1
      _ ≤ P * Mtot := mul_le_mul h3 h4 h5 hPnn
  -- the final chain of estimates
  have hsKL : KL ≤ Real.sqrt (P * Mtot) := by
    have h := Real.sqrt_le_sqrt hKLsq
    rwa [Real.sqrt_sq hKLnn] at h
  have hsKR : KR ≤ Real.sqrt (P * Mtot) := by
    have h := Real.sqrt_le_sqrt hKRsq
    rwa [Real.sqrt_sq hKRnn] at h
  have h6 : |c| * mL * mR ≤ Real.sqrt (P * Mtot) * (mL + mR) + Real.pi * A * mL * mR := by
    have h7 : mL * KR + KL * mR ≤ Real.sqrt (P * Mtot) * (mL + mR) := by
      have h8 : mL * KR ≤ mL * Real.sqrt (P * Mtot) := mul_le_mul_of_nonneg_left hsKR hmLnn
      have h9 : KL * mR ≤ Real.sqrt (P * Mtot) * mR :=
        mul_le_mul_of_nonneg_right hsKL hmRnn
      linarith [h8, h9]
    linarith [hstep3, h7]
  have hpos : 0 < mL * mR :=
    mul_pos (lt_of_lt_of_le (by norm_num) hmL_ge) (lt_of_lt_of_le (by norm_num) hmR_ge)
  have h7 : |c| ≤ Real.sqrt (P * Mtot) * (mL + mR) / (mL * mR) + Real.pi * A := by
    have h8 : (|c| - Real.pi * A) * (mL * mR) ≤ Real.sqrt (P * Mtot) * (mL + mR) := by
      have h9 : |c| * (mL * mR)
          ≤ Real.sqrt (P * Mtot) * (mL + mR) + Real.pi * A * (mL * mR) := by linarith [h6]
      nlinarith [h9]
    have h10 : |c| - Real.pi * A ≤ Real.sqrt (P * Mtot) * (mL + mR) / (mL * mR) :=
      (le_div_iff₀ hpos).mpr h8
    linarith [h10]
  have hratio : (mL + mR) / (mL * mR) ≤ 128 := by
    have hLpos : 0 < mL := lt_of_lt_of_le (by norm_num) hmL_ge
    have hRpos : 0 < mR := lt_of_lt_of_le (by norm_num) hmR_ge
    have h1 : 1 / mL ≤ 64 := by rw [div_le_iff₀ hLpos]; linarith
    have h2 : 1 / mR ≤ 64 := by rw [div_le_iff₀ hRpos]; linarith
    have h3 : (mL + mR) / (mL * mR) = 1 / mR + 1 / mL := by field_simp
    linarith [h1, h2, h3]
  have hs : |c| ≤ 128 * Real.sqrt (P * Mtot) + Real.pi * A := by
    have h8 : Real.sqrt (P * Mtot) * ((mL + mR) / (mL * mR))
        ≤ Real.sqrt (P * Mtot) * 128 :=
      mul_le_mul_of_nonneg_left hratio (Real.sqrt_nonneg _)
    have h9 : Real.sqrt (P * Mtot) * (mL + mR) / (mL * mR)
        = Real.sqrt (P * Mtot) * ((mL + mR) / (mL * mR)) := by ring
    linarith [h7, h8, h9]
  have hsq : c ^ 2 ≤ (128 * Real.sqrt (P * Mtot) + Real.pi * A) ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg c) hs
    simpa [sq, sq_abs] using h
  have hsq2 : (128 * Real.sqrt (P * Mtot) + Real.pi * A) ^ 2
      ≤ 2 * (128 * Real.sqrt (P * Mtot)) ^ 2 + 2 * (Real.pi * A) ^ 2 := by
    nlinarith [sq_nonneg (128 * Real.sqrt (P * Mtot) - Real.pi * A)]
  have hsq3 : (Real.sqrt (P * Mtot)) ^ 2 = P * Mtot := Real.sq_sqrt (mul_nonneg hPnn hMtotnn)
  have hsq2' : (128 * Real.sqrt (P * Mtot)) ^ 2 = 16384 * (P * Mtot) := by
    rw [mul_pow, hsq3]
    norm_num
  have hfin : c ^ 2 ≤ 32768 * (P * Mtot) + 2 * Real.pi ^ 2 * A ^ 2 := by
    calc c ^ 2 ≤ (128 * Real.sqrt (P * Mtot) + Real.pi * A) ^ 2 := hsq
      _ ≤ 2 * (128 * Real.sqrt (P * Mtot)) ^ 2 + 2 * (Real.pi * A) ^ 2 := hsq2
      _ = 32768 * (P * Mtot) + 2 * Real.pi ^ 2 * A ^ 2 := by
          rw [hsq2', mul_pow]
          ring
  have hfin2 : 32768 * (P * Mtot) + 2 * Real.pi ^ 2 * A ^ 2 ≤ 10 ^ 9 * (P + E) := by
    have h1 : P * Mtot ≤ P * 10000 := mul_le_mul_of_nonneg_left hMtotle hPnn
    have h2 : Real.pi ^ 2 * A ^ 2 ≤ Real.pi ^ 2 * (Real.pi / 2 * E) :=
      mul_le_mul_of_nonneg_left hA2 (sq_nonneg _)
    have hπ2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
    have hπ3 : Real.pi ^ 3 ≤ 64 := by nlinarith [hπ2, Real.pi_pos, Real.pi_lt_four]
    have h3 : 2 * Real.pi ^ 2 * (Real.pi / 2 * E) ≤ 64 * E := by
      nlinarith [hπ3, hEnn]
    have h4 : 32768 * (P * 10000) ≤ 10 ^ 9 * P := by nlinarith [hPnn]
    nlinarith [h1, h2, h3, h4, hPnn, hEnn]
  linarith [hfin, hfin2]

/-! ## Assembly -/

theorem angularAgmon_of (Cp : ℝ) (hCp : 0 < Cp)
    (hpiv : ∀ (u : ℝ → ℝ), ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) →
      IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      (deriv u (Real.pi / 4)) ^ 2
        ≤ Cp * ((∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ)))
    (hfin : ∀ (u : ℝ → ℝ),
      (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
      IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ →
        (∫ θ in Work.Spaces.Iθ,
            (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ)
          ≤ C * ((∫ θ in Work.Spaces.Iθ,
                (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
  refine ⟨20000 * Cp + 10000 * Real.pi + 1, by positivity, ?_⟩
  intro α u hα hα4 hu h0 hπ hA
  have hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) := hu 2
  have hM : IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    hfin u hu hA
  obtain ⟨hIntu1, hbound⟩ := deriv_sq_mul_sEta_le Cp hCp hpiv u hu2 hM hA
  have hL : (∫ θ in Work.Spaces.Iθ,
        (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ)
      ≤ (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    refine integral_mono_of_nonneg ?_ hIntu1 ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      exact dth1Iter_one_sq_mul_sGam_le α hα hα4 u θ hθ
  have h3 : (20000 * Cp + 10000 * Real.pi + 1)
        * ((∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ))
      = (20000 * Cp + 10000 * Real.pi + 1)
        * ((∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by ring
  linarith [hL, hbound, h3]

theorem angularAgmon : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
    u 0 = 0 → u (Real.pi / 2) = 0 →
    MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ,
          (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ)
        ≤ C * ((∫ θ in Work.Spaces.Iθ,
              (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by
  obtain ⟨Cp, hCp, hpiv⟩ := pivotBound
  refine angularAgmon_of Cp hCp hpiv ?_
  intro u hu h2
  exact u_sq_mul_sEta_integrable (hu 2) h2

end

end Work.FTS.EllipticEst.H2W
