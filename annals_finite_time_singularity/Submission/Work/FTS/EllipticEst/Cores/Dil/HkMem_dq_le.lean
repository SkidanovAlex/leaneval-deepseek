import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllipticEst.Cores.Dil.HkSqLimit
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Physical.Ident.vorticity_psiField_scaled
import Submission.Work.Stability.mul_rpow_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.Dil

set_option autoImplicit false
set_option maxHeartbeats 8000000

/-! ## The level-`0` radial majorant of the difference quotient -/



theorem Iθ_eq : Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) := rfl


/-! ## The weight comparison `w z ≤ u² w (z u)` for `u ≥ 1` -/

theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_nonneg (by positivity) (by positivity)


/-! ## The `u`-integral representation of the difference quotient -/


/-! ## Cauchy–Schwarz on an interval -/

theorem sq_intervalIntegral_le {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : IntervalIntegrable F MeasureTheory.volume a b)
    (hF2 : IntervalIntegrable (fun u => F u ^ 2) MeasureTheory.volume a b) :
    (∫ u in a..b, F u) ^ 2 ≤ (b - a) * ∫ u in a..b, F u ^ 2 := by
  have hF' : MeasureTheory.Integrable F (MeasureTheory.volume.restrict (Set.Ioc a b)) := by
    have h := intervalIntegrable_iff.mp hF
    rwa [Set.uIoc_of_le hab] at h
  have hF2' : MeasureTheory.Integrable (fun u => F u ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioc a b)) := by
    have h := intervalIntegrable_iff.mp hF2
    rwa [Set.uIoc_of_le hab] at h
  have hmu : (MeasureTheory.volume.restrict (Set.Ioc a b)) Set.univ ≠ ∞ := by
    rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hone : MeasureTheory.Integrable (fun _ : ℝ => (1:ℝ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioc a b)) := by
    simpa using (integrableOn_const (s := Set.Ioc a b) (C := (1:ℝ)) hmu (by simp))
  have hcs := Work.RPFresh.integral_mul_sq_le_sq_mul_sq
    (MeasureTheory.volume.restrict (Set.Ioc a b)) hF'.aestronglyMeasurable
    aestronglyMeasurable_const hF2' hone
  have hleft : (∫ u in a..b, F u) = ∫ u in Set.Ioc a b, F u :=
    intervalIntegral.integral_of_le hab
  have hright : (∫ u in a..b, F u ^ 2) = ∫ u in Set.Ioc a b, F u ^ 2 :=
    intervalIntegral.integral_of_le hab
  have honeval : (∫ u in Set.Ioc a b, (1:ℝ) ^ 2) = b - a := by
    rw [MeasureTheory.integral_const, smul_eq_mul, MeasureTheory.Measure.real,
      MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
    ring
  have hmain : (∫ u in Set.Ioc a b, F u) ^ 2
      ≤ (∫ u in Set.Ioc a b, F u ^ 2) * (b - a) := by
    rw [← honeval]
    simpa only [mul_one] using hcs
  rw [hleft, hright]
  rw [mul_comm]
  exact hmain

/-! ## The level-`0` integrand as a product of squares -/

theorem HkIntegrand_sq_eq {α : ℝ} (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ) ^ 2 * ((Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rw [HkIntegrand_zero_apply, mul_pow, div_pow,
    show (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
        = Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) * Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)
      from by ring,
    ← Real.rpow_add hs,
    show Work.Spaces.eta / 2 + Work.Spaces.eta / 2 = Work.Spaces.eta from by ring,
    div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hs)]


theorem continuousOn_w : ContinuousOn Work.Spaces.w (Set.Ioi (0:ℝ)) := by
  have h : (Work.Spaces.w : ℝ → ℝ) = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := by
    funext z; rfl
  rw [h]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))

/-! ## The pointwise majorisation -/


/-! ## Measure bookkeeping on the quadrant -/






/-! ## Change of variables for the lower Lebesgue integral -/



/-! ## The interval-integral bridge -/

theorem ofReal_intervalIntegral_eq_lintegral {F : ℝ → ℝ} {c : ℝ} (hc : 1 < c)
    (hF : ContinuousOn F (Set.Icc (1:ℝ) c)) (hnn : ∀ u ∈ Set.Icc (1:ℝ) c, 0 ≤ F u) :
    ENNReal.ofReal (∫ u in (1:ℝ)..c, F u)
      = ∫⁻ u in Set.Ioo (1:ℝ) c, ENNReal.ofReal (F u) := by
  have hio : MeasureTheory.IntegrableOn F (Set.Ioc (1:ℝ) c) MeasureTheory.volume :=
    (hF.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hnn' : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Ioc (1:ℝ) c)), 0 ≤ F u := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    exact hnn u (Set.Ioc_subset_Icc_self hu)
  rw [intervalIntegral.integral_of_le hc.le]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hio hnn']
  show (∫⁻ u, ENNReal.ofReal (F u) ∂(MeasureTheory.volume.restrict (Set.Ioc (1:ℝ) c)))
      = ∫⁻ u in Set.Ioo (1:ℝ) c, ENNReal.ofReal (F u)
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Ioc (a := (1:ℝ)) (b := c))]

/-! ## The `u`-substitution of the majorant -/



/-! ## The `ofReal` expansion of the majorant -/

theorem continuousOn_u_majorant {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) {c z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContinuousOn (fun u : ℝ => u ^ 2
        * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ) (Set.Icc (1:ℝ) c) := by
  have hmap : ∀ u ∈ Set.Icc (1:ℝ) c, 0 < z * u := fun u hu =>
    mul_pos hz (lt_of_lt_of_le zero_lt_one (Set.mem_Icc.mp hu).1)
  have h1 : ContinuousOn (fun u : ℝ => (Work.Spaces.Dz g (z * u) θ) ^ 2) (Set.Icc (1:ℝ) c) :=
    (((hg.Dz).curry_z hθ).continuousOn.pow 2).comp (by fun_prop) hmap
  have h2 : ContinuousOn (fun u : ℝ => (Work.Spaces.w (z * u)) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (Set.Icc (1:ℝ) c) :=
    ((continuousOn_w.comp (by fun_prop) hmap).pow 2).mul continuousOn_const
  rw [show (fun u : ℝ => u ^ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dz g) (z * u) θ)
      = fun u : ℝ => u ^ 2 * ((Work.Spaces.Dz g (z * u) θ) ^ 2
          * ((Work.Spaces.w (z * u)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) from
    funext fun u => by rw [HkIntegrand_sq_eq (Work.Spaces.Dz g) hθ]]
  exact (continuousOn_id.pow 2).mul (h1.mul h2)



/-! ## The `ℋ⁰`-lintegral of the majorant -/


/-! ## The `θ`-slices of the majorant are integrable -/


/-! ## The `z`-integral of the slices of the majorant is integrable -/



end Work.FTS.EllipticEst.Cores.Dil
