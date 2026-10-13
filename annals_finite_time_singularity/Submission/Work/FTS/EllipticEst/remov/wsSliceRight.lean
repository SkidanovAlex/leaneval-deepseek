import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.SourceBound.tanuIdentity
import Submission.Work.FTS.EllipticEst.remov.SourceBound.tendstoOfAbsLeCosDivSin
import Submission.Work.FTS.EllipticEst.remov.SourceBound.absIntegrableOfSq
import Submission.Work.FTS.EllipticEst.remov.SourceBound.absIntegrableOfSqMulSeta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The right-end limit of an angular slice with honest `Lzero1`-source.**

A single integration of `Lzero1 u = -u'' + (tan θ · u)' - 6u` over `(π/4, b)` gives

  `tan b · u b = ∫_{π/4}^b Lzero1 u + u'(b) - u'(π/4) + tan(π/4)·u(π/4) + 6∫_{π/4}^b u`,

whose right hand side is bounded uniformly in `b < π/2`: the first term by the total mass of
`|Lzero1 u|` on `Iθ` (hypothesis `hL`), the second by writing `u'(b) - u'(π/4)` as the integral
of `u''` (hypothesis `h2`, whose weight `sEta ≥ 1` makes `|u''|` integrable), and the last by the
total mass of `|u|` (hypothesis `hu`).  Hence `|tan b · u b| ≤ K`, so
`|u θ| ≤ K·cos θ / sin θ → 0` as `θ → (π/2)⁻`. -/
theorem wsSliceRight {u : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ)
    (hL : MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ)
    (hu : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ) :
    Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have h4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  -- ### a.e. strong measurability of the three functions
  have huaesm : MeasureTheory.AEStronglyMeasurable u
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    (hsm.continuousOn.aemeasurable measurableSet_Ioo).aestronglyMeasurable
  have h2aesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => deriv (fun t => deriv u t) θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    (measurable_deriv (fun t => deriv u t)).aestronglyMeasurable
  have hLaesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.FTS.EllipticEst.Lzero1 u θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    show MeasureTheory.AEStronglyMeasurable
      (fun θ => -(deriv (fun t => deriv u t) θ) + deriv (fun t => Real.tan t * u t) θ
        - 6 * u θ) _
    exact (((measurable_deriv (fun t => deriv u t)).neg.aestronglyMeasurable).add
      ((measurable_deriv (fun t => Real.tan t * u t)).aestronglyMeasurable)).sub
      (huaesm.const_mul 6)
  -- ### the three absolute-value integrabilities on the open interval
  have huabs : MeasureTheory.IntegrableOn (fun θ => |u θ|)
      (Set.Ioo 0 (Real.pi / 2)) := SourceBound.absIntegrableOfSq huaesm hu
  have h2abs : MeasureTheory.IntegrableOn (fun θ => |deriv (fun t => deriv u t) θ|)
      (Set.Ioo 0 (Real.pi / 2)) := SourceBound.absIntegrableOfSqMulSeta h2aesm h2
  have hLabs : MeasureTheory.IntegrableOn (fun θ => |Work.FTS.EllipticEst.Lzero1 u θ|)
      (Set.Ioo 0 (Real.pi / 2)) := SourceBound.absIntegrableOfSqMulSeta hLaesm hL
  -- ### the constant `K`
  set A : ℝ := ∫ x in Set.Ioo 0 (Real.pi / 2), |Work.FTS.EllipticEst.Lzero1 u x| with hA
  set B : ℝ := ∫ x in Set.Ioo 0 (Real.pi / 2), |deriv (fun t => deriv u t) x| with hB
  set C : ℝ := ∫ x in Set.Ioo 0 (Real.pi / 2), |u x| with hC
  have hAnn : 0 ≤ A := by rw [hA]; exact integral_nonneg (fun x => abs_nonneg _)
  have hBnn : 0 ≤ B := by rw [hB]; exact integral_nonneg (fun x => abs_nonneg _)
  have hCnn : 0 ≤ C := by rw [hC]; exact integral_nonneg (fun x => abs_nonneg _)
  set K : ℝ := |Real.tan (Real.pi / 4) * u (Real.pi / 4)| + A + B + 6 * C with hK
  refine SourceBound.tendstoOfAbsLeCosDivSin (K := K) ?_
  intro θ hθ
  have hθπ : Real.pi / 4 < θ := hθ.1
  have hθ2 : θ < Real.pi / 2 := hθ.2
  have hsubIcc : Set.Icc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_of_lt_of_le hpi4 hx.1, lt_of_le_of_lt hx.2 hθ2⟩
  -- ### the fundamental theorem of calculus for `u''`
  have hdu_c : ContinuousOn (deriv u) (Set.Icc (Real.pi / 4) θ) :=
    ((hsm.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).continuousOn).mono hsubIcc
  have hd2_c : ContinuousOn (fun x => deriv (fun t => deriv u t) x)
      (Set.Icc (Real.pi / 4) θ) := by
    have h1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
      hsm.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
    have h0 : ContDiffOn ℝ 0 (fun x => deriv (fun t => deriv u t) x)
        (Set.Ioo 0 (Real.pi / 2)) :=
      h1.deriv_of_isOpen isOpen_Ioo (m := 0) (by norm_num)
    exact h0.continuousOn.mono hsubIcc
  have hderiv2 : ∀ x ∈ Set.Ioo (Real.pi / 4) θ,
      HasDerivAt (deriv u) (deriv (fun t => deriv u t) x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hsubIcc ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have h2x : ContDiffAt ℝ 2 u x := hsm.contDiffAt (isOpen_Ioo.mem_nhds hx')
    have h1x : ContDiffAt ℝ 1 (deriv u) x := h2x.derivWithin (by norm_num)
    exact (h1x.differentiableAt (by norm_num)).hasDerivAt
  have hIint2 : IntervalIntegrable (fun x => deriv (fun t => deriv u t) x) volume
      (Real.pi / 4) θ := by
    have hc : ContinuousOn (fun x => deriv (fun t => deriv u t) x)
        (Set.uIcc (Real.pi / 4) θ) := by
      rw [Set.uIcc_of_le hθπ.le]; exact hd2_c
    exact hc.intervalIntegrable
  have hftc2 : ∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x
      = deriv u θ - deriv u (Real.pi / 4) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθπ.le hdu_c hderiv2 hIint2
  -- ### the combined identity
  have hid := SourceBound.tanuIdentity hsm hpi4 hθπ hθ2
  have hcomb : Real.tan θ * u θ
      = (∫ x in (Real.pi / 4)..θ, Work.FTS.EllipticEst.Lzero1 u x)
        + (∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x)
        + Real.tan (Real.pi / 4) * u (Real.pi / 4)
        + 6 * (∫ x in (Real.pi / 4)..θ, u x) := by
    linarith [hid, hftc2]
  -- ### bound each of the three interval integrals by its total mass
  have hIocJ : Set.Ioc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
    ⟨lt_trans hpi4 hx.1, lt_of_le_of_lt hx.2 hθ2⟩
  have hbL : |∫ x in (Real.pi / 4)..θ, Work.FTS.EllipticEst.Lzero1 u x| ≤ A := by
    rw [hA]
    have h1 : |∫ x in (Real.pi / 4)..θ, Work.FTS.EllipticEst.Lzero1 u x|
        ≤ ∫ x in (Real.pi / 4)..θ, |Work.FTS.EllipticEst.Lzero1 u x| := by
      simpa only [Real.norm_eq_abs] using
        intervalIntegral.norm_integral_le_integral_norm (μ := volume)
          (f := fun x => Work.FTS.EllipticEst.Lzero1 u x) hθπ.le
    refine h1.trans ?_
    rw [intervalIntegral.integral_of_le hθπ.le]
    exact setIntegral_mono_set hLabs (Filter.Eventually.of_forall (fun x => abs_nonneg _))
      (Filter.Eventually.of_forall (fun x hx => hIocJ hx))
  have hb2 : |∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x| ≤ B := by
    rw [hB]
    have h1 : |∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x|
        ≤ ∫ x in (Real.pi / 4)..θ, |deriv (fun t => deriv u t) x| := by
      simpa only [Real.norm_eq_abs] using
        intervalIntegral.norm_integral_le_integral_norm (μ := volume)
          (f := fun x => deriv (fun t => deriv u t) x) hθπ.le
    refine h1.trans ?_
    rw [intervalIntegral.integral_of_le hθπ.le]
    exact setIntegral_mono_set h2abs (Filter.Eventually.of_forall (fun x => abs_nonneg _))
      (Filter.Eventually.of_forall (fun x hx => hIocJ hx))
  have hbC : |∫ x in (Real.pi / 4)..θ, u x| ≤ C := by
    rw [hC]
    have h1 : |∫ x in (Real.pi / 4)..θ, u x| ≤ ∫ x in (Real.pi / 4)..θ, |u x| := by
      simpa only [Real.norm_eq_abs] using
        intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := u) hθπ.le
    refine h1.trans ?_
    rw [intervalIntegral.integral_of_le hθπ.le]
    exact setIntegral_mono_set huabs (Filter.Eventually.of_forall (fun x => abs_nonneg _))
      (Filter.Eventually.of_forall (fun x hx => hIocJ hx))
  -- ### the resulting bound on `tan θ · u θ`
  have hbound : |Real.tan θ * u θ| ≤ K := by
    rw [hK]
    have htri : |(∫ x in (Real.pi / 4)..θ, Work.FTS.EllipticEst.Lzero1 u x)
        + (∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x)
        + Real.tan (Real.pi / 4) * u (Real.pi / 4)
        + 6 * (∫ x in (Real.pi / 4)..θ, u x)| ≤
        |∫ x in (Real.pi / 4)..θ, Work.FTS.EllipticEst.Lzero1 u x|
        + |∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x|
        + |Real.tan (Real.pi / 4) * u (Real.pi / 4)|
        + |6 * (∫ x in (Real.pi / 4)..θ, u x)| := by
      have h1 := abs_add_le ((∫ x in (Real.pi / 4)..θ, Work.FTS.EllipticEst.Lzero1 u x)
          + (∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x)
          + Real.tan (Real.pi / 4) * u (Real.pi / 4))
        (6 * (∫ x in (Real.pi / 4)..θ, u x))
      have h2 := abs_add_le ((∫ x in (Real.pi / 4)..θ, Work.FTS.EllipticEst.Lzero1 u x)
          + (∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x))
        (Real.tan (Real.pi / 4) * u (Real.pi / 4))
      have h3 := abs_add_le (∫ x in (Real.pi / 4)..θ, Work.FTS.EllipticEst.Lzero1 u x)
        (∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x)
      linarith
    have h6 : |6 * (∫ x in (Real.pi / 4)..θ, u x)| = 6 * |∫ x in (Real.pi / 4)..θ, u x| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
    rw [hcomb]
    have h6le : |6 * (∫ x in (Real.pi / 4)..θ, u x)| ≤ 6 * C := by
      rw [h6]; exact mul_le_mul_of_nonneg_left hbC (by norm_num)
    linarith [hbL, hb2, h6le]
  -- ### pass from `tan θ · u θ` to `u θ`
  have htan : 0 < Real.tan θ :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (lt_trans hpi4 hθπ) hθ2
  have hKey : |u θ| = |Real.tan θ * u θ| / Real.tan θ := by
    rw [abs_mul, abs_of_pos htan]
    field_simp
  rw [hKey]
  calc |Real.tan θ * u θ| / Real.tan θ
      ≤ K / Real.tan θ := div_le_div_of_nonneg_right hbound htan.le
    _ = K * (Real.cos θ / Real.sin θ) := by
        rw [div_eq_mul_inv, Real.tan_eq_sin_div_cos, inv_div]

end

end Work.FTS.EllipticEst.remov
