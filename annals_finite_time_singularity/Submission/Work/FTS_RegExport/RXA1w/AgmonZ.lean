import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted radial Agmon inequality

`Work.FTS_RegExport.RXA1w.agmonZ_weight`: for `v : ℝ → ℝ` differentiable on `(0,∞)`, with
`(v w)²` and `(x v' w)²` integrable on `[0,∞)` and `x (v x w(x))² → 0` at `+∞`,

  `(v z)² w(z)² z ≤ 4 ∫_{[0,∞)} (v w)² + ∫_{[0,∞)} (x v' w)²`   for `z > 0`,

where `w(z) = (1+z)²/z²`.  This is the weighted Agmon inequality in the radial variable, the
structurally new ingredient of RX-A1w.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXA1w

private lemma continuousOn_w_Ioi : ContinuousOn Work.Spaces.w (Set.Ioi (0 : ℝ)) := by
  have h : (fun y : ℝ => (1 + y) ^ 2 / y ^ 2) = Work.Spaces.w := by
    funext y; rw [Work.Spaces.w]
  rw [← h]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun y hy => pow_ne_zero 2 (ne_of_gt hy))

/-- `(v x · w x)² · x`, the weighted square of a radial slice. -/
private noncomputable def agmonF (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  x * (v x * Work.Spaces.w x) ^ 2

/-- The derivative of `agmonF v` on `(0,∞)`. -/
private noncomputable def agmonF' (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 * v x * (x * deriv v x) * (Work.Spaces.w x) ^ 2
    + (v x) ^ 2 * (Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))

/-- **Weighted radial Agmon inequality on the half-line.** -/
theorem agmonZ_weight {v : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt v (deriv v x) x)
    (hint1 : MeasureTheory.IntegrableOn (fun x => (v x * Work.Spaces.w x) ^ 2) Work.Spaces.Iz)
    (hint2 : MeasureTheory.IntegrableOn (fun x => (x * deriv v x * Work.Spaces.w x) ^ 2)
      Work.Spaces.Iz)
    (hdec : Filter.Tendsto (fun x => x * (v x * Work.Spaces.w x) ^ 2) Filter.atTop (𝓝 0)) :
    (v z) ^ 2 * (Work.Spaces.w z) ^ 2 * z ≤
      4 * (∫ x in Work.Spaces.Iz, (v x * Work.Spaces.w x) ^ 2)
        + ∫ x in Work.Spaces.Iz, (x * deriv v x * Work.Spaces.w x) ^ 2 := by
  have hvcont : ContinuousOn v (Set.Ioi (0 : ℝ)) := fun x hx =>
    (hderiv x hx).differentiableAt.continuousAt.continuousWithinAt
  have hIz_eq : volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [Work.Spaces.Iz, MeasureTheory.restrict_Ioi_eq_restrict_Ici]
  have hFderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (agmonF v) (agmonF' v x) x := by
    intro x hx
    have hx0 : 0 < x := hx
    have hxne : x ≠ 0 := ne_of_gt hx0
    have hev : agmonF v =ᶠ[𝓝 x] fun y : ℝ => (v y) ^ 2 * (1 + y) ^ 4 / y ^ 3 := by
      filter_upwards [isOpen_Ioi.mem_nhds hx0] with y hy
      simp only [agmonF, Work.Spaces.w]
      field_simp
    have hv2 : HasDerivAt (fun y : ℝ => (v y) ^ 2) (2 * v x * deriv v x) x := by
      have h := (hderiv x hx).pow 2
      convert h using 1 <;> ring
    have h1xy : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
      have h := (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
      convert h using 1
      · funext y; simp
      · simp
    have hp : HasDerivAt (fun y : ℝ => (1 + y) ^ 4) (4 * (1 + x) ^ 3) x := by
      have h := h1xy.pow 4
      convert h using 1 <;> ring
    have hden : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
      have h := (hasDerivAt_id x).pow 3
      convert h using 1
      · funext y; rfl
      · simp
    have hnum : HasDerivAt (fun y : ℝ => (v y) ^ 2 * (1 + y) ^ 4)
        (2 * v x * deriv v x * (1 + x) ^ 4 + (v x) ^ 2 * (4 * (1 + x) ^ 3)) x := by
      have h := hv2.mul hp
      convert h using 1 <;> ring
    have hq := hnum.div hden (pow_ne_zero 3 hxne)
    refine (hev.hasDerivAt_iff).mpr ?_
    convert hq using 1
    rw [agmonF']
    simp only [Work.Spaces.w]
    field_simp <;> ring
  have hF'bound : ∀ x ∈ Work.Spaces.Iz,
      |agmonF' v x| ≤ 4 * (v x * Work.Spaces.w x) ^ 2
        + (x * deriv v x * Work.Spaces.w x) ^ 2 := by
    intro x hx
    have hx0 : 0 ≤ x := hx
    have hb : |(x - 3) / (1 + x)| ≤ 3 := by
      have h1x : (0 : ℝ) < 1 + x := by linarith
      rw [abs_div, abs_of_pos h1x, div_le_iff₀ h1x]
      by_cases h : x ≤ 3
      · rw [abs_of_nonpos (by linarith)]; nlinarith
      · push_neg at h
        rw [abs_of_pos (by linarith)]; nlinarith
    have hkey : agmonF' v x
        = 2 * (v x * Work.Spaces.w x) * (x * deriv v x * Work.Spaces.w x)
          + (v x * Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x)) := by
      rw [agmonF']; ring
    have hAB : 2 * |(v x * Work.Spaces.w x)| * |(x * deriv v x * Work.Spaces.w x)|
        ≤ (v x * Work.Spaces.w x) ^ 2 + (x * deriv v x * Work.Spaces.w x) ^ 2 := by
      nlinarith [sq_nonneg (|v x * Work.Spaces.w x| - |x * deriv v x * Work.Spaces.w x|),
        sq_abs (v x * Work.Spaces.w x), sq_abs (x * deriv v x * Work.Spaces.w x)]
    have hE1 : |2 * (v x * Work.Spaces.w x) * (x * deriv v x * Work.Spaces.w x)|
        = 2 * |(v x * Work.Spaces.w x)| * |(x * deriv v x * Work.Spaces.w x)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] <;> ring
    have hE2 : |(v x * Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))|
        = (v x * Work.Spaces.w x) ^ 2 * |(x - 3) / (1 + x)| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    rw [hkey]
    calc |2 * (v x * Work.Spaces.w x) * (x * deriv v x * Work.Spaces.w x)
            + (v x * Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))|
        ≤ |2 * (v x * Work.Spaces.w x) * (x * deriv v x * Work.Spaces.w x)|
            + |(v x * Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))| := abs_add_le _ _
      _ = 2 * |(v x * Work.Spaces.w x)| * |(x * deriv v x * Work.Spaces.w x)|
            + (v x * Work.Spaces.w x) ^ 2 * |(x - 3) / (1 + x)| := by rw [hE1, hE2]
      _ ≤ (v x * Work.Spaces.w x) ^ 2 + (x * deriv v x * Work.Spaces.w x) ^ 2
            + (v x * Work.Spaces.w x) ^ 2 * 3 := by
          refine add_le_add hAB ?_
          exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ = 4 * (v x * Work.Spaces.w x) ^ 2
            + (x * deriv v x * Work.Spaces.w x) ^ 2 := by ring
  have hgint : MeasureTheory.IntegrableOn
      (fun x => 4 * (v x * Work.Spaces.w x) ^ 2
        + (x * deriv v x * Work.Spaces.w x) ^ 2) Work.Spaces.Iz :=
    (hint1.const_mul 4).add hint2
  have haesm : AEStronglyMeasurable (agmonF' v) (volume.restrict Work.Spaces.Iz) := by
    rw [hIz_eq]
    have hdv : AEStronglyMeasurable (deriv v) (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (aestronglyMeasurable_deriv v volume).restrict
    have hvc : AEStronglyMeasurable v (volume.restrict (Set.Ioi (0 : ℝ))) :=
      hvcont.aestronglyMeasurable measurableSet_Ioi
    have hwc : AEStronglyMeasurable (fun x : ℝ => Work.Spaces.w x)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      continuousOn_w_Ioi.aestronglyMeasurable measurableSet_Ioi
    have hc3 : AEStronglyMeasurable (fun x : ℝ => (x - 3) / (1 + x))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      have h2 : ContinuousOn (fun x : ℝ => 1 + x) (Set.Ioi (0 : ℝ)) :=
        continuousOn_const.add continuousOn_id
      exact ((continuousOn_id.sub continuousOn_const).div h2
        (fun x hx => by have hx0 : 0 < x := hx; exact ne_of_gt (by linarith))).aestronglyMeasurable
        measurableSet_Ioi
    have h1 : AEStronglyMeasurable
        (fun x : ℝ => 2 * v x * (x * deriv v x) * (Work.Spaces.w x) ^ 2)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (((hvc.const_mul 2).mul (aestronglyMeasurable_id.mul hdv)).mul (hwc.pow 2))
    have h2 : AEStronglyMeasurable
        (fun x : ℝ => (v x) ^ 2 * (Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x)))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (((hvc.pow 2).mul (hwc.pow 2)).mul hc3)
    exact (h1.add h2).congr (Filter.Eventually.of_forall fun x => by
      simp only [agmonF', Pi.add_apply]; try ring)
  have hF'int : MeasureTheory.IntegrableOn (agmonF' v) Work.Spaces.Iz :=
    hgint.mono' haesm (ae_restrict_of_forall_mem measurableSet_Ici fun x hx => by
      rw [Real.norm_eq_abs]; exact hF'bound x hx)
  have hAbsOn : MeasureTheory.IntegrableOn (fun x => |agmonF' v x|) Work.Spaces.Iz :=
    hF'int.abs
  have htail : ∀ X : ℝ, z ≤ X → agmonF v z
      ≤ agmonF v X + ∫ x in Set.Ioi z, |agmonF' v x| := by
    intro X hzX
    have hFcont : ContinuousOn (agmonF v) (Set.Icc z X) := by
      have hv : ContinuousOn v (Set.Icc z X) :=
        hvcont.mono (fun x hx => lt_of_lt_of_le hz hx.1)
      have hw : ContinuousOn Work.Spaces.w (Set.Icc z X) :=
        continuousOn_w_Ioi.mono (fun x hx => lt_of_lt_of_le hz hx.1)
      have h := ((hv.pow 2).mul (hw.pow 2)).mul continuousOn_id
      refine h.congr (fun y _ => ?_)
      simp only [agmonF, Pi.mul_apply, Pi.pow_apply, id_eq]; ring
    have hd : ∀ x ∈ Set.Ioo z X, HasDerivAt (agmonF v) (agmonF' v x) x :=
      fun x hx => hFderiv x (lt_trans hz hx.1)
    have hintv : IntervalIntegrable (agmonF' v) volume z X := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hzX]
      exact hF'int.mono_set (fun x hx => le_of_lt (lt_trans hz hx.1))
    have hFTC : ∫ x in z..X, agmonF' v x = agmonF v X - agmonF v z :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hzX hFcont hd hintv
    have h3abs : |∫ x in z..X, agmonF' v x| ≤ ∫ x in Set.Ioi z, |agmonF' v x| := by
      rw [intervalIntegral.integral_of_le hzX]
      refine le_trans (MeasureTheory.abs_integral_le_integral_abs) ?_
      exact MeasureTheory.setIntegral_mono_set
        (hAbsOn.mono_set (fun x hx => le_of_lt (lt_trans hz hx)))
        (Filter.Eventually.of_forall fun x => abs_nonneg _)
        (Filter.Eventually.of_forall fun x hx => hx.1)
    have h3 : -(∫ x in z..X, agmonF' v x) ≤ ∫ x in Set.Ioi z, |agmonF' v x| :=
      le_trans (neg_le_abs _) h3abs
    linarith [hFTC, h3]
  have hlim : Filter.Tendsto (fun X : ℝ => agmonF v X + ∫ x in Set.Ioi z, |agmonF' v x|)
      Filter.atTop (𝓝 (0 + ∫ x in Set.Ioi z, |agmonF' v x|)) :=
    hdec.add_const _
  have hev2 : ∀ᶠ X in Filter.atTop,
      agmonF v z ≤ agmonF v X + ∫ x in Set.Ioi z, |agmonF' v x| :=
    (Filter.eventually_ge_atTop z).mono htail
  have hmain : agmonF v z ≤ ∫ x in Set.Ioi z, |agmonF' v x| := by
    have := ge_of_tendsto hlim hev2
    simpa using this
  have hmono : ∀ᵐ x ∂(volume.restrict (Set.Ioi z)),
      |agmonF' v x| ≤ 4 * (v x * Work.Spaces.w x) ^ 2
        + (x * deriv v x * Work.Spaces.w x) ^ 2 :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun x hx =>
      hF'bound x (le_of_lt (lt_trans hz hx))
  have hgintz : MeasureTheory.IntegrableOn
      (fun x => 4 * (v x * Work.Spaces.w x) ^ 2
        + (x * deriv v x * Work.Spaces.w x) ^ 2) (Set.Ioi z) :=
    hgint.mono_set (fun x hx => le_of_lt (lt_trans hz hx))
  have habsint : MeasureTheory.IntegrableOn (fun x => |agmonF' v x|) (Set.Ioi z) :=
    hAbsOn.mono_set (fun x hx => le_of_lt (lt_trans hz hx))
  have hle : ∫ x in Set.Ioi z, |agmonF' v x| ≤ ∫ x in Set.Ioi z,
      (4 * (v x * Work.Spaces.w x) ^ 2 + (x * deriv v x * Work.Spaces.w x) ^ 2) :=
    integral_mono_ae habsint hgintz hmono
  have hIz : (∫ x in Set.Ioi z,
        (4 * (v x * Work.Spaces.w x) ^ 2 + (x * deriv v x * Work.Spaces.w x) ^ 2))
      ≤ 4 * (∫ x in Work.Spaces.Iz, (v x * Work.Spaces.w x) ^ 2)
        + ∫ x in Work.Spaces.Iz, (x * deriv v x * Work.Spaces.w x) ^ 2 := by
    have hIa0 : MeasureTheory.IntegrableOn (fun x => 4 * (v x * Work.Spaces.w x) ^ 2)
        Work.Spaces.Iz := hint1.const_mul 4
    have hIa : MeasureTheory.IntegrableOn (fun x => 4 * (v x * Work.Spaces.w x) ^ 2)
        (Set.Ioi z) := hIa0.mono_set (fun x hx => le_of_lt (lt_trans hz hx))
    have hIb : MeasureTheory.IntegrableOn
        (fun x => (x * deriv v x * Work.Spaces.w x) ^ 2) (Set.Ioi z) :=
      hint2.mono_set (fun x hx => le_of_lt (lt_trans hz hx))
    rw [integral_add hIa hIb, integral_const_mul]
    refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by norm_num)) ?_
    · exact MeasureTheory.setIntegral_mono_set hint1
        (Filter.Eventually.of_forall fun x => sq_nonneg _)
        (Filter.Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx))
    · exact MeasureTheory.setIntegral_mono_set hint2
        (Filter.Eventually.of_forall fun x => sq_nonneg _)
        (Filter.Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx))
  have hfin : (v z) ^ 2 * (Work.Spaces.w z) ^ 2 * z = agmonF v z := by
    rw [agmonF]; ring
  rw [hfin]
  linarith [hmain, hle, hIz]

end Work.FTS_RegExport.RXA1w
