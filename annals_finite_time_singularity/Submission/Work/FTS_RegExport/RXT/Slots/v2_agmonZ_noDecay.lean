import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS_RegExport.RXT.AgmonND.Defs
import Submission.Work.FTS_RegExport.RXT.AgmonND.hasDerivAt_agmonF

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted radial Agmon inequality, without any decay hypothesis

`Work.FTS_RegExport.RXT.Slots.v2_agmonZ_noDecay`: for `v : ℝ → ℝ` differentiable on `(0,∞)`
with `(v w)²` and `(x v' w)²` integrable on `[0,∞)`, and `z > 0`,

  `(v z)² w(z)² z ≤ 4 ∫_{z}^{∞} (v w)² + ∫_{z}^{∞} (x v' w)²`.

This is the statement of `Work.FTS_RegExport.RXA1w.agmonZ_weight` with the hypothesis that
`x (v x w x)² → 0` at `+∞` removed.  That hypothesis is *not* needed: writing
`F x = x (v x w x)²`, the fundamental theorem of calculus on `[z, X]` gives

  `F z ≤ F X + ∫_{z}^{∞} |F'|`   for every `X ≥ z`,

and integrability of `(v w)²` alone forces `F` to take arbitrarily small values at
arbitrarily large points (`agmon_small_value` below, via the divergence of `∫ dx/x`), so
`inf_{X ≥ z} F X = 0` and `F z ≤ ∫_{z}^{∞} |F'|`.  The pointwise bound
`|F'| ≤ 4 (v w)² + (x v' w)²` on `[0,∞)` finishes the argument.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Slots

/-- If `u²` is integrable on `(z,∞)` (with `z > 0`), then `x * u x ^ 2` is arbitrarily small
at arbitrarily large points.  (No continuity of `u` is required: the pointwise lower bound
`u x² > ε/x` on the whole half-line `(z,∞)` forces `∫_{z}^{N} u² ≥ ε log(N/z) → ∞`.) -/
private lemma agmon_small_value {u : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hint : MeasureTheory.IntegrableOn (fun x => u x ^ 2) (Set.Ioi z)) :
    ∀ ε > 0, ∃ R : ℝ, z < R ∧ R * (u R) ^ 2 ≤ ε := by
  intro ε hε
  by_contra hcon
  push_neg at hcon
  have hstep : ∀ N : ℝ, z < N →
      ε * Real.log (N / z) ≤ ∫ x in Set.Ioi z, u x ^ 2 := by
    intro N hzN
    have hNz : z ≤ N := le_of_lt hzN
    have hInt1 : IntervalIntegrable (fun x : ℝ => ε / x) volume z N := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hNz]
      exact ContinuousOn.div continuousOn_const continuousOn_id
        (fun x hx => ne_of_gt (lt_of_lt_of_le hz hx.1))
    have hInt2 : IntervalIntegrable (fun x : ℝ => u x ^ 2) volume z N := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hNz]
      exact hint.mono_set (fun x hx => hx.1)
    have hcmp : ∫ x in z..N, ε / x ≤ ∫ x in z..N, u x ^ 2 :=
      intervalIntegral.integral_mono_on_of_le_Ioo hNz hInt1 hInt2 (fun x hx => by
        have hx0 : 0 < x := lt_trans hz hx.1
        rw [div_le_iff₀ hx0]
        linarith [hcon x hx.1])
    have h2 : ∫ x in z..N, u x ^ 2 ≤ ∫ x in Set.Ioi z, u x ^ 2 := by
      rw [intervalIntegral.integral_of_le hNz]
      exact MeasureTheory.setIntegral_mono_set hint
        (Filter.Eventually.of_forall fun x => sq_nonneg _)
        (Filter.Eventually.of_forall fun x hx => hx.1)
    have h3 : ∫ x in z..N, ε / x = ε * Real.log (N / z) := by
      have hdiv : (fun x : ℝ => ε / x) = fun x : ℝ => ε * x⁻¹ := by
        funext x; rw [div_eq_mul_inv]
      rw [hdiv, intervalIntegral.integral_const_mul,
        integral_inv_of_pos hz (lt_trans hz hzN)]
    linarith
  set N : ℝ := z * Real.exp (|(∫ x in Set.Ioi z, u x ^ 2)| / ε + 1) with hN
  have hcpos : 0 < |(∫ x in Set.Ioi z, u x ^ 2)| / ε + 1 := by
    have h1 : 0 ≤ |(∫ x in Set.Ioi z, u x ^ 2)| / ε :=
      div_nonneg (abs_nonneg _) (le_of_lt hε)
    linarith
  have hzN : z < N := by
    rw [hN]
    have h : z * 1 < z * Real.exp (|(∫ x in Set.Ioi z, u x ^ 2)| / ε + 1) :=
      mul_lt_mul_of_pos_left (Real.one_lt_exp_iff.mpr hcpos) hz
    simpa using h
  have hlog : ε * Real.log (N / z) = |(∫ x in Set.Ioi z, u x ^ 2)| + ε := by
    have hNz' : N / z = Real.exp (|(∫ x in Set.Ioi z, u x ^ 2)| / ε + 1) := by
      rw [hN, mul_div_cancel_left₀ _ (ne_of_gt hz)]
    rw [hNz', Real.log_exp]
    have hεne : ε ≠ 0 := ne_of_gt hε
    field_simp
  have hcontra := hstep N hzN
  rw [hlog] at hcontra
  have habs : (∫ x in Set.Ioi z, u x ^ 2) ≤ |(∫ x in Set.Ioi z, u x ^ 2)| :=
    le_abs_self _
  linarith

/-- The pointwise bound `|(x (v x w x)²)'| ≤ 4 (v w)² + (x v' w)²` on `[0,∞)`. -/
private lemma agmon_deriv_bound (v v' : ℝ → ℝ) (x : ℝ) (hx : x ∈ Work.Spaces.Iz) :
    |Work.FTS_RegExport.RXT.agmonFderiv v v' x|
      ≤ 4 * (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2 := by
  have hx0 : 0 ≤ x := hx
  have hb : |(x - 3) / (1 + x)| ≤ 3 := by
    have h1x : (0 : ℝ) < 1 + x := by linarith
    rw [abs_div, abs_of_pos h1x, div_le_iff₀ h1x]
    by_cases h : x ≤ 3
    · rw [abs_of_nonpos (by linarith)]; nlinarith
    · push_neg at h
      rw [abs_of_pos (by linarith)]; nlinarith
  have hkey : Work.FTS_RegExport.RXT.agmonFderiv v v' x
      = 2 * (v x * Work.Spaces.w x) * (x * v' x * Work.Spaces.w x)
        + (v x * Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x)) := by
    rw [Work.FTS_RegExport.RXT.agmonFderiv]; ring
  have hAB : 2 * |(v x * Work.Spaces.w x)| * |(x * v' x * Work.Spaces.w x)|
      ≤ (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2 := by
    nlinarith [sq_nonneg (|v x * Work.Spaces.w x| - |x * v' x * Work.Spaces.w x|),
      sq_abs (v x * Work.Spaces.w x), sq_abs (x * v' x * Work.Spaces.w x)]
  have hE1 : |2 * (v x * Work.Spaces.w x) * (x * v' x * Work.Spaces.w x)|
      = 2 * |(v x * Work.Spaces.w x)| * |(x * v' x * Work.Spaces.w x)| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hE2 : |(v x * Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))|
      = (v x * Work.Spaces.w x) ^ 2 * |(x - 3) / (1 + x)| := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  rw [hkey]
  calc |2 * (v x * Work.Spaces.w x) * (x * v' x * Work.Spaces.w x)
          + (v x * Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))|
      ≤ |2 * (v x * Work.Spaces.w x) * (x * v' x * Work.Spaces.w x)|
          + |(v x * Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))| := abs_add_le _ _
    _ = 2 * |(v x * Work.Spaces.w x)| * |(x * v' x * Work.Spaces.w x)|
          + (v x * Work.Spaces.w x) ^ 2 * |(x - 3) / (1 + x)| := by rw [hE1, hE2]
    _ ≤ (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2
          + (v x * Work.Spaces.w x) ^ 2 * 3 := by
        refine add_le_add hAB ?_
        exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = 4 * (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2 := by ring

theorem v2_agmonZ_noDecay {v v' : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt v (v' x) x)
    (hint1 : MeasureTheory.IntegrableOn (fun x => (v x * Work.Spaces.w x) ^ 2) Work.Spaces.Iz)
    (hint2 : MeasureTheory.IntegrableOn (fun x => (x * v' x * Work.Spaces.w x) ^ 2) Work.Spaces.Iz) :
    (v z) ^ 2 * (Work.Spaces.w z) ^ 2 * z
      ≤ 4 * (∫ x in Set.Ioi z, (v x * Work.Spaces.w x) ^ 2)
        + ∫ x in Set.Ioi z, (x * v' x * Work.Spaces.w x) ^ 2 := by
  -- `(z, ∞) ⊆ [0, ∞)`
  have hsub : Set.Ioi z ⊆ Work.Spaces.Iz := fun x hx => le_of_lt (lt_trans hz hx)
  have hvcont : ContinuousOn v (Set.Ioi (0 : ℝ)) :=
    fun x hx => (hderiv x hx).differentiableAt.continuousAt.continuousWithinAt
  -- arbitrarily small values of `agmonF v` at arbitrarily large points
  have hsmall : ∀ ε > 0, ∃ R : ℝ, z ≤ R ∧ Work.FTS_RegExport.RXT.agmonF v R ≤ ε := by
    intro ε hε
    obtain ⟨R, hzR, hR⟩ :=
      agmon_small_value hz (hint1.mono_set hsub) ε hε
    exact ⟨R, le_of_lt hzR, hR⟩
  -- the pointwise derivative of `agmonF v`
  have hFderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.FTS_RegExport.RXT.agmonF v)
        (Work.FTS_RegExport.RXT.agmonFderiv v v' x) x :=
    Work.FTS_RegExport.RXT.AgmonND.hasDerivAt_agmonF hderiv
  -- the pointwise bound for that derivative
  have hF'bound : ∀ x ∈ Work.Spaces.Iz,
      |Work.FTS_RegExport.RXT.agmonFderiv v v' x|
        ≤ 4 * (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2 :=
    fun x hx => agmon_deriv_bound v v' x hx
  -- integrability of the dominating function
  have hgint : MeasureTheory.IntegrableOn
      (fun x => 4 * (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2)
      Work.Spaces.Iz := (hint1.const_mul 4).add hint2
  have hIz_eq : volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [Work.Spaces.Iz, MeasureTheory.restrict_Ioi_eq_restrict_Ici]
  -- `v'` agrees a.e. with `deriv v` on `(0,∞)`, hence is a.e. strongly measurable there
  have hv'meas : AEStronglyMeasurable v' (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (aestronglyMeasurable_deriv v volume).restrict.congr
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => (hderiv x hx).deriv))
  have haesm : AEStronglyMeasurable (Work.FTS_RegExport.RXT.agmonFderiv v v')
      (volume.restrict Work.Spaces.Iz) := by
    rw [hIz_eq]
    have hvc : AEStronglyMeasurable v (volume.restrict (Set.Ioi (0 : ℝ))) :=
      hvcont.aestronglyMeasurable measurableSet_Ioi
    have hwc : AEStronglyMeasurable (fun x : ℝ => Work.Spaces.w x)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      Work.FTS_RegExport.RXT.continuousOn_w_Ioi.aestronglyMeasurable measurableSet_Ioi
    have hc3 : AEStronglyMeasurable (fun x : ℝ => (x - 3) / (1 + x))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      have h2 : ContinuousOn (fun x : ℝ => 1 + x) (Set.Ioi (0 : ℝ)) :=
        continuousOn_const.add continuousOn_id
      exact ((continuousOn_id.sub continuousOn_const).div h2
        (fun x hx => by have hx0 : 0 < x := hx; exact ne_of_gt (by linarith))).aestronglyMeasurable
        measurableSet_Ioi
    have h1 : AEStronglyMeasurable
        (fun x : ℝ => 2 * v x * (x * v' x) * (Work.Spaces.w x) ^ 2)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (((hvc.const_mul 2).mul (aestronglyMeasurable_id.mul hv'meas)).mul (hwc.pow 2))
    have h2 : AEStronglyMeasurable
        (fun x : ℝ => (v x) ^ 2 * (Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x)))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (((hvc.pow 2).mul (hwc.pow 2)).mul hc3)
    exact (h1.add h2).congr (Filter.Eventually.of_forall fun x => by
      simp only [Work.FTS_RegExport.RXT.agmonFderiv, Pi.add_apply])
  have hF'int : MeasureTheory.IntegrableOn (Work.FTS_RegExport.RXT.agmonFderiv v v')
      Work.Spaces.Iz :=
    hgint.mono' haesm (ae_restrict_of_forall_mem measurableSet_Ici fun x hx => by
      rw [Real.norm_eq_abs]; exact hF'bound x hx)
  have hAbsOn : MeasureTheory.IntegrableOn
      (fun x => |Work.FTS_RegExport.RXT.agmonFderiv v v' x|) Work.Spaces.Iz := hF'int.abs
  have hAbsOnz : MeasureTheory.IntegrableOn
      (fun x => |Work.FTS_RegExport.RXT.agmonFderiv v v' x|) (Set.Ioi z) :=
    hAbsOn.mono_set hsub
  have hgintz : MeasureTheory.IntegrableOn
      (fun x => 4 * (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2)
      (Set.Ioi z) := hgint.mono_set hsub
  -- the fundamental theorem of calculus on `[z, X]`
  have htail : ∀ X : ℝ, z ≤ X → Work.FTS_RegExport.RXT.agmonF v z
      ≤ Work.FTS_RegExport.RXT.agmonF v X
        + ∫ x in Set.Ioi z, |Work.FTS_RegExport.RXT.agmonFderiv v v' x| := by
    intro X hzX
    have hFcont : ContinuousOn (Work.FTS_RegExport.RXT.agmonF v) (Set.Icc z X) := by
      have hv : ContinuousOn v (Set.Icc z X) := hvcont.mono (fun x hx => lt_of_lt_of_le hz hx.1)
      have hw : ContinuousOn Work.Spaces.w (Set.Icc z X) :=
        Work.FTS_RegExport.RXT.continuousOn_w_Ioi.mono (fun x hx => lt_of_lt_of_le hz hx.1)
      have h := ((hv.pow 2).mul (hw.pow 2)).mul continuousOn_id
      refine h.congr (fun y _ => ?_)
      simp only [Work.FTS_RegExport.RXT.agmonF, Pi.mul_apply, Pi.pow_apply, id_eq]
      ring
    have hd : ∀ x ∈ Set.Ioo z X,
        HasDerivAt (Work.FTS_RegExport.RXT.agmonF v)
          (Work.FTS_RegExport.RXT.agmonFderiv v v' x) x :=
      fun x hx => hFderiv x (lt_trans hz hx.1)
    have hintv : IntervalIntegrable (Work.FTS_RegExport.RXT.agmonFderiv v v') volume z X := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hzX]
      exact hF'int.mono_set (fun x hx => le_of_lt (lt_trans hz hx.1))
    have hFTC : ∫ x in z..X, Work.FTS_RegExport.RXT.agmonFderiv v v' x
        = Work.FTS_RegExport.RXT.agmonF v X - Work.FTS_RegExport.RXT.agmonF v z :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hzX hFcont hd hintv
    have h3abs : |∫ x in z..X, Work.FTS_RegExport.RXT.agmonFderiv v v' x|
        ≤ ∫ x in Set.Ioi z, |Work.FTS_RegExport.RXT.agmonFderiv v v' x| := by
      rw [intervalIntegral.integral_of_le hzX]
      refine le_trans (MeasureTheory.abs_integral_le_integral_abs) ?_
      exact MeasureTheory.setIntegral_mono_set hAbsOnz
        (Filter.Eventually.of_forall fun x => abs_nonneg _)
        (Filter.Eventually.of_forall fun x hx => hx.1)
    have h3 : -(∫ x in z..X, Work.FTS_RegExport.RXT.agmonFderiv v v' x)
        ≤ ∫ x in Set.Ioi z, |Work.FTS_RegExport.RXT.agmonFderiv v v' x| :=
      le_trans (neg_le_abs _) h3abs
    linarith [hFTC, h3]
  -- `inf_{X ≥ z} agmonF v X = 0` gives the boundary term at `+∞` for free
  have hmain : Work.FTS_RegExport.RXT.agmonF v z
      ≤ ∫ x in Set.Ioi z, |Work.FTS_RegExport.RXT.agmonFderiv v v' x| := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨R, hzR, hR⟩ := hsmall ε hε
    have h1 := htail R hzR
    linarith
  have hle : ∫ x in Set.Ioi z, |Work.FTS_RegExport.RXT.agmonFderiv v v' x|
      ≤ ∫ x in Set.Ioi z,
          (4 * (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2) := by
    refine integral_mono_ae hAbsOnz hgintz ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioi
      (fun x hx => hF'bound x (le_of_lt (lt_trans hz hx)))
  have hsplit : ∫ x in Set.Ioi z,
        (4 * (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2)
      = 4 * (∫ x in Set.Ioi z, (v x * Work.Spaces.w x) ^ 2)
        + ∫ x in Set.Ioi z, (x * v' x * Work.Spaces.w x) ^ 2 := by
    rw [integral_add ((hint1.mono_set hsub).const_mul 4) (hint2.mono_set hsub),
      integral_const_mul]
  calc (v z) ^ 2 * (Work.Spaces.w z) ^ 2 * z
      = Work.FTS_RegExport.RXT.agmonF v z := (Work.FTS_RegExport.RXT.agmonF_eq v z).symm
    _ ≤ ∫ x in Set.Ioi z, |Work.FTS_RegExport.RXT.agmonFderiv v v' x| := hmain
    _ ≤ ∫ x in Set.Ioi z,
          (4 * (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2) := hle
    _ = 4 * (∫ x in Set.Ioi z, (v x * Work.Spaces.w x) ^ 2)
          + ∫ x in Set.Ioi z, (x * v' x * Work.Spaces.w x) ^ 2 := hsplit

end Work.FTS_RegExport.RXT.Slots
