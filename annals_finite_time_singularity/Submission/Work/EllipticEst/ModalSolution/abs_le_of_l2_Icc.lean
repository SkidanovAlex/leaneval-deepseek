import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.ModalSolution

open MeasureTheory Set intervalIntegral

/-- **One-dimensional Sobolev `L∞`–`L²` bound on a closed interval.**  For a function `v` of
class `C¹` on `[c,d]` (`c < d`) and any `θ ∈ [c,d]`,
`|v θ| ≤ ‖v‖_{L²(c,d)}/√(d-c) + √(d-c)·‖v'‖_{L²(c,d)}`.

The proof picks a point `y₀` where `|v|` is minimal on `[c,d]` (so `|v y₀|` is at most the mean of
`|v|`, hence controlled by `∫ v²`), writes `v θ - v y₀ = ∫_{y₀}^{θ} deriv v` (FTC), and bounds the
latter by Cauchy–Schwarz against `∫ (deriv v)²` over the whole interval.

Derivatives are handled through `derivWithin v (Icc c d)`, which is continuous on `[c,d]`, and which
agrees with `deriv v` on the interior. -/
theorem abs_le_of_l2_Icc (v : ℝ → ℝ) {c d : ℝ} (hcd : c < d) {θ : ℝ} (hθ : θ ∈ Set.Icc c d)
    (hv : ContDiffOn ℝ 1 v (Set.Icc c d)) :
    |v θ| ≤ Real.sqrt (∫ x in c..d, v x ^ 2) / Real.sqrt (d - c)
      + Real.sqrt (d - c) * Real.sqrt (∫ x in c..d, (deriv v x) ^ 2) := by
  have hle : c ≤ d := hcd.le
  have hLpos : 0 < d - c := sub_pos.mpr hcd
  have hLnonneg : 0 ≤ d - c := hLpos.le
  have hcont : ContinuousOn v (Set.Icc c d) := hv.continuousOn
  -- the continuous representative of the derivative
  set g : ℝ → ℝ := derivWithin v (Set.Icc c d) with hgdef
  have hgcont : ContinuousOn g (Set.Icc c d) := by
    rw [hgdef]
    exact hv.continuousOn_derivWithin (uniqueDiffOn_Icc hcd) le_rfl
  haveI hfinIcc : IsFiniteMeasure (volume.restrict (Set.Icc c d)) := by
    rw [isFiniteMeasure_restrict, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  -- `g` agrees with `deriv v` a.e.
  have hbad : volume {x : ℝ | x ∈ Set.Icc c d ∧ g x ≠ deriv v x} = 0 := by
    have hsub : {x : ℝ | x ∈ Set.Icc c d ∧ g x ≠ deriv v x} ⊆ ({c, d} : Set ℝ) := by
      intro x hx
      by_contra hxc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hxc
      have hx1 : c < x := lt_of_le_of_ne hx.1.1 (Ne.symm hxc.1)
      have hx2 : x < d := lt_of_le_of_ne hx.1.2 hxc.2
      refine hx.2 ?_
      rw [hgdef]
      exact derivWithin_of_mem_nhds (Icc_mem_nhds hx1 hx2)
    refine measure_mono_null hsub ?_
    rw [Set.insert_eq]
    exact measure_union_null (measure_singleton c) (measure_singleton d)
  have hae_restrict : ∀ {s : Set ℝ}, MeasurableSet s → s ⊆ Set.Icc c d →
      g =ᵐ[volume.restrict s] deriv v := by
    intro s hs hsub
    change ∀ᵐ x ∂volume.restrict s, g x = deriv v x
    rw [MeasureTheory.ae_restrict_iff' hs, MeasureTheory.ae_iff]
    have hset : {x : ℝ | ¬(x ∈ s → g x = deriv v x)} = {x : ℝ | x ∈ s ∧ g x ≠ deriv v x} := by
      ext x
      simp only [not_imp]
    rw [hset]
    exact measure_mono_null
      (fun x hx => (⟨hsub hx.1, hx.2⟩ : x ∈ {y : ℝ | y ∈ Set.Icc c d ∧ g y ≠ deriv v y})) hbad
  -- boundedness/MemLp of `g` and `deriv v` on `[c,d]`
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hgcont
  have hgM : MemLp g 2 (volume.restrict (Set.Icc c d)) := by
    refine MemLp.of_bound (hgcont.aestronglyMeasurable_of_subset_isCompact isCompact_Icc
      measurableSet_Icc subset_rfl) C ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with x hx
    exact hC x hx
  have hdvM : MemLp (deriv v) 2 (volume.restrict (Set.Icc c d)) :=
    MemLp.ae_eq (hae_restrict measurableSet_Icc subset_rfl) hgM
  have hdvInt : IntegrableOn (fun x => (deriv v x) ^ 2) (Set.Icc c d) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hdvM.aestronglyMeasurable).mp hdvM
  -- minimal point of `|v|`
  obtain ⟨y₀, hy₀, hmin⟩ :=
    isCompact_Icc.exists_isMinOn ⟨c, ⟨le_rfl, hle⟩⟩ hcont.abs
  -- interval inclusions
  have huIcc_sub : Set.uIcc y₀ θ ⊆ Set.Icc c d := by
    intro x hx
    simp only [Set.uIcc, Set.mem_Icc] at hx
    exact ⟨le_trans (le_min hy₀.1 hθ.1) hx.1, le_trans hx.2 (max_le hy₀.2 hθ.2)⟩
  have huIoc_sub : Set.uIoc y₀ θ ⊆ Set.Icc c d := by
    intro x hx
    simp only [Set.uIoc, Set.mem_Ioc] at hx
    exact ⟨le_trans (le_min hy₀.1 hθ.1) hx.1.le, le_trans hx.2 (max_le hy₀.2 hθ.2)⟩
  have huIoc_meas : MeasurableSet (Set.uIoc y₀ θ) := measurableSet_uIoc
  -- the `L²` bound on `|v|`
  have hIntV2 : IntervalIntegrable (fun x => v x ^ 2) volume c d :=
    (hcont.pow 2).intervalIntegrable_of_Icc hle
  have hpt : ∀ x ∈ Set.Icc c d, (|v y₀| ^ 2 : ℝ) ≤ v x ^ 2 := by
    intro x hx
    have h1 : |v y₀| ≤ |v x| := hmin hx
    have h2 : |v y₀| ^ 2 ≤ |v x| ^ 2 := sq_le_sq.mpr (by simpa using h1)
    rwa [sq_abs (v x)] at h2
  have hconst_eq : (∫ x in c..d, (|v y₀| ^ 2 : ℝ)) = |v y₀| ^ 2 * (d - c) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hcv : (|v y₀| ^ 2) * (d - c) ≤ ∫ x in c..d, v x ^ 2 := by
    rw [← hconst_eq]
    exact integral_mono_on hle (intervalIntegrable_const (c := |v y₀| ^ 2)) hIntV2 hpt
  have hsqrt_y0 : |v y₀| ≤ Real.sqrt (∫ x in c..d, v x ^ 2) / Real.sqrt (d - c) := by
    have hsq : (|v y₀| * Real.sqrt (d - c)) ^ 2 ≤ ∫ x in c..d, v x ^ 2 := by
      have hrew : (|v y₀| * Real.sqrt (d - c)) ^ 2 = |v y₀| ^ 2 * (d - c) := by
        rw [mul_pow, Real.sq_sqrt hLnonneg]
      rw [hrew]
      exact hcv
    have hle2 : |v y₀| * Real.sqrt (d - c) ≤ Real.sqrt (∫ x in c..d, v x ^ 2) :=
      Real.le_sqrt_of_sq_le hsq
    rw [le_div_iff₀ (Real.sqrt_pos_of_pos hLpos)]
    exact hle2
  -- Cauchy–Schwarz over the subinterval, against `g`
  haveI hfinU : IsFiniteMeasure (volume.restrict (Set.uIoc y₀ θ)) := by
    rw [isFiniteMeasure_restrict]
    exact ne_of_lt (lt_of_le_of_lt (measure_mono huIoc_sub)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top))
  have hMemLp_absg : MemLp (fun x => |g x|) 2 (volume.restrict (Set.uIoc y₀ θ)) := by
    refine MemLp.of_bound (hgcont.abs.aestronglyMeasurable_of_subset_isCompact isCompact_Icc
      huIoc_meas huIoc_sub) C ?_
    filter_upwards [MeasureTheory.ae_restrict_mem huIoc_meas] with x hx
    simpa only [Real.norm_eq_abs, abs_abs] using hC x (huIoc_sub hx)
  have hMemLp_one : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Set.uIoc y₀ θ)) :=
    memLp_const 1
  have hcs := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt
    (u := fun x => |g x|) (v := fun _ : ℝ => (1 : ℝ)) (s := Set.uIoc y₀ θ)
    hMemLp_absg hMemLp_one
  have hCS : ∫ x in Set.uIoc y₀ θ, |g x| ≤
      Real.sqrt (∫ x in Set.uIoc y₀ θ, g x ^ 2) * Real.sqrt ((volume (Set.uIoc y₀ θ)).toReal) := by
    have hL : |∫ x in Set.uIoc y₀ θ, |g x| * 1| = ∫ x in Set.uIoc y₀ θ, |g x| := by
      simp only [mul_one]
      exact abs_of_nonneg (MeasureTheory.integral_nonneg_of_ae
        (μ := volume.restrict (Set.uIoc y₀ θ))
        (Filter.Eventually.of_forall (fun x => abs_nonneg (g x))))
    have hR1 : (∫ x in Set.uIoc y₀ θ, |g x| ^ 2) = ∫ x in Set.uIoc y₀ θ, g x ^ 2 := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      simp only [sq_abs]
    have hR2 : (∫ x in Set.uIoc y₀ θ, ((1 : ℝ)) ^ 2) = (volume (Set.uIoc y₀ θ)).toReal := by
      simp only [one_pow, MeasureTheory.setIntegral_one_eq_measureReal,
        MeasureTheory.Measure.real_def]
    rw [← hL, ← hR1, ← hR2]
    exact hcs
  -- comparison with the full-interval quantities
  have hsvol : (volume (Set.uIoc y₀ θ)).toReal ≤ d - c := by
    have h1 : volume (Set.uIoc y₀ θ) ≤ volume (Set.Icc c d) := measure_mono huIoc_sub
    have h2 : volume (Set.Icc c d) ≠ ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    refine (ENNReal.toReal_mono h2 h1).trans_eq ?_
    rw [Real.volume_Icc, ENNReal.toReal_ofReal hLnonneg]
  have hsg : ∫ x in Set.uIoc y₀ θ, g x ^ 2 = ∫ x in Set.uIoc y₀ θ, (deriv v x) ^ 2 := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hae_restrict huIoc_meas huIoc_sub] with x hx
    rw [hx]
  have hsB : ∫ x in Set.uIoc y₀ θ, (deriv v x) ^ 2 ≤ ∫ x in c..d, (deriv v x) ^ 2 := by
    have hmono := MeasureTheory.setIntegral_mono_set
      (s := Set.uIoc y₀ θ) (t := Set.Icc c d) (f := fun x => (deriv v x) ^ 2) hdvInt
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (Filter.Eventually.of_forall (fun x hx => huIoc_sub hx))
    rwa [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle] at hmono
  -- FTC and the derivative bound
  have hFTC : ∫ x in y₀..θ, deriv v x = v θ - v y₀ :=
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hv.mono huIcc_sub)
  have hB : |v θ - v y₀| ≤
      Real.sqrt (d - c) * Real.sqrt (∫ x in c..d, (deriv v x) ^ 2) := by
    calc |v θ - v y₀|
        = |∫ x in y₀..θ, deriv v x| := by simp only [hFTC]
      _ = |∫ x in Set.uIoc y₀ θ, deriv v x| :=
            intervalIntegral.abs_integral_eq_abs_integral_uIoc (deriv v)
      _ ≤ ∫ x in Set.uIoc y₀ θ, |deriv v x| := by
            simpa only [Real.norm_eq_abs] using
              (MeasureTheory.norm_integral_le_integral_norm
                (μ := volume.restrict (Set.uIoc y₀ θ)) (fun x => deriv v x))
      _ = ∫ x in Set.uIoc y₀ θ, |g x| := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [hae_restrict huIoc_meas huIoc_sub] with x hx
            rw [hx]
      _ ≤ Real.sqrt (∫ x in Set.uIoc y₀ θ, g x ^ 2) *
            Real.sqrt ((volume (Set.uIoc y₀ θ)).toReal) := hCS
      _ ≤ Real.sqrt (∫ x in c..d, (deriv v x) ^ 2) * Real.sqrt (d - c) := by
            have h3 : Real.sqrt (∫ x in Set.uIoc y₀ θ, g x ^ 2) ≤
                Real.sqrt (∫ x in c..d, (deriv v x) ^ 2) := by
              rw [hsg]
              exact Real.sqrt_le_sqrt hsB
            have h4 : Real.sqrt ((volume (Set.uIoc y₀ θ)).toReal) ≤ Real.sqrt (d - c) :=
              Real.sqrt_le_sqrt hsvol
            exact mul_le_mul h3 h4 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt (d - c) * Real.sqrt (∫ x in c..d, (deriv v x) ^ 2) := by ring
  -- assembly
  have hsplit : |v θ| ≤ |v y₀| + |v θ - v y₀| := by
    calc |v θ| = |v y₀ + (v θ - v y₀)| := by congr 1; ring
      _ ≤ |v y₀| + |v θ - v y₀| := abs_add_le _ _
  calc |v θ| ≤ |v y₀| + |v θ - v y₀| := hsplit
    _ ≤ Real.sqrt (∫ x in c..d, v x ^ 2) / Real.sqrt (d - c)
          + Real.sqrt (d - c) * Real.sqrt (∫ x in c..d, (deriv v x) ^ 2) :=
          add_le_add hsqrt_y0 hB

end Work.EllipticEst.ModalSolution
