import Mathlib
import Submission.Work.GM.Affine.nearcorr_defs
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.WinMass_basic

/-!
# Continuity of the smoothed profile `Afun` (GM §9)

`Afun f M₂ K T v = ∫ u, Hprof f M₂ (v - s u) ψ u` with `s = smScale K T M₂` and
`ψ = psiSmooth`.  The kernel `ψ` is concentrated on `[-1,1]`, so for `v` in a fixed ball
around a point `v₀` the profile is evaluated only on a compact interval.  As `f` is
continuous, `Hprof f M₂` is continuous, hence bounded on that interval, and the dominated
convergence theorem applies: the integrand is separately continuous in `v` and dominated by
`‖Hprof f M₂ x₀‖ · ‖ψ u‖`, an integrable function (a constant multiple of the norm of the
compactly supported continuous `ψ`).  No compact-support hypothesis on `f` is needed, and no
sign or non-vanishing hypothesis on `s`, `M₂`, `K`, `T` is needed either.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

theorem nearcorr_Afun_continuous {f : ℝ → ℝ} (hf : Continuous f) (M₂ K T : ℝ) :
    Continuous (Afun f M₂ K T) := by
  have hHcont : Continuous (Hprof f M₂) := Hprof_continuous hf M₂
  have hψcont : Continuous psiSmooth := psiSmooth_contDiff.continuous
  have hψcs : HasCompactSupport psiSmooth :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (fun x hx => psiSmooth_support hx)
  have hψint : Integrable (fun u : ℝ => ‖psiSmooth u‖) volume :=
    (hψcont.integrable_of_hasCompactSupport hψcs).norm
  rw [continuous_iff_continuousAt]
  intro v₀
  show ContinuousAt (fun v : ℝ => ∫ u : ℝ,
    Hprof f M₂ (v - smScale K T M₂ * u) * psiSmooth u) v₀
  -- A constant dominating the profile on the compact region reached by the kernel.
  obtain ⟨x₀, _hx₀K, hx₀max⟩ :=
    IsCompact.exists_isMaxOn
      (s := Set.Icc (v₀ - (1 + |smScale K T M₂|)) (v₀ + (1 + |smScale K T M₂|)))
      isCompact_Icc
      (Set.nonempty_Icc.mpr (by linarith [abs_nonneg (smScale K T M₂)]))
      (hHcont.norm.continuousOn)
  refine continuousAt_of_dominated
    (F := fun v u => Hprof f M₂ (v - smScale K T M₂ * u) * psiSmooth u)
    (bound := fun u => ‖Hprof f M₂ x₀‖ * ‖psiSmooth u‖) ?_ ?_ ?_ ?_
  · -- a.e. strong measurability of the integrand, which is continuous in `u`
    exact Filter.Eventually.of_forall (fun v =>
      ((hHcont.comp (continuous_const.sub (continuous_const.mul continuous_id))).mul
        hψcont).aestronglyMeasurable)
  · -- domination: for `v` near `v₀` the profile stays on the compact interval
    filter_upwards [Metric.ball_mem_nhds v₀ one_pos] with v hv
    refine Filter.Eventually.of_forall (fun u => ?_)
    rw [norm_mul]
    by_cases hψu : psiSmooth u = 0
    · rw [hψu, norm_zero, mul_zero, mul_zero]
    · have hu : u ∈ Set.Icc (-1 : ℝ) 1 := psiSmooth_support hψu
      have hdist : |v - smScale K T M₂ * u - v₀| ≤ 1 + |smScale K T M₂| := by
        have hu1 : |u| ≤ 1 := abs_le.mpr hu
        have h1 : |v - v₀| < 1 := by
          rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] at hv; exact hv
        calc |v - smScale K T M₂ * u - v₀|
            = |(v - v₀) - smScale K T M₂ * u| := by ring_nf
          _ ≤ |v - v₀| + |smScale K T M₂ * u| := abs_sub _ _
          _ = |v - v₀| + |smScale K T M₂| * |u| := by rw [abs_mul]
          _ ≤ 1 + |smScale K T M₂| := by
              have h2 := abs_nonneg (smScale K T M₂)
              nlinarith
      have hmem : v - smScale K T M₂ * u ∈
          Set.Icc (v₀ - (1 + |smScale K T M₂|)) (v₀ + (1 + |smScale K T M₂|)) := by
        rw [Set.mem_Icc]
        rw [abs_le] at hdist
        constructor <;> linarith [hdist.1, hdist.2]
      exact mul_le_mul_of_nonneg_right (hx₀max hmem) (norm_nonneg _)
  · exact hψint.const_mul ‖Hprof f M₂ x₀‖
  · -- separate continuity of the integrand in `v`
    exact Filter.Eventually.of_forall (fun u =>
      ((hHcont.comp (continuous_id.sub continuous_const)).mul continuous_const).continuousAt)

end

end Work.GM.Affine
