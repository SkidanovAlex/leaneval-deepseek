/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Deleg/psiDIntegralLimitAlt` — the `δ ↓ 0⁺` limit of the `psiD`-truncated pairing

A self-contained proof of the generic limit lemma used by `Deleg.mixedPairLimit` (the sibling
of `Deleg.psiDIntegralLimit`, written independently as insurance): nested dominated convergence
in `θ` then in `z`, with the angular bump `psiD δ` tending to `1` pointwise on `(0,π/2)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.AeColl.pairFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Deleg

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

theorem psiDIntegralLimitAlt {c : ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Set.Ioi (0 : ℝ))))
    (hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ => G p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))))
    (hGz : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      Integrable (fun θ => G z θ) (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
    (hdom : Integrable (fun z => |c z| *
        ∫ θ, |G z θ| ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      (volume.restrict (Set.Ioi (0 : ℝ)))) :
    Tendsto (fun δ : ℝ => ∫ z, c z *
        (∫ θ, Work.FTS.EllipticEst.AeColl.psiD δ θ * G z θ
          ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
      ∂(volume.restrict (Set.Ioi (0 : ℝ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ z, c z * (∫ θ, G z θ ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))))
        ∂(volume.restrict (Set.Ioi (0 : ℝ))))) := by
  set ν : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) with hν
  have hψc : ∀ δ : ℝ, Continuous (Work.FTS.EllipticEst.AeColl.psiD δ) := fun δ =>
    (Work.FTS.EllipticEst.AeColl.psiD_contDiff δ).continuous
  -- (1) a.e. strong measurability of the integrands
  have hmeas : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (fun z => c z *
        (∫ θ, Work.FTS.EllipticEst.AeColl.psiD δ θ * G z θ ∂ν))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine Filter.Eventually.of_forall (fun δ => ?_)
    have h1 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.psiD δ p.2 * G p.1 p.2)
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod ν) :=
      ((hψc δ).measurable.comp measurable_snd).aestronglyMeasurable.mul hjoint
    exact hc.mul h1.integral_prod_right'
  -- (2) domination by the absolute marginal
  have hpt : ∀ (z : ℝ) (δ θ : ℝ), ‖Work.FTS.EllipticEst.AeColl.psiD δ θ * G z θ‖ ≤ |G z θ| := by
    intro z δ θ
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (Work.FTS.EllipticEst.AeColl.psiD_nonneg δ θ)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Work.FTS.EllipticEst.AeColl.psiD_le_one δ θ)
  have hbound : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ‖c z * (∫ θ, Work.FTS.EllipticEst.AeColl.psiD δ θ * G z θ ∂ν)‖
          ≤ |c z| * ∫ θ, |G z θ| ∂ν := by
    refine Filter.Eventually.of_forall (fun δ => ?_)
    filter_upwards [hGz] with z hzint
    have h3 : ‖∫ θ, Work.FTS.EllipticEst.AeColl.psiD δ θ * G z θ ∂ν‖
        ≤ ∫ θ, |G z θ| ∂ν :=
      le_trans (norm_integral_le_integral_norm _)
        (integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun θ => norm_nonneg _) hzint.norm
          (Filter.Eventually.of_forall fun θ => hpt z δ θ))
    calc ‖c z * (∫ θ, Work.FTS.EllipticEst.AeColl.psiD δ θ * G z θ ∂ν)‖
        = |c z| * ‖∫ θ, Work.FTS.EllipticEst.AeColl.psiD δ θ * G z θ ∂ν‖ := by
          rw [norm_mul, Real.norm_eq_abs]
      _ ≤ |c z| * ∫ θ, |G z θ| ∂ν := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
  -- (3) pointwise convergence for a.e. `z`
  have hlim : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      Tendsto (fun δ : ℝ => c z * (∫ θ, Work.FTS.EllipticEst.AeColl.psiD δ θ * G z θ ∂ν))
        (𝓝[>] (0 : ℝ)) (𝓝 (c z * (∫ θ, G z θ ∂ν))) := by
    filter_upwards [hGz, hjoint.prodMk_left] with z hzint hzslice
    have hinner : Tendsto (fun δ : ℝ =>
        ∫ θ, Work.FTS.EllipticEst.AeColl.psiD δ θ * G z θ ∂ν) (𝓝[>] (0 : ℝ))
        (𝓝 (∫ θ, G z θ ∂ν)) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun θ => |G z θ|)
        ?_ ?_ hzint.norm ?_
      · exact Filter.Eventually.of_forall (fun δ =>
          (hψc δ).measurable.aestronglyMeasurable.mul hzslice)
      · exact Filter.Eventually.of_forall (fun δ =>
          ae_restrict_of_forall_mem measurableSet_Ioo (fun θ _ => hpt z δ θ))
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
        have h := Work.FTS.EllipticEst.AeColl.psiD_tendsto_one θ hθ
        simpa using h.mul_const (G z θ)
    exact hinner.const_mul (c z)
  -- (4) the outer dominated convergence
  exact tendsto_integral_filter_of_dominated_convergence (fun z => |c z| * ∫ θ, |G z θ| ∂ν)
    hmeas hbound hdom hlim

end

end Work.FTS.EllipticEst.Deleg
