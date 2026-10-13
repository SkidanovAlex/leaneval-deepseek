/-
# `Work.FTS.EllSol.EllPkgAux.sKer_conv_integral`

The mollifier `sKer δ` (`MollDefs`) is a smooth, nonnegative bump of radius `δ > 0` with
total mass `1`.  Hence, for an integrable `φ`, the convolution `s ↦ ∫ t, sKer δ (s - t) * φ t`
is integrable and has the same total integral as `φ`:

  `∫ s, ∫ t, sKer δ (s - t) * φ t = (∫ sKer δ) * (∫ φ) = ∫ φ`.

This is the standard `∫ (ρ * φ) = (∫ ρ) (∫ φ)` for a kernel of unit mass.  The proof uses
Mathlib's convolution API (`MeasureTheory.integrable_convolution`,
`MeasureTheory.integral_convolution`) after identifying the iterated integral with the
convolution `(φ ⋆[mul] sKer δ) s = ∫ t, φ t * sKer δ (s - t)`, together with the elementary
facts that `sKer δ` is continuous with compact support (so integrable) and that
`∫ sKer δ = 1` (`sKer_integral_eq_one`).
-/
import Mathlib.Analysis.Convolution
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory

namespace Work.FTS.EllSol.EllPkgAux

open Work.FTS.EllSol.PkgK5.K5c

/-- `sKer δ` is continuous. -/
private lemma sKer_continuous (δ : ℝ) : Continuous (sKer δ) := by
  have h : sKer δ = fun t : ℝ => (δ * sMass)⁻¹ * sBump (t / δ) := by
    funext t; rw [sKer]
  rw [h]
  exact continuous_const.mul (sBump_continuous.comp (continuous_id.div_const δ))

/-- `sKer δ` is supported in `[-δ, δ]`, hence has compact support. -/
private lemma sKer_hasCompactSupport {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (fun u : ℝ => sKer δ u) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-δ) δ) isCompact_Icc ?_
  intro t ht
  rw [Function.mem_support] at ht
  have hlt : |t| < δ := by
    by_contra h
    exact ht (sKer_eq_zero_of_le_abs hδ (not_lt.mp h))
  rw [abs_lt] at hlt
  exact ⟨le_of_lt hlt.1, le_of_lt hlt.2⟩

/-- `sKer δ` is integrable. -/
private lemma sKer_integrable {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun u : ℝ => sKer δ u) :=
  (sKer_continuous δ).integrable_of_hasCompactSupport (sKer_hasCompactSupport hδ)

theorem sKer_conv_integral (δ : ℝ) (hδ : 0 < δ) {φ : ℝ → ℝ} (hφ : MeasureTheory.Integrable φ) :
    MeasureTheory.Integrable (fun s : ℝ => ∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (s - t) * φ t)
      ∧ (∫ s : ℝ, ∫ t : ℝ, Work.FTS.EllSol.PkgK5.K5c.sKer δ (s - t) * φ t) = ∫ t : ℝ, φ t := by
  have hK : Integrable (fun u : ℝ => sKer δ u) := sKer_integrable hδ
  have hKmass : ∫ u : ℝ, sKer δ u = 1 := sKer_integral_eq_one hδ
  -- the iterated integral is the convolution `φ ⋆ sKer δ`
  have hconv : ∀ s : ℝ,
      convolution φ (fun u : ℝ => sKer δ u) (ContinuousLinearMap.mul ℝ ℝ) volume s
        = ∫ t : ℝ, sKer δ (s - t) * φ t := by
    intro s
    rw [convolution_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
  constructor
  · refine (hφ.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hK).congr ?_
    filter_upwards with s
    exact hconv s
  · have hint : ∫ s : ℝ,
        convolution φ (fun u : ℝ => sKer δ u) (ContinuousLinearMap.mul ℝ ℝ) volume s
        = (∫ t : ℝ, φ t) * (∫ u : ℝ, sKer δ u) :=
      integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hφ hK
    calc (∫ s : ℝ, ∫ t : ℝ, sKer δ (s - t) * φ t)
        = ∫ s : ℝ, convolution φ (fun u : ℝ => sKer δ u) (ContinuousLinearMap.mul ℝ ℝ)
            volume s := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun s => (hconv s).symm)
      _ = (∫ t : ℝ, φ t) * (∫ u : ℝ, sKer δ u) := hint
      _ = ∫ t : ℝ, φ t := by rw [hKmass, mul_one]

end Work.FTS.EllSol.EllPkgAux
