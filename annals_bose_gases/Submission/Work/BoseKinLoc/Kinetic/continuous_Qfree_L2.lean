import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Kinetic.continuous_Qfree_L2`

Continuity in the parameter `q` of the box mean-free `L²`-mass

    `q ↦ ∫_{Ω(ℓ)} (Q_uψ)² ,   ψ = K q ,  u = 0 ,  Ω(ℓ) = acube ℓ`,

for a jointly continuous family `K : γ × ℝ³ → ℝ` over a locally compact, first countable
parameter space `γ`.

The mathematical content is only the standard continuity of a parametric integral over the
**compact** cube `acube ℓ` (`continuous_parametric_integral_of_continuous`): the box mean
`bsMean ℓ 0 (K q)` is such an integral (times `ℓ⁻³`), and so is `∫ (K q − mean)²`, since
`(q,z) ↦ (K q z − bsMean ℓ 0 (K q))²` is again jointly continuous.  No uniform bound over all
of `γ` is needed: local compactness of `γ` supplies a compact neighbourhood, and the cube is
compact.

## Contents

* `continuous_integral_acube` — the parametric integral `q ↦ ∫_{acube ℓ} K q z`;
* `continuous_bsMean_zero` — its normalised form `q ↦ bsMean ℓ 0 (K q)`;
* `continuous_Qfree_L2` — the target (note `Qfree ℓ 0 (K q) z = K q z − bsMean ℓ 0 (K q)`,
  definitionally).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseKinLoc.Kinetic

/-- The centred cube `acube ℓ` is compact for `ℓ > 0`. -/
private lemma acube_isCompact_of_pos {ℓ : ℝ} (hℓ : 0 < ℓ) :
    IsCompact (Submission.BoseGases.acube ℓ) :=
  (Metric.isCompact_iff_isClosed_bounded).mpr
    ⟨Submission.BoseGases.acube_isClosed ℓ, Submission.BoseGases.acube_isBounded ℓ hℓ.le⟩

/-- **The integral over the centred cube is continuous in the parameter**, for a jointly
continuous integrand on a locally compact, first countable parameter space. -/
theorem continuous_integral_acube {γ : Type*} [TopologicalSpace γ] [FirstCountableTopology γ]
    [LocallyCompactSpace γ] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {K : γ → ℝ³ → ℝ}
    (hK : Continuous fun p : γ × ℝ³ => K p.1 p.2) :
    Continuous fun q : γ => ∫ z in Submission.BoseGases.acube ℓ, K q z :=
  continuous_parametric_integral_of_continuous (μ := volume) hK (acube_isCompact_of_pos hℓ)

/-- **The box mean `bsMean ℓ 0 (K q) = ℓ⁻³ ∫_{acube ℓ} K q` is continuous in the parameter.** -/
theorem continuous_bsMean_zero {γ : Type*} [TopologicalSpace γ] [FirstCountableTopology γ]
    [LocallyCompactSpace γ] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {K : γ → ℝ³ → ℝ}
    (hK : Continuous fun p : γ × ℝ³ => K p.1 p.2) :
    Continuous fun q : γ => Work.BSKinetic.bsMean ℓ 0 (K q) := by
  have h := (continuous_integral_acube hℓ hK).const_mul ((ℓ ^ 3)⁻¹)
  simpa [Work.BSKinetic.bsMean] using h

theorem continuous_Qfree_L2 {γ : Type*} [TopologicalSpace γ] [FirstCountableTopology γ]
    [LocallyCompactSpace γ] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {K : γ → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hK : Continuous fun p : γ × EuclideanSpace ℝ (Fin 3) => K p.1 p.2) :
    Continuous fun q : γ => ∫ z in Submission.BoseGases.acube ℓ,
      (Work.BoseKinLoc.Qfree ℓ 0 (K q) z) ^ 2 := by
  have hs : IsCompact (Submission.BoseGases.acube ℓ) := acube_isCompact_of_pos hℓ
  have hmean := continuous_bsMean_zero hℓ hK
  have hmain : Continuous fun q : γ => ∫ z in Submission.BoseGases.acube ℓ,
      (K q z - Work.BSKinetic.bsMean ℓ 0 (K q)) ^ 2 := by
    apply continuous_parametric_integral_of_continuous (μ := volume) _ hs
    exact (hK.sub (hmean.comp continuous_fst)).pow 2
  simpa only [Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ] using hmain

end Work.BoseKinLoc.Kinetic
