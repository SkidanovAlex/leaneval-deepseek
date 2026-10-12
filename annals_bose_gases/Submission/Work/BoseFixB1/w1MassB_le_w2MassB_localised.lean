import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.ae_nonneg_g0_sub
import Submission.Work.BoseFixB1.ae_wSmall1Pair_le_wSmallPair_g2
import Submission.Work.BoseFixB1.integrableOn_wSmallPair_cube
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.w1MassB_le_w2MassB_localised` — FS `lm:w2>w1`, localised form

The localised counterpart of `Submission.BoseGases.w2c_acube_integral_ge_w1c`
(`Submission/Work/FSKernelCompare.lean`): over the big box `acube ℓ`, the
small-box localised one-body kernel `w_{1,B(u)}` is dominated, box by box, by
the localised two-body kernel `w_{2,B(u)}` with the FS numerator
`g₂ = v(1−ω₀)(1+ω₀)` (`ω₀ := Classical.choose h`).

Both localised kernels share the (pointwise nonnegative) cutoffs
`chiSmallB M ℓ d u` and the (pointwise nonnegative) renormalisation
denominators `convScaleSmall M (ℓ·d)` and `convScale ℓ`, so the pointwise
comparison reduces to the numerator comparison `g₀ ≤ g₂`, which is FS's
`0 ≤ ω₀ ≤ 1` (eq:omegabounds) together with `v ≥ 0`: the excess is
`g₂ − g₀ = g₀·ω₀ ≥ 0`.  That a.e. pointwise step is
`Work.BoseFixB1.ae_wSmall1Pair_le_wSmallPair_g2`.

Since the Bochner integral of a non-integrable function is the junk value `0`,
the integral monotonicity `∫w₁ ≤ ∫w₂` needs the right-hand side to be
integrable, which is `Work.BoseFixB1.integrableOn_wSmallPair_cube` applied to
the numerator `g₂` (dominated by `χ_M((ℓd)⁻¹x−u)·C·|g₂(x−y)| ∈ L¹`).

The final step is `MeasureTheory.integral_mono_of_nonneg`, which needs only the
a.e. nonnegativity of the left integrand, the integrability of the right one,
and the a.e. pointwise comparison.
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology Real ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

-- (`ℝ³` is the global corpus notation `EuclideanSpace ℝ (Fin 3)`, declared in
-- `Submission.Work.BoseKinLoc.Defs`.)

theorem w1MassB_le_w2MassB_localised {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) :
    (∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2)
      ≤ ∫ p in Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h) p.1 p.2 := by
  -- ### The left integrand is nonnegative a.e.
  have hgnn : ∀ᵐ p : ℝ³ × ℝ³ ∂(volume : Measure (ℝ³ × ℝ³)), 0 ≤ g0 v h (p.1 - p.2) :=
    ae_nonneg_g0_sub (v := v) h hv hvrad hR0 hv_supp
  have hLnn_full : ∀ᵐ p : ℝ³ × ℝ³ ∂(volume : Measure (ℝ³ × ℝ³)),
      0 ≤ wSmall1Pair h M ℓ d u p.1 p.2 := by
    filter_upwards [hgnn] with p hp
    simp only [wSmall1Pair, wSmallPair, wSmallScaled]
    exact mul_nonneg (mul_nonneg (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u p.1)
      (div_nonneg (div_nonneg hp
          (Work.SmallBoxSliding.convScaleSmall_nonneg M (ℓ * d) (p.1 - p.2)))
        (Submission.BoseGases.convScale_nonneg ℓ (p.1 - p.2))))
      (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u p.2)
  have hLnn : 0 ≤ᵐ[volume.restrict (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)]
      (fun p : ℝ³ × ℝ³ => wSmall1Pair h M ℓ d u p.1 p.2) :=
    hLnn_full.filter_mono (MeasureTheory.ae_mono Measure.restrict_le_self)
  -- ### The a.e. pointwise comparison `w_{1,B(u)} ≤ w_{2,B(u)}`
  have hpt_full : ∀ᵐ p : ℝ³ × ℝ³ ∂(volume : Measure (ℝ³ × ℝ³)),
      wSmall1Pair h M ℓ d u p.1 p.2
        ≤ wSmallPair M ℓ d u (g2 v h) p.1 p.2 :=
    ae_wSmall1Pair_le_wSmallPair_g2 (v := v) (R0 := R0) hv_supp hR0 hv hvrad h u
  have hpt : (fun p : ℝ³ × ℝ³ => wSmall1Pair h M ℓ d u p.1 p.2)
      ≤ᵐ[volume.restrict (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)]
      (fun p : ℝ³ × ℝ³ => wSmallPair M ℓ d u (g2 v h) p.1 p.2) :=
    hpt_full.filter_mono (MeasureTheory.ae_mono Measure.restrict_le_self)
  -- ### Integrability of the right integrand
  have hf2 : MeasureTheory.Integrable (g2 v h) := g2_integrable hR0 hv hvrad hv_supp h
  have hf2supp : ∀ z : ℝ³, R0 ≤ ‖z‖ → g2 v h z = 0 :=
    fun z hz => g2_zero_of_norm_ge hv_supp hz h
  have hRint : MeasureTheory.Integrable
      (fun p : ℝ³ × ℝ³ => wSmallPair M ℓ d u (g2 v h) p.1 p.2)
      (volume.restrict (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ)) :=
    integrableOn_wSmallPair_cube (f := g2 v h) (R0 := R0) hf2 hf2supp hM hℓ hd hR hRχ u
  exact integral_mono_of_nonneg hLnn hRint hpt

end Work.BoseFixB1
