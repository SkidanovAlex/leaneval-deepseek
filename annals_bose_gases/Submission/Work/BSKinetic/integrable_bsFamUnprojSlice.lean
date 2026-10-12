import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.Defs
import Submission.Work.SmallBoxBridge.Resolve.kinKernel_aestronglyMeasurable
import Submission.Work.SmallBoxBridge.Resolve.kinKernel_bdd
import Submission.Work.SmallBoxBridge.Resolve.kinKernel_stronglyMeasurable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BSKinetic.integrable_bsFamUnprojSlice`

The slice (`u` fixed) integrability of the two-slot kernel pairing of the *unprojected* big-box
family:

    `z ↦ χ_u(z₁)ψ(z₁)·K_F(z₁−z₂)·χ_u(z₂)ψ(z₂)`

is integrable for the product of the Lebesgue measures on `ℝ³ × ℝ³`.  This is the key input which
lets the `u`-integral (`bsFamilyFormUnproj`) be exchanged with the two-slot integral (`x`-integral
then `y`-integral), i.e. Fubini for the family form.

The proof is by domination: writing `g = χ_u·ψ` (continuous, compactly supported, hence integrable)
and using that the kernel is bounded (`kinKernel_bdd`, by `C = (2π)⁻³∫_p ‖F ‖p‖‖`) and strongly
measurable (`kinKernel_stronglyMeasurable`), the two-slot integrand is dominated pointwise by
`C·‖g z₁‖·‖g z₂‖`, which is integrable by `Integrable.mul_prod` (Tonelli).
-/

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory

/-- `bsWin ℓ u = chiScale ℓ (· − ℓ•u)` is continuous for `ℓ ≠ 0`. -/
private lemma continuous_bsWin {ℓ : ℝ} (hℓ : ℓ ≠ 0) (u : ℝ³) : Continuous (bsWin ℓ u) :=
  (Submission.BoseGases.chiScale_contDiff hℓ).continuous.comp
    (continuous_id.sub continuous_const)

/-- `bsWin ℓ u` has compact support for `ℓ > 0`: it vanishes outside the closed ball of
radius `ℓ/2` about the box centre `ℓ • u` (`chiScale_support_le`). -/
private lemma hasCompactSupport_bsWin {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) :
    HasCompactSupport (bsWin ℓ u) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (ℓ • u) (ℓ / 2)) ?_
  intro x hx
  rw [Function.mem_support] at hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact Submission.BoseGases.chiScale_support_le hℓ (by simpa [bsWin] using hx)

/-- **Integrability of the two-slot kernel pairing** `g(z₁)·(K_F(z₁−z₂)·g(z₂))` on
`volume.prod volume`, for a bounded kernel `K_F` (`kinKernel_bdd`) and an integrable `g`:
dominate by `C·‖g z₁‖·‖g z₂‖` with `C = (2π)⁻³∫_p ‖F ‖p‖‖` and use `Integrable.mul_prod`
(Tonelli), the a.e. strong measurability coming from the strong measurability of `K_F`. -/
private lemma integrable_mul_kernel_pair {F : ℝ → ℝ} {g : ℝ³ → ℝ}
    (hF : MeasureTheory.Integrable (fun p : ℝ³ => F ‖p‖)) (hg : MeasureTheory.Integrable g) :
    MeasureTheory.Integrable
      (fun z : ℝ³ × ℝ³ => g z.1 * (Submission.BoseGases.kinKernel F (z.1 - z.2) * g z.2))
      (volume.prod volume) := by
  have hKbd : ∀ w : ℝ³,
      ‖Submission.BoseGases.kinKernel F w‖ ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖F ‖p‖‖ :=
    fun w => Work.SmallBoxBridge.Resolve.kinKernel_bdd F hF w
  have hmaj : MeasureTheory.Integrable
      (fun z : ℝ³ × ℝ³ =>
        (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖F ‖p‖‖) * (‖g z.1‖ * ‖g z.2‖))
      (volume.prod volume) :=
    (hg.norm.mul_prod hg.norm).const_mul _
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · exact (hg.aestronglyMeasurable.comp_fst).mul
      (((Work.SmallBoxBridge.Resolve.kinKernel_stronglyMeasurable hF).comp_measurable
        (measurable_fst.sub measurable_snd)).aestronglyMeasurable.mul
        (hg.aestronglyMeasurable.comp_snd))
  · filter_upwards with z
    calc ‖g z.1 * (Submission.BoseGases.kinKernel F (z.1 - z.2) * g z.2)‖
        = ‖g z.1‖ * ‖Submission.BoseGases.kinKernel F (z.1 - z.2) * g z.2‖ := norm_mul _ _
      _ ≤ ‖g z.1‖ * (‖Submission.BoseGases.kinKernel F (z.1 - z.2)‖ * ‖g z.2‖) :=
          mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ‖g z.1‖ * ((((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖F ‖p‖‖) * ‖g z.2‖) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hKbd _) (norm_nonneg _)) (norm_nonneg _)
      _ = (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖F ‖p‖‖) * (‖g z.1‖ * ‖g z.2‖) := by ring

theorem integrable_bsFamUnprojSlice {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) (u : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Work.BSKinetic.bsWin ℓ u z.1 * ψ z.1 *
          (Submission.BoseGases.kinKernel F (z.1 - z.2) *
            (Work.BSKinetic.bsWin ℓ u z.2 * ψ z.2)))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) := by
  refine integrable_mul_kernel_pair (F := F) (g := fun x : ℝ³ => bsWin ℓ u x * ψ x) hFi ?_
  exact ((continuous_bsWin (ne_of_gt hℓ) u).mul hψ.continuous).integrable_of_hasCompactSupport
    hcs.mul_left

end Work.BSKinetic
