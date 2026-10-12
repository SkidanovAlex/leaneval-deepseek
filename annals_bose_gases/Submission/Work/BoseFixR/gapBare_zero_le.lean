import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBox.q3kinDiagCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.gapBare_zero_le`

**The anchored bare mean-free box mass of a bounded state is at most `(2M)²ℓ³`.**

For `ℓ > 0`, `M ≥ 0` and a *continuous* one-body state `ψ` with `|ψ z| ≤ M` on the centred
cube `acube ℓ`, the anchored (`u = 0`) bare box mass

    `gapBare ℓ 0 ψ = ∫_{Λ(0)} (Q_0ψ)² = ∫_{acube ℓ} (ψ − m)²`,
    `m = |acube ℓ|⁻¹ ∫_{acube ℓ} ψ`,

satisfies `gapBare ℓ 0 ψ ≤ (2M)²ℓ³`.

## Proof

All the content is the trivial bound on the box mean: `|m| ≤ M` because `m` is the average of
values each of modulus at most `M` (`‖∫_{acube ℓ} ψ‖ ≤ M·|acube ℓ| = M·ℓ³`), so on the box

    `|ψ z − m| ≤ |ψ z| + |m| ≤ 2M`,   hence   `(ψ z − m)² ≤ (2M)²`,

and integrating the constant `(2M)²` over `acube ℓ` (`|acube ℓ| = ℓ³`) gives the claim.  Only
continuity of `ψ` is used, and only to get integrability over the compact cube.

## Contents

* `gapBare_zero_le` — the requested bound.
-/

open MeasureTheory
open scoped Topology ENNReal

namespace Work.BoseFixR

open Submission.BoseGases

theorem gapBare_zero_le {ℓ M : ℝ} (hℓ : 0 < ℓ) (hM : 0 ≤ M)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : Continuous ψ) (hb : ∀ z ∈ Submission.BoseGases.acube ℓ, |ψ z| ≤ M) :
    Work.BoseKinLoc.gapBare ℓ 0 ψ ≤ (2 * M) ^ 2 * ℓ ^ 3 := by
  have hl3 : 0 < ℓ ^ 3 := by positivity
  -- the volume of the centred cube, as a real
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (acube ℓ) = ℓ ^ 3 := by
    have h := Submission.BoseGases.real_volume_acube ℓ hℓ.le
    rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.restrict_apply_univ] at h
    rwa [MeasureTheory.Measure.real_def]
  have hcompt : IsCompact (acube ℓ) := acube_compact hℓ
  have hfin : (volume : Measure (EuclideanSpace ℝ (Fin 3))) (acube ℓ) < ∞ := hcompt.measure_lt_top
  -- the box integral of `ψ` is bounded by `M·ℓ³`
  have hInt : |∫ z in acube ℓ, ψ z| ≤ M * ℓ ^ 3 := by
    have h1 := MeasureTheory.norm_setIntegral_le_of_norm_le_const (f := ψ) (s := acube ℓ)
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3)))) hfin (fun z hz => by
        simpa [Real.norm_eq_abs] using hb z hz)
    rwa [Real.norm_eq_abs, hvol] at h1
  -- hence the box mean is bounded by `M`
  have hm : |Work.BSKinetic.bsMean ℓ 0 ψ| ≤ M := by
    rw [Work.BSKinetic.bsMean]
    simp only [smul_zero, zero_add]
    rw [abs_mul, abs_inv, abs_of_pos hl3]
    have h2 : (ℓ ^ 3)⁻¹ * |∫ z in acube ℓ, ψ z| ≤ (ℓ ^ 3)⁻¹ * (M * ℓ ^ 3) :=
      mul_le_mul_of_nonneg_left hInt (by positivity)
    rwa [mul_comm M (ℓ ^ 3), ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hl3), one_mul] at h2
  -- pointwise bound on the mean-free part
  have hpt : ∀ z ∈ acube ℓ, (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ) ^ 2 ≤ (2 * M) ^ 2 := by
    intro z hz
    have h1 : |ψ z - Work.BSKinetic.bsMean ℓ 0 ψ| ≤ 2 * M := by
      have h2 := abs_sub (ψ z) (Work.BSKinetic.bsMean ℓ 0 ψ)
      have h3 := hb z hz
      linarith [hm]
    rw [← sq_abs (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ), ← sq_abs (2 * M),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * M)]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hIntSq : IntegrableOn (fun z => (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ) ^ 2) (acube ℓ) :=
    ((hψ.sub continuous_const).pow 2).continuousOn.integrableOn_compact hcompt
  have hIntC : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 3) => (2 * M) ^ 2) (acube ℓ) :=
    MeasureTheory.integrableOn_const hfin.ne
  have hmono : (∫ z in acube ℓ, (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ) ^ 2)
      ≤ ∫ z in acube ℓ, (2 * M) ^ 2 :=
    setIntegral_mono_on hIntSq hIntC (acube_measurable ℓ) hpt
  -- `gapBare ℓ 0` is exactly that integral over the centred cube
  have hgapsimp : Work.BoseKinLoc.gapBare ℓ 0 ψ
      = ∫ z in acube ℓ, (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ) ^ 2 := by
    simp only [Work.BoseKinLoc.gapBare, Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ]
    rw [show Work.BoseKinLoc.lamBox ℓ 0 = acube ℓ from by
      ext x; simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]]
  rw [hgapsimp]
  calc (∫ z in acube ℓ, (ψ z - Work.BSKinetic.bsMean ℓ 0 ψ) ^ 2)
      ≤ ∫ z in acube ℓ, (2 * M) ^ 2 := hmono
    _ = (2 * M) ^ 2 * ℓ ^ 3 := by
        rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul, mul_comm]

end Work.BoseFixR
