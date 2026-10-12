import Mathlib
import Submission.Work.BSKinetic.FamKernelAux
import Submission.Work.SmallBoxBridge.Resolve.kinKernel_aestronglyMeasurable
import Submission.Work.SmallBoxBridge.Resolve.kinKernel_bdd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.BSKinetic.integrable_bsFamUnprojJoint`

**The joint (`u`-integrated) unprojected family integrand is `L¹`.**

For `ℓ > 0`, a radial symbol `F` with `p ↦ F‖p‖` integrable and a smooth compactly supported
one-body state `ψ`, the function

    `w = (u, x, y) ↦ χ_u(x)·ψ(x)·K_F(x − y)·χ_u(y)·ψ(y)`

is `Integrable` for the product of the Lebesgue measure on `ℝ³` with itself (three times), where

* `χ_u = bsWin ℓ u = χ_ℓ(· − ℓu)` is the moving-box window, and
* `K_F = Submission.BoseGases.kinKernel F` is the kernel of the symbol `F‖·‖`.

This is the joint companion of `Work.BSKinetic.integrable_bsFamUnprojSlice`.

## Proof

The integrand is a product of three classes of factors:

* `χ_u(x)`, `χ_u(y)`, `ψ(x)`, `ψ(y)` are *continuous* in `w`;
* `K_F(x − y)` is only a.e. strongly measurable (`kinKernel_aestronglyMeasurable`), but the
  difference map `(x,y) ↦ x − y` is quasi-measure-preserving
  (`quasiMeasurePreserving_sub_of_right_invariant`) since the Lebesgue measure is
  right-translation invariant, so `AEStronglyMeasurable.comp_quasiMeasurePreserving` turns the
  a.e. measurability of `K_F` into that of `K_F(x − y)`.

The function is then bounded (`|χ| ≤ chiSup`, `ψ` bounded on its compact support,
`|K_F| ≤ K_F(0)`-type bound `kinKernel_bdd`) and supported in the compact product of balls

    `closedBall 0 ((R + ℓ/2)/ℓ) × (closedBall 0 R × closedBall 0 R)`,

where `R` bounds the support of `ψ`: `ψ x ≠ 0` forces `‖x‖ ≤ R`, and `χ_u(x) ≠ 0` forces
`‖x − ℓu‖ ≤ ℓ/2`, whence `ℓ‖u‖ ≤ ‖x‖ + ℓ/2 ≤ R + ℓ/2`.  A bounded a.e. strongly measurable
function supported in a compact set is integrable (`integrable_of_compact_support`).
-/

noncomputable section

open MeasureTheory
open Submission.BoseGases
open Work.SmallBoxBridge.Resolve

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

theorem integrable_bsFamUnprojJoint {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) :
    MeasureTheory.Integrable
      (fun w : EuclideanSpace ℝ (Fin 3) ×
          (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
        Work.BSKinetic.bsWin ℓ w.1 w.2.1 * ψ w.2.1 *
          (Submission.BoseGases.kinKernel F (w.2.1 - w.2.2) *
            (Work.BSKinetic.bsWin ℓ w.1 w.2.2 * ψ w.2.2)))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))) := by
  classical
  obtain ⟨R, hψsupp⟩ := HasCompactSupport.exists_norm_le hcs
  obtain ⟨Cψ, hCψ⟩ := hcs.exists_bound_of_continuous hψ.continuous
  set M : ℝ := max Cψ 0 with hMdef
  have hMnn : 0 ≤ M := by rw [hMdef]; exact le_max_right _ _
  have hψM : ∀ x : ℝ³, ‖ψ x‖ ≤ M := by
    intro x; rw [hMdef]; exact le_trans (hCψ x) (le_max_left _ _)
  have hCnn : 0 ≤ chiSup := le_of_lt chiSup_pos
  set Kval : ℝ := ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖F ‖p‖‖ with hKvaldef
  have hKbd : ∀ z : ℝ³, ‖kinKernel F z‖ ≤ Kval := by
    intro z; rw [hKvaldef]; exact kinKernel_bdd F hFi z
  have hKnn : 0 ≤ Kval := le_trans (norm_nonneg (kinKernel F 0)) (hKbd 0)
  set Kc : Set (ℝ³ × (ℝ³ × ℝ³)) :=
      Metric.closedBall (0:ℝ³) ((R + ℓ/2)/ℓ) ×ˢ
        (Metric.closedBall (0:ℝ³) R ×ˢ Metric.closedBall (0:ℝ³) R) with hKcdef
  have hKcompact : IsCompact Kc := by
    rw [hKcdef]
    exact (isCompact_closedBall _ _).prod
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hsupp : ∀ w : ℝ³ × (ℝ³ × ℝ³),
      bsWin ℓ w.1 w.2.1 * ψ w.2.1 *
        (kinKernel F (w.2.1 - w.2.2) * (bsWin ℓ w.1 w.2.2 * ψ w.2.2)) ≠ 0 → w ∈ Kc := by
    intro w hw
    rw [hKcdef]
    obtain ⟨hA, hB⟩ := mul_ne_zero_iff.mp hw
    obtain ⟨hbsx, hψx⟩ := mul_ne_zero_iff.mp hA
    obtain ⟨_hK, hBy⟩ := mul_ne_zero_iff.mp hB
    obtain ⟨hbsy, hψy⟩ := mul_ne_zero_iff.mp hBy
    have hxR : ‖w.2.1‖ ≤ R := hψsupp w.2.1 hψx
    have hyR : ‖w.2.2‖ ≤ R := hψsupp w.2.2 hψy
    have hnsub : ‖w.2.1 - ℓ • w.1‖ ≤ ℓ / 2 := bsWin_ne_zero_le_norm hℓ hbsx
    have huU : ‖w.1‖ ≤ (R + ℓ/2)/ℓ := by
      have h1 : ‖ℓ • w.1‖ ≤ ‖w.2.1‖ + ℓ/2 := by
        have h2 : ‖ℓ • w.1‖ ≤ ‖w.2.1‖ + ‖w.2.1 - ℓ • w.1‖ := by
          simpa using (norm_sub_le w.2.1 (w.2.1 - ℓ • w.1))
        linarith
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ] at h1
      rw [le_div_iff₀ hℓ, mul_comm]
      linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]; exact huU
    · rw [Metric.mem_closedBall, dist_zero_right]; exact hxR
    · rw [Metric.mem_closedBall, dist_zero_right]; exact hyR
  have hbound : ∀ w : ℝ³ × (ℝ³ × ℝ³),
      ‖bsWin ℓ w.1 w.2.1 * ψ w.2.1 *
        (kinKernel F (w.2.1 - w.2.2) * (bsWin ℓ w.1 w.2.2 * ψ w.2.2))‖
      ≤ chiSup * M * (Kval * (chiSup * M)) := by
    intro w
    have hbsx : |bsWin ℓ w.1 w.2.1| ≤ chiSup := abs_bsWin_le ℓ w.1 w.2.1
    have hbsy : |bsWin ℓ w.1 w.2.2| ≤ chiSup := abs_bsWin_le ℓ w.1 w.2.2
    have hψx : |ψ w.2.1| ≤ M := by simpa [Real.norm_eq_abs] using hψM w.2.1
    have hψy : |ψ w.2.2| ≤ M := by simpa [Real.norm_eq_abs] using hψM w.2.2
    have hKz : |kinKernel F (w.2.1 - w.2.2)| ≤ Kval := by
      simpa [Real.norm_eq_abs] using hKbd (w.2.1 - w.2.2)
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (mul_le_mul hbsx hψx (abs_nonneg _) hCnn)
      (mul_le_mul hKz (mul_le_mul hbsy hψy (abs_nonneg _) hCnn)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hKnn)
      (mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
      (mul_nonneg hCnn hMnn)
  have hχc : Continuous (chiScale ℓ) := (chiScale_contDiff (ne_of_gt hℓ)).continuous
  have hc1 : Continuous (fun w : ℝ³ × (ℝ³ × ℝ³) => bsWin ℓ w.1 w.2.1) := by
    show Continuous (fun w : ℝ³ × (ℝ³ × ℝ³) => chiScale ℓ (w.2.1 - ℓ • w.1))
    exact hχc.comp (continuous_snd.fst.sub (continuous_fst.const_smul ℓ))
  have hc2 : Continuous (fun w : ℝ³ × (ℝ³ × ℝ³) => ψ w.2.1) :=
    hψ.continuous.comp continuous_snd.fst
  have hc3 : Continuous (fun w : ℝ³ × (ℝ³ × ℝ³) => bsWin ℓ w.1 w.2.2) := by
    show Continuous (fun w : ℝ³ × (ℝ³ × ℝ³) => chiScale ℓ (w.2.2 - ℓ • w.1))
    exact hχc.comp (continuous_snd.snd.sub (continuous_fst.const_smul ℓ))
  have hc4 : Continuous (fun w : ℝ³ × (ℝ³ × ℝ³) => ψ w.2.2) :=
    hψ.continuous.comp continuous_snd.snd
  have hKmeas : AEStronglyMeasurable (fun w : ℝ³ × (ℝ³ × ℝ³) => kinKernel F (w.2.1 - w.2.2))
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod (volume : Measure ℝ³))) := by
    have hsub : Measure.QuasiMeasurePreserving (fun q : ℝ³ × ℝ³ => q.1 - q.2)
        ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) (volume : Measure ℝ³) :=
      quasiMeasurePreserving_sub_of_right_invariant volume volume
    have h1 : AEStronglyMeasurable (fun q : ℝ³ × ℝ³ => kinKernel F (q.1 - q.2))
        ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
      (kinKernel_aestronglyMeasurable F hFi).comp_quasiMeasurePreserving hsub
    have h2 := h1.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ³))
        (ν := (volume : Measure ℝ³).prod (volume : Measure ℝ³)))
    simpa only [Function.comp_def] using h2
  have haes : AEStronglyMeasurable (fun w : ℝ³ × (ℝ³ × ℝ³) =>
      bsWin ℓ w.1 w.2.1 * ψ w.2.1 *
        (kinKernel F (w.2.1 - w.2.2) * (bsWin ℓ w.1 w.2.2 * ψ w.2.2)))
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod (volume : Measure ℝ³))) :=
    ((hc1.aestronglyMeasurable.mul hc2.aestronglyMeasurable).mul
      (hKmeas.mul (hc3.aestronglyMeasurable.mul hc4.aestronglyMeasurable)))
  exact integrable_of_compact_support ⟨Kc, hKcompact, hsupp⟩ haes
    ⟨chiSup * M * (Kval * (chiSup * M)), hbound⟩

end Work.BSKinetic
