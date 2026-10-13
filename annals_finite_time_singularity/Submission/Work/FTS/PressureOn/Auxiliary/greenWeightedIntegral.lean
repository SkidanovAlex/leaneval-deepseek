/-
# The weighted Green identity

`∫ χ u ΔF = -∫ u F Δχ - 2 ∫ u ⟪∇χ, ∇F⟫` for `u` harmonic and `χ` compactly supported,
obtained from three integrations by parts.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Green.integral_mul_laplaceTrace_comm
import Submission.Work.FTS.PressureOn.Green.div_gradient_eq_laplaceTrace
import Submission.Work.FTS.PressureOn.PoissonAux.Ibp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity MeasureTheory Set Filter Topology
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn.Auxiliary

noncomputable section

/-- **The weighted Green identity.**  For `u` harmonic on `ℝ³`, a compactly supported weight `χ` and
a `C²` function `F`,

  `∫ χ u ΔF = -∫ u F Δχ - 2 ∫ u ⟪∇χ, ∇F⟫`.

Proof: three integrations by parts (`integral_inner_gradient_mul_eq_neg`) on the compactly
supported fields `χ ∇F`, `χ ∇u` and `F ∇χ`; the harmonicity of `u` kills the `Δu` term, and the
mixed terms combine to the stated expression. -/
lemma integral_green_weighted (u χ F : R3 → ℝ)
    (hu1 : ContDiff ℝ 1 u) (hu2 : ContDiff ℝ 2 u)
    (hχ1 : ContDiff ℝ 1 χ) (hχ2 : ContDiff ℝ 2 χ) (hχcs : HasCompactSupport χ)
    (hF1 : ContDiff ℝ 1 F) (hF2 : ContDiff ℝ 2 F) (hlapu : ∀ y, laplaceTrace u y = 0)
    (hint1 : Integrable (fun y => (χ y * laplaceTrace F y) * u y))
    (hint2 : Integrable (fun y => inner ℝ (gradient χ y) (gradient F y) * u y))
    (hint3 : Integrable (fun y => (F y * laplaceTrace χ y) * u y)) :
    ∫ y, χ y * u y * laplaceTrace F y
      = -(∫ y, u y * F y * laplaceTrace χ y)
        - 2 * ∫ y, u y * inner ℝ (gradient χ y) (gradient F y) := by
  have hgχ : ContDiff ℝ 1 (fun y : R3 => gradient χ y) := Green.contDiff_gradient χ hχ2
  have hgu : ContDiff ℝ 1 (fun y : R3 => gradient u y) := Green.contDiff_gradient u hu2
  have hgF : ContDiff ℝ 1 (fun y : R3 => gradient F y) := Green.contDiff_gradient F hF2
  have hdivF : ∀ y : R3, div (fun z : R3 => gradient F z) y = laplaceTrace F y :=
    fun y => congrFun (Green.div_gradient_eq_laplaceTrace F hF2) y
  have hdivχ : ∀ y : R3, div (fun z : R3 => gradient χ z) y = laplaceTrace χ y :=
    fun y => congrFun (Green.div_gradient_eq_laplaceTrace χ hχ2) y
  have hdivu : ∀ y : R3, div (fun z : R3 => gradient u z) y = laplaceTrace u y :=
    fun y => congrFun (Green.div_gradient_eq_laplaceTrace u hu2) y
  -- (A)  ω = χ ∇F, ψ = u
  have hAcs : HasCompactSupport (fun y : R3 => χ y • gradient F y) := hχcs.mono' (fun y hy => by
    by_contra hyt
    rw [Function.mem_support] at hy
    exact hy (by rw [image_eq_zero_of_notMem_tsupport hyt, zero_smul]))
  have hAibp := Work.FTS.PressureOn.integral_inner_gradient_mul_eq_neg
    (fun y : R3 => χ y • gradient F y) (hχ1.smul hgF) hAcs hu1
  have hAlhs : ∫ y, inner ℝ (χ y • gradient F y) (gradient u y)
      = ∫ y, χ y * inner ℝ (gradient F y) (gradient u y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [real_inner_smul_left]
  have hArhs : ∫ y, div (fun z : R3 => χ z • gradient F z) y * u y
      = ∫ y, ((χ y * laplaceTrace F y) * u y
          + inner ℝ (gradient χ y) (gradient F y) * u y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show div (fun z : R3 => χ z • gradient F z) y * u y = _
    rw [Work.FTS.PressureOn.div_smul (ψ := χ) (ω := fun y : R3 => gradient F y) hχ1 hgF y,
      hdivF y]
    ring
  have hAsplit : ∫ y, ((χ y * laplaceTrace F y) * u y
        + inner ℝ (gradient χ y) (gradient F y) * u y)
      = (∫ y, (χ y * laplaceTrace F y) * u y)
        + (∫ y, inner ℝ (gradient χ y) (gradient F y) * u y) :=
    integral_add hint1 hint2
  have hAeq : ∫ y, χ y * inner ℝ (gradient F y) (gradient u y)
      = -((∫ y, (χ y * laplaceTrace F y) * u y)
          + (∫ y, inner ℝ (gradient χ y) (gradient F y) * u y)) := by
    have h := hAibp
    rw [hAlhs, hArhs, hAsplit] at h
    exact h
  -- (B)  ω = χ ∇u, ψ = F
  have hBcs : HasCompactSupport (fun y : R3 => χ y • gradient u y) := hχcs.mono' (fun y hy => by
    by_contra hyt
    rw [Function.mem_support] at hy
    exact hy (by rw [image_eq_zero_of_notMem_tsupport hyt, zero_smul]))
  have hBibp := Work.FTS.PressureOn.integral_inner_gradient_mul_eq_neg
    (fun y : R3 => χ y • gradient u y) (hχ1.smul hgu) hBcs hF1
  have hBlhs : ∫ y, inner ℝ (χ y • gradient u y) (gradient F y)
      = ∫ y, χ y * inner ℝ (gradient u y) (gradient F y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [real_inner_smul_left]
  have hBrhs : ∫ y, div (fun z : R3 => χ z • gradient u z) y * F y
      = ∫ y, inner ℝ (gradient χ y) (gradient u y) * F y := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show div (fun z : R3 => χ z • gradient u z) y * F y
      = inner ℝ (gradient χ y) (gradient u y) * F y
    rw [Work.FTS.PressureOn.div_smul (ψ := χ) (ω := fun y : R3 => gradient u y) hχ1 hgu y,
      hdivu y, hlapu y]
    ring
  have hBeq : ∫ y, χ y * inner ℝ (gradient u y) (gradient F y)
      = -(∫ y, inner ℝ (gradient χ y) (gradient u y) * F y) := by
    have h := hBibp
    rw [hBlhs, hBrhs] at h
    exact h
  -- (D)  ω = F ∇χ, ψ = u
  have hDcs : HasCompactSupport (fun y : R3 => F y • gradient χ y) := hχcs.mono' (fun y hy => by
    by_contra hyt
    rw [Function.mem_support] at hy
    exact hy (by rw [Green.gradient_eq_zero_of_notMem_tsupport hyt, smul_zero]))
  have hDibp := Work.FTS.PressureOn.integral_inner_gradient_mul_eq_neg
    (fun y : R3 => F y • gradient χ y) (hF1.smul hgχ) hDcs hu1
  have hDlhs : ∫ y, inner ℝ (F y • gradient χ y) (gradient u y)
      = ∫ y, inner ℝ (gradient χ y) (gradient u y) * F y := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [real_inner_smul_left]
    ring
  have hDrhs : ∫ y, div (fun z : R3 => F z • gradient χ z) y * u y
      = ∫ y, ((F y * laplaceTrace χ y) * u y
          + inner ℝ (gradient χ y) (gradient F y) * u y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show div (fun z : R3 => F z • gradient χ z) y * u y = _
    rw [Work.FTS.PressureOn.div_smul (ψ := F) (ω := fun y : R3 => gradient χ y) hF1 hgχ y,
      hdivχ y, real_inner_comm]
    ring
  have hDsplit : ∫ y, ((F y * laplaceTrace χ y) * u y
        + inner ℝ (gradient χ y) (gradient F y) * u y)
      = (∫ y, (F y * laplaceTrace χ y) * u y)
        + (∫ y, inner ℝ (gradient χ y) (gradient F y) * u y) :=
    integral_add hint3 hint2
  have hDeq : ∫ y, inner ℝ (gradient χ y) (gradient u y) * F y
      = -((∫ y, (F y * laplaceTrace χ y) * u y)
          + (∫ y, inner ℝ (gradient χ y) (gradient F y) * u y)) := by
    have h := hDibp
    rw [hDlhs, hDrhs, hDsplit] at h
    exact h
  -- the left-hand sides of (A) and (B) agree
  have hcomm : ∫ y, χ y * inner ℝ (gradient F y) (gradient u y)
      = ∫ y, χ y * inner ℝ (gradient u y) (gradient F y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [real_inner_comm]
  set X : ℝ := ∫ y, χ y * inner ℝ (gradient F y) (gradient u y) with hX
  set Z : ℝ := ∫ y, inner ℝ (gradient χ y) (gradient u y) * F y with hZ
  set A1 : ℝ := ∫ y, (χ y * laplaceTrace F y) * u y with hA1
  set A2 : ℝ := ∫ y, inner ℝ (gradient χ y) (gradient F y) * u y with hA2
  set W1 : ℝ := ∫ y, (F y * laplaceTrace χ y) * u y with hW1
  have hA' : X = -(A1 + A2) := hAeq
  have hB' : X = -Z := by
    rw [hcomm]
    exact hBeq
  have hD' : Z = -(W1 + A2) := hDeq
  have key : A1 = -W1 - 2 * A2 := by linarith
  have e1 : A1 = ∫ y, χ y * u y * laplaceTrace F y := by
    rw [hA1]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    ring
  have e2 : W1 = ∫ y, u y * F y * laplaceTrace χ y := by
    rw [hW1]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    ring
  have e3 : A2 = ∫ y, u y * inner ℝ (gradient χ y) (gradient F y) := by
    rw [hA2]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    ring
  rw [← e1, ← e2, ← e3]
  linarith

end

end Work.FTS.PressureOn.Auxiliary
