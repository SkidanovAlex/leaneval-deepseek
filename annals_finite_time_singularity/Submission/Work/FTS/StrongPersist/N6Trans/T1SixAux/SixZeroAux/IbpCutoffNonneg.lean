/-
Auxiliary module for `Work.FTS.StrongPersist.N6Trans.T1SixAux.hardSlotSliceSixZero`.

The single-slot angular integration by parts of `Work.H2.T1Q.IbpCutoff` is stated there for a
*strictly positive* exponent `q`.  The exceptional slot of the level-six pairing
(`a = 0`, the pure `D_z`-slot) carries the exponent `q = 0`, where `sin(2θ)^{-q} = 1` is the
weight; the identity itself does not use `q > 0` at all, so this file re-proves it under the
weaker hypothesis `0 ≤ q`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.H2.T1Q.IbpCutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux

set_option linter.unusedVariables false

/-- **The cut-off angular integration by parts, for `0 ≤ q`.**

For `χ` of class `C^∞` vanishing off `[δ, π/2-δ]` (`0 < δ ≤ π/4`) and `hf`, `hv` of class `C¹`
on the open interval `(0, π/2)`,

`∫_θ sin(2θ)^{-q}·(χ hf)·(sin(2θ)·hv')·hv
    = -∫_θ sin(2θ)^{-q}·(χ·((1/2) sin(2θ) hf' + (1-q) cos(2θ) hf) + (1/2) sin(2θ) χ' hf)·hv²`

with both sides integrable.  This is `Work.H2.T1Q.IbpCutoff` with the hypothesis `0 < q`
weakened to `0 ≤ q` (its proof never uses it). -/
theorem ibpCutoff_nonneg {q : ℝ} (hq : 0 ≤ q) {χ hf hv : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ π / 4)
    (hχ0 : ∀ θ : ℝ, θ ≤ δ → χ θ = 0)
    (hχ2 : ∀ θ : ℝ, π / 2 - δ ≤ θ → χ θ = 0)
    (hf' : ContDiffOn ℝ 1 hf (Set.Ioo 0 (π / 2)))
    (hv' : ContDiffOn ℝ 1 hv (Set.Ioo 0 (π / 2))) :
    MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (-q) * (χ θ * hf θ)
          * (Real.sin (2 * θ) * deriv hv θ) * hv θ) Work.Spaces.Iθ
      ∧ ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q) * (χ θ * hf θ)
            * (Real.sin (2 * θ) * deriv hv θ) * hv θ
        = -∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-q)
            * (χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv hf θ)
                + (1 - q) * Real.cos (2 * θ) * hf θ)
              + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * hf θ)
            * (hv θ) ^ 2 := by
  have hpi : (0 : ℝ) < π / 2 := by positivity
  obtain ⟨hIntG, hIntK⟩ := Work.H2.T1Q.ibpCutoff_integrable (q := q) hχ hδ hδ4 hχ0 hχ2 hf' hv'
  have hIcc : ∀ u : ℝ → ℝ, ∫ θ in Work.Spaces.Iθ, u θ = ∫ θ in (0 : ℝ)..(π / 2), u θ := by
    intro u
    rw [show Work.Spaces.Iθ = Set.Icc 0 (π / 2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi.le]
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      HasDerivAt (Work.H2.T1Q.IbpPrim q χ hf hv)
        (Work.H2.T1Q.IbpG q χ hf hv θ + Work.H2.T1Q.IbpK q χ hf hv θ) θ := by
    intro θ hθ
    exact Work.H2.T1Q.ibpCutoff_deriv hθ (hχ.contDiffAt.differentiableAt (by simp))
      ((hf'.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ))
      ((hv'.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ))
  have hint : IntervalIntegrable
      (fun θ => Work.H2.T1Q.IbpG q χ hf hv θ + Work.H2.T1Q.IbpK q χ hf hv θ)
      volume 0 (π / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hpi.le]
    exact hIntG.add hIntK
  have hFTC : ∫ θ in (0 : ℝ)..(π / 2),
      (Work.H2.T1Q.IbpG q χ hf hv θ + Work.H2.T1Q.IbpK q χ hf hv θ) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hpi hderiv hint
      (Work.H2.T1Q.ibpCutoff_prim_tendsto_zero_right hδ hχ0)
      (Work.H2.T1Q.ibpCutoff_prim_tendsto_zero_left hδ hχ2)
    simpa using h
  have hsplit : ∫ θ in Work.Spaces.Iθ,
      (Work.H2.T1Q.IbpG q χ hf hv θ + Work.H2.T1Q.IbpK q χ hf hv θ)
      = (∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpG q χ hf hv θ)
        + ∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpK q χ hf hv θ :=
    MeasureTheory.integral_add hIntG hIntK
  have hsum : (∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpG q χ hf hv θ)
      + ∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpK q χ hf hv θ = 0 := by
    rw [← hsplit, hIcc, hFTC]
  change MeasureTheory.IntegrableOn (Work.H2.T1Q.IbpG q χ hf hv) Work.Spaces.Iθ
      ∧ ∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpG q χ hf hv θ
        = -∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpK q χ hf hv θ
  exact ⟨hIntG, by linarith⟩

end Work.FTS.StrongPersist.N6Trans.T1SixAux
