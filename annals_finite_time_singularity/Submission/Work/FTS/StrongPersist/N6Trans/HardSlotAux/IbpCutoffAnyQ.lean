import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.IbpCutoffDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `IbpCutoffAnyQ` — the cutoff angular integration by parts for an arbitrary real exponent

`Work.H2.T1Q.IbpCutoff` proves the angular integration by parts

  `∫_θ sin(2θ)^{-q}·(χ hf)·(sin(2θ)·hv')·hv
      = -∫_θ sin(2θ)^{-q}·(χ·((1/2) sin(2θ) hf' + (1-q) cos(2θ) hf)
                              + (1/2) sin(2θ) χ' hf)·hv²`

for `χ` smooth and vanishing off `[δ, π/2-δ]` (`0 < δ ≤ π/4`), `hf`, `hv` of class `C¹` on the
open interval `(0, π/2)`, **under the extra hypothesis `0 < q`**.  That hypothesis is never used
in the proof — the `rpow` factor `sin(2θ)^{-q}` is only ever handled on the compact support of
`χ`, where `sin(2θ) > 0` regardless of the sign of `q` (the auxiliary lemmas
`ibpCutoff_integrable`, `ibpCutoff_deriv` and the two `tendsto`-to-zero lemmas of
`Submission/Work/H2/T1Q/IbpCutoff.lean` are all stated for an arbitrary real `q`).

This file therefore records the same identity for an **arbitrary real `q`**, with the two
integrands named through `IbpG`/`IbpK`; it is the form needed by the `N6` hard-slot analysis,
where the slots carry the exponents `η = 99/100` and `γ = 1 + α/10 > 1` (so in particular
`q > 1` for the `γ`-slots, well outside the reach of the `IbpCutoff` statement as published).

The proof is a verbatim replay of the body of `Work.H2.T1Q.IbpCutoff` with the unused hypothesis
deleted.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.HardSlotAux

theorem IbpCutoffAnyQ {q : ℝ} {χ hf hv : ℝ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ π / 4)
    (hχ0 : ∀ θ : ℝ, θ ≤ δ → χ θ = 0)
    (hχ2 : ∀ θ : ℝ, π / 2 - δ ≤ θ → χ θ = 0)
    (hf' : ContDiffOn ℝ 1 hf (Set.Ioo 0 (π / 2)))
    (hv' : ContDiffOn ℝ 1 hv (Set.Ioo 0 (π / 2))) :
    MeasureTheory.IntegrableOn (Work.H2.T1Q.IbpG q χ hf hv) Work.Spaces.Iθ
      ∧ ∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpG q χ hf hv θ
        = -∫ θ in Work.Spaces.Iθ, Work.H2.T1Q.IbpK q χ hf hv θ := by
  have hpi : (0 : ℝ) < π / 2 := by positivity
  obtain ⟨hIntG, hIntK⟩ :=
    Work.H2.T1Q.ibpCutoff_integrable (q := q) hχ hδ hδ4 hχ0 hχ2 hf' hv'
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
  exact ⟨hIntG, by linarith⟩

end Work.FTS.StrongPersist.N6Trans.HardSlotAux
