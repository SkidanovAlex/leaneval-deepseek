import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FM.Core
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsZero.Bridge

set_option linter.unusedVariables false

/-- **Angular-slice integrability of `𝓛_Γ`, positive half-line.**

For a datum `f` which is `C^∞` on the open quadrant and lies in `ℋ⁴`, and for which the
angular slice `θ ↦ K(θ)·∂_z f (s,θ)` is integrable for every `s > 0`, the same holds for
`θ ↦ K(θ)·(𝓛_Γ f)(s,θ)/s`.

The two `θ`-dependent pieces of `𝓛_Γ f/s` are
* `θ ↦ K θ · f s θ / s` — integrable by `sliceK_integrableOn_of_continuousOn` (`K` is bounded
  by `3`, the slice `f s ·` is square-integrable by `HkMem α 4 f` and `Iθ` has finite measure),
  together with `θ ↦ K θ · ∂_z f s θ` (the hypothesis `hpz`, scaled by `s`), and
* the contribution of `L₁₂(f)(s)`, which is *constant* in `θ`: the `θ`-dependence is
  `K θ · Γ(θ)/(c(1+s)²)`, which is continuous (hence integrable on the compact `Iθ`), and the
  constant factor `L₁₂(f)(s)` is pulled out.

The pointwise identity
`K θ · 𝓛_Γ f s θ = (1 - 2/(1+s))·(K θ f s θ) + s·(K θ ∂_z f s θ)
   - (K θ · 2sΓ(θ)/(c(1+s)²))·L₁₂(f)(s)`
is a pure ring identity (all the divisions are kept as atoms), so no positivity of `c` is
needed. -/
theorem LGammaSlice {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hpz : ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.Spaces.pz f s θ) Work.Spaces.Iθ) :
    ∀ s : ℝ, 0 < s → MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.Coercivity.LGamma α f s θ / s) Work.Spaces.Iθ := by
  intro s hs
  -- `f` is continuous on the open quadrant, so the `f`-slice is integrable
  have hC : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0 := hsm.continuousOn
  have h1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ :=
    Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn hC hmem s hs
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- `K·f` (the division by `s` is undone with `s ≠ 0`)
  have hKf : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * f s θ) Work.Spaces.Iθ := by
    have h : MeasureTheory.IntegrableOn
        (fun θ : ℝ => s * (Work.Spaces.K θ * f s θ / s)) Work.Spaces.Iθ := h1.const_mul s
    exact h.congr_fun (fun θ _ => by field_simp) hIθ
  -- `K·Γ` is integrable on `Iθ` (continuous on the compact interval)
  have hKΓ : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.Spaces.Gam α θ) Work.Spaces.Iθ := by
    exact (Work.Spaces.CAux.integrableOn_GamK α hα).congr_fun (fun θ _ => by ring) hIθ
  -- the `L₁₂`-term: a continuous `θ`-dependent factor times the constant `L₁₂(f)(s)`
  have h3 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.K θ * (2 * s * Work.Spaces.Gam α θ
          / (Work.Spaces.c α * (1 + s) ^ 2))) * Work.Coercivity.L12f f s) Work.Spaces.Iθ := by
    have h : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (2 * s / (Work.Spaces.c α * (1 + s) ^ 2)
            * (Work.Spaces.K θ * Work.Spaces.Gam α θ)) * Work.Coercivity.L12f f s)
        Work.Spaces.Iθ := (hKΓ.const_mul (2 * s / (Work.Spaces.c α * (1 + s) ^ 2))).mul_const _
    exact h.congr_fun (fun θ _ => by ring) hIθ
  -- assemble: `K θ · 𝓛_Γ f s θ = (1 - 2/(1+s))·(K θ f) + s·(K θ ∂_z f) - (K θ B)·L₁₂(f)(s)`
  have hmain : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.Coercivity.LGamma α f s θ) Work.Spaces.Iθ := by
    have h : MeasureTheory.IntegrableOn
        (fun θ : ℝ => (1 - 2/(1+s)) * (Work.Spaces.K θ * f s θ)
          + s * (Work.Spaces.K θ * Work.Spaces.pz f s θ)
          - (Work.Spaces.K θ * (2 * s * Work.Spaces.Gam α θ
              / (Work.Spaces.c α * (1 + s) ^ 2))) * Work.Coercivity.L12f f s)
        Work.Spaces.Iθ :=
      ((hKf.const_mul (1 - 2/(1+s))).add ((hpz s hs).const_mul s)).sub h3
    exact h.congr_fun (fun θ _ => by
      simp only [Work.Coercivity.LGamma, Work.Coercivity.L, Work.Spaces.Dz]
      ring) hIθ
  -- finally divide by `s`, which is a constant factor
  have h : MeasureTheory.IntegrableOn
      (fun θ : ℝ => s⁻¹ * (Work.Spaces.K θ * Work.Coercivity.LGamma α f s θ)) Work.Spaces.Iθ :=
    hmain.const_mul s⁻¹
  exact h.congr_fun (fun θ _ => by ring) hIθ

end Work.FTS.StrongEps.EpsZero.Bridge
