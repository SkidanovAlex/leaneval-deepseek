import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_StreamBdry.SB6.sb6_rates

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `sb6_rates_proved` — the frozen SB6 producer `StreamBdryIface.sb6_rates`

The slim rates of the reflected `U`-slot part: with `λ = 4/αG` (`αG·λ = 4 ≥ 2`),
`Φ w θ = (0 < w) · oddPerS (psiP αG Ψ) w θ` satisfies

* `|Φ w θ| ≤ C₀ (π/2 - θ) (1+w)^{-λ}`,
* `|∂_w Φ| ≤ C₀ (π/2 - θ) (1+w)^{-λ-1}`,
* `|∂_θ Φ| ≤ C₀ (1+w)^{-λ}`

on `0 ≤ w`, `0 ≤ θ < π/2`.  The compact part comes from SB3/SB4 (`hnear0`) and the far part from
`SB5.sb5_decay` (`∂_θpsiP = V + tan θ·psiP`, `V` with zero `cos`-mean); the `w = 0` values are
junk-safe because `Φ = 0` for `w ≤ 0`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_StreamBdry

open Work.FTS.StreamBdryIface (SlotBd SrcOK psiP oddPerS)
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **SB6 proved** (frozen type `sb6_rates`). -/
theorem sb6_rates_proved {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : Fn}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) (hF : SrcOK F L Mf)
    (hnear0 : ∃ K : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd → z ≤ 1 →
      |Work.Spaces.DzIter 1 (psiP αG Ψ) z θ| ≤ K * z * Work.Construction.s2 θ) :
    let Φ : Fn := fun w θ => if 0 < w then oddPerS (psiP αG Ψ) w θ else 0
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < π / 2 →
      |Φ w θ| ≤ C₀ * (π / 2 - θ) * (1 + w) ^ (-(4 / αG)) ∧
      |deriv (fun w' => Φ w' θ) w| ≤ C₀ * (π / 2 - θ) * (1 + w) ^ (-(4 / αG) - 1) ∧
      |deriv (fun θ' => Φ w θ') θ| ≤ C₀ * (1 + w) ^ (-(4 / αG)) :=
  SB6.sb6_rates hαG hsol h3 hslot hF hnear0

end Work.FTS_StreamBdry
