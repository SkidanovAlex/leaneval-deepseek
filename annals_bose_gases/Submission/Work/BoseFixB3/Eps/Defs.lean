import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB3.Steps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB3/Eps/Defs` — the one-body residual profile of `B3EpsRoot`

This module fixes the vocabulary of the `b3EpsRoot_holds` proof (FS's
`ε₂`-Cauchy–Schwarz, `lem:Q3-splitting1`, l. 1531–1545 of
`Papers/fournais_solovej/final_v2.tex`).

The word `q3convWord` of `Work.BoseFixB3.Defs` is

  `q3convWord fc κ ℓ I Φ = I ℓ⁻³ Σ_{i,j} ∫_{abox n ℓ} P_iΦ · (1−f_L)_j(χ_Λ² P_jΦ)`,

and since `P_jΦ` is *constant in the slot `j`*, the slot-`j` fibre of
`χ_Λ²·P_jΦ` is the constant `P_jΦ(x)` times `χ_ℓ²`, so the multiplier
`1−f_L` only ever acts on the single one-body profile

  `hRes fc κ ℓ z = χ_ℓ(z)² − lowMult fc κ ℓ (χ_ℓ²)(z) = (1−f_L)(χ_ℓ²)(z)`.

The whole content of `B3EpsRoot` is that `hRes` is *small*: the multiplier
`1−f_L` cuts momenta below `κ`, while `χ_ℓ²` is an `ℓ`-smooth bump, and
`κℓ ≫ 1` in FS's dilute regime — so `(1−f_L)(χ_ℓ²)` is of size
`(κℓ)^{-s}` for every `s` (we use `s = 49`, far above FS's `M−1 = 47`).

`bumpSq` is the *fixed* profile `χ²` whose ℓ-scalings are `χ_ℓ²`; the Fourier
decay of its transform is the analytic input (`kinFT_bumpSq_decay`).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixB3.Eps

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false

/-- The fixed bump `χ²` whose `ℓ`-scalings are the localisation windows. -/
def bumpSq (x : ℝ³) : ℝ := chi x ^ 2

/-- The fixed bump `χ²`, complexified (the argument of `kinFT`). -/
def bumpSqC (x : ℝ³) : ℂ := ((chi x ^ 2 : ℝ) : ℂ)

/-- FS's `(1−f_L)(χ_Λ²)`: the low-momentum multiplier `f_L = lowMult fc κ ℓ`
applied to the bump `χ_ℓ² = χU ℓ 0 · ²`, subtracted from the bump. -/
def hRes (fc : LowCut) (κ ℓ : ℝ) (z : ℝ³) : ℝ :=
  chiU ℓ 0 z ^ 2 - lowMult fc κ ℓ (fun w => chiU ℓ 0 w ^ 2) z

end Work.BoseFixB3.Eps
