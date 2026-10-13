/-
# `Work.FTS_RegExport.Basic` — the shared header of the FTS_RegExport subproject

This is the chapter that proves every open producer of
`Submission/Work/FTS/RegExportIface/Producers.lean` as `<name>_proved`, with the *identical*
statement (same `open`s, same `variable`s), so that `FinalV2.Producers.regPkg7'` — and through it
`theorem_1_v2` — can be built on `regExport_proved` instead of on the `sorry`-ed interface.

`Submission/Work/FTS/RegExportIface/*` and `Submission/Work/FTS/FinalV2/*` are FROZEN: nothing here
edits them, and every statement below is a verbatim copy of the corresponding one there.

| item | theorem | file |
|---|---|---|
| RX-A1  | `abs_mixed_le_HkNorm_C4_proved`      | `A1.lean` |
| RX-A1w | `abs_mixed_le_HkNorm_C4_w_proved`    | `A1w.lean` |
| RX-A2  | `lim_mixed_bounds_proved`            | `A2.lean` |
| RX-A2w | `lim_mixed_weighted_proved`          | `A2w.lean` |
| RX-B   | `l12_zero_lim_proved`                | `B.lean` |
| RX-T0  | `dtau_mixed_proved`                  | `T0.lean` |
| RX-T   | `transport_weighted_proved`          | `T.lean` |
| RX-St1 | `st1Export_proved`                   | `St1.lean` |
| RX-VP  | `velPkg_proved`                      | `VP.lean` |
| RX-R7  | `r7Block_proved`                     | `R7.lean` |
| RX-Supp| `suppExport_proved`                  | `Supp.lean` |
| RX-R1  | `r1Block_proved`                     | `R1.lean` |
| RX-R5  | `r5Parts_proved`                     | `R5.lean` |
| RX0    | `forall_regPkg_of_parts'_proved`     | `RX0/Assembly.lean` |
| top    | `regExport_proved`                   | `Assembly.lean` |
-/

import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.RegExportIface.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.RegPkgGal (extG RegPkg' St1Class R5Parts Avort Bdyn)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-! ## §1 Elementary facts about the weight `ω = z²Γ(θ)/(1+z)²` -/

/-- `Γ(θ) ≥ 0` on `Iθ`. -/
theorem Gamma_nonneg {α : ℝ} {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.Regularity.Gamma α θ :=
  Work.ConstructionInstance.Gamma_nonneg hθ

/-- `Γ(θ) ≤ 1` on `Iθ`. -/
theorem Gamma_le_one {α : ℝ} (hα : 0 ≤ α) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.Regularity.Gamma α θ ≤ 1 :=
  Work.ConstructionInstance.Gamma_le_one hα hθ

/-- `ω α z θ ≥ 0` on the closed quadrant. -/
theorem omega_nonneg {α z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.RegExportIface.ω α z θ := by
  have hΓ : 0 ≤ Work.FTS.Regularity.Gamma α θ := Gamma_nonneg hθ
  have h1 : (0:ℝ) < (1 + z) ^ 2 := by positivity
  have h2 : 0 ≤ z ^ 2 := sq_nonneg z
  simp only [Work.FTS.RegExportIface.ω]
  exact div_nonneg (mul_nonneg h2 hΓ) h1.le

/-- `ω α z θ = 0` at `z = 0`. -/
theorem omega_zero_z (α θ : ℝ) : Work.FTS.RegExportIface.ω α 0 θ = 0 := by
  simp [Work.FTS.RegExportIface.ω]

end Work.FTS_RegExport
