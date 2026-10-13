/-
# N4 — the `F_*`-package of design §3.2, re-exported in the frozen namespace

The six estimates of design §3.2 are proved in `Submission/Work/FTS/Nonlinear/FstarPkg/`
(in the namespace `Work.FTS.Nonlinear.FstarPkg`, chosen by the provers of those files).
This module re-exports them under the **frozen** namespace `Work.FTS.Nonlin`, so that every
consumer of the N4 chapter finds them where `NOTES_N4.md` says they are.

`Work.Spaces.Gamma_WlInf` supplies `WlInf α l (Γ(θ)·z/(1+z)²) ≤ C` uniformly in `α`; hence
`WlInf α 4 (F_*) ≤ Cα`, `WlInf α 4 (D_zF_*) ≤ Cα`, `WlInf α 4 ((z+1)²/z·F_*) ≤ Cα`,
`WlInf α 4 (c2m·L₁₂(F_*)) ≤ Cα`, while `D_θF_*` gains one further factor `α`
(`D_θ` differentiates `Γ = (sinθcos²θ)^{α/3}`, `dthU_Gam_le`), so `WlInf α 4 (D_θF_*) ≤ Cα²`;
and `FK(F_*) = α·2z/(1+z)²` exactly.
-/
import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.Nonlinear.FstarPkg.Fstar_W
import Submission.Work.FTS.Nonlinear.FstarPkg.DthFstar_W
import Submission.Work.FTS.Nonlinear.FstarPkg.DzFstar_W
import Submission.Work.FTS.Nonlinear.FstarPkg.Fstar_z_W
import Submission.Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W
import Submission.Work.FTS.Nonlinear.FstarPkg.FK_Fstar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlin

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `F_* ∈ 𝒲^{4,∞}` with `|F_*|_{𝒲^{4,∞}} ≤ Cα`. -/
theorem Fstar_W :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.WlInfMem α 4 (Work.Construction.Fstar α) ∧
      Work.Spaces.WlInf α 4 (Work.Construction.Fstar α) ≤ C * α :=
  Work.FTS.Nonlinear.FstarPkg.Fstar_W

/-- `D_θ F_* ∈ 𝒲^{4,∞}` with `|D_θF_*|_{𝒲^{4,∞}} ≤ Cα²`. -/
theorem DthFstar_W :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.WlInfMem α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
      Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ C * α ^ 2 :=
  Work.FTS.Nonlinear.FstarPkg.DthFstar_W

/-- `D_z F_* ∈ 𝒲^{4,∞}` with `|D_zF_*|_{𝒲^{4,∞}} ≤ Cα`. -/
theorem DzFstar_W :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.WlInfMem α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) ∧
      Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ C * α :=
  Work.FTS.Nonlinear.FstarPkg.DzFstar_W

/-- `((z+1)²/z)F_* ∈ 𝒲^{4,∞}` with norm `≤ Cα`. -/
theorem Fstar_z_W :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 2 / z * Work.Construction.Fstar α z θ) ∧
      Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 2 / z * Work.Construction.Fstar α z θ)
        ≤ C * α :=
  Work.FTS.Nonlinear.FstarPkg.Fstar_z_W

/-- `c2m·L₁₂(F_*) ∈ 𝒲^{4,∞}` with norm `≤ Cα`. -/
theorem c2m_L12Fstar_W :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      Work.Spaces.WlInfMem α 4 (fun z θ => Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z) ∧
      Work.Spaces.WlInf α 4 (fun z θ => Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z) ≤ C * α :=
  Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W

/-- The angular moment of `F_*`: `FK(F_*) = α·2z/(1+z)²` exactly. -/
theorem FK_Fstar {α z : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.Construction.FK (Work.Construction.Fstar α) z = α * (2 * z / (1 + z) ^ 2) :=
  Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1

end Work.FTS.Nonlin
