import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.E4R3.Flow5
import Submission.Work.FTS.CoercivityFix.Assembly.Defs
import Submission.Work.FTS.StrongEps.E4R3.Flow5Leaves.IP4_JfamP_hasDerivWithinAt_of_flow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Flow5Leaves/IP4Flow.lean` — OPEN LEAF-C: the level-four product rule over `EpsFlowP`

curric-46 install 2026-10-12 (`cbc/fts_regularity_interface.md` §4.3, REVIEW F3).  TRUE.

Plan: a copy of the PROVED S4 proof `rawE6_hasDerivWithinAt_of_flow` (`E4R3/Flow5.lean`) at level
4 on `x_τ = P₀ J_ε (slice g τ)`, with derivative `P₀ J_ε (epsRHSP τ)`.
* remainder: `P₀J_ε(rem) = rem` of `x` by linearity (`Jeps_sub_eq` + scalar factor; `Pz_sub_eq` +
  `L12_sub_HkMem`); price it by **`PzHkNormFour`** (`HkNorm k (Pz f) ≤ A·HkNorm 4 f`, k ≤ 4) +
  **`HkSq_Jeps_le`** (`HkSq k (J_ε f) ≤ e^{Cε} HkSq k f`, membership `HkMem_Jeps`) +
  **`HkNorm_mono_of_mem`** (4 ≤ 6): `‖P₀J_ε rem‖₄ ≤ A'‖rem‖₆ = o(|s-τ|)` from `hF.deriv`.
  (Do NOT use `HkSq_JepsPz_le` on the remainder: it needs `EpsSq rem`, i.e. vanishing traces, which
  raw slices do not carry.)
* form: `IP4_cs_HQo`, `IP4_add_Qd`, `IP4_symm_all` (IPGen/…); `x_τ ∈ HQo 4` from `ClassC`
  (`HkMem 7`, `hreg.2 τ hτ`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R5

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6 concat)
open Work.FTS.VocabO (HQo)
open Work.FTS.StrongEps
open Work.FTS.StrongEps.EpsE4Thr
open Work.FTS.StrongEps.EpsE4Thr.E4R4 (rawE6 IP6o)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **LEAF-C: H4's energy identity from `EpsFlowP`** — the level-four product rule for the
projected mollified family `x_τ = P₀ J_ε (slice g τ)`: `x` is `ℋ⁴`-differentiable with derivative
`P₀ J_ε (epsRHSP τ)` (linearity of `P₀ J_ε`; remainder priced by `PzHkNormFour` + `HkSq_Jeps_le` +
`HkNorm_mono_of_mem` from `hF.deriv`), and `IP4` is bilinear, symmetric and bounded on `HQo α 4`.
It replaces the interface items (I)–(V) of `EnergyDeriv_IP4_JfamP_of_solution`.

**PROVED** (2026-10-12) in the sibling module
`E4R3/Flow5Leaves/IP4_JfamP_hasDerivWithinAt_of_flow.lean`; the declaration below is re-pointed at
it, so this file no longer carries a `sorry`. -/
theorem IP4_JfamP_hasDerivWithinAt_of_flow {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {g : Fam} (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hc₁' : 0 ≤ c₁') (hc₂' : 0 ≤ c₂') (hc₁'' : 0 ≤ c₁'') (hc₂'' : 0 ≤ c₂'')
    (hρ : IsSmoothKernel ρ) (hα : α ∈ Ioc (0 : ℝ) 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hreg : EpsRegP α ρ ε T g) (hF : EpsFlowP α ρ ε T Φs E g) {τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    HasDerivWithinAt
      (fun s => Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
        (slice (JfamP ρ ε g) s) (slice (JfamP ρ ε g) s))
      (2 * Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
        (Pz (Jeps ρ ε (epsRHSP α ρ ε Φs E g τ))) (slice (JfamP ρ ε g) τ))
      (Icc 0 T) τ :=
  Work.FTS.StrongEps.E4R3.Flow5Leaves.IP4_JfamP_hasDerivWithinAt_of_flow
    c₁ c₂ c₁' c₂' c₁'' c₂'' hc₁ hc₂ hc₁' hc₂' hc₁'' hc₂'' hρ hα hε hε1 hreg hF hτ

end Work.FTS.StrongEps.EpsE4Thr.E4R5
