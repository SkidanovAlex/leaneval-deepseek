import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.E4R3.Flow5
import Submission.Work.FTS.StrongEps.EpsE4Thr.XStep
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.epsFlowP_of_xball

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Flow5Leaves/FlowOfXBall.lean` — OPEN LEAF-A `epsFlowP_of_xball` (producer of `EpsFlowP`)

curric-46 install 2026-10-12 (`cbc/fts_regularity_interface.md` §2, §4.3; REVIEW (a), F4).  TRUE at
fixed `ε` (constants may depend on `ε`, `R`, the packages and the solution).

Route: `Feps w = P₀ J_ε profRHS(P₀ J_ε w)`.
* `rhs`, `rhsBdd`: `EpsEngine.Feps_data_of_xball8` (`SmoothOpen`, `HkMem 8`, `HkNorm 8 ≤ Ce8` on the
  `XBall`) + monotonicity to level 6.
* `wp`: `epsWP τ = profRHS(W)`, `XDataClean` gives `HkMem 4`, lifted by `HkMem_Jeps`.
* `rhsCont`: `Feps u − Feps v = Pz(J_ε Δ)` (`Jeps_sub_eq`, `Pz_sub_eq`, `L12_sub_HkMem`); the
  pre-mollified bound `EpsMem Δ ∧ EpsSq Δ ≤ K·EpsSq(u−v)` is inside `ConjTwoSq` (lines 115–152:
  `DeltaXnBound`, `DiffTraces`, `TraceToEpsMem`) — expose it as `ConjTwoSq_pre`; then
  `HkSq_JepsPz_le` at k = 6, plus the curve's `EpsSq`-Lipschitz bound.
* curve `EpsSq`-Lipschitz: Volterra identity by FTC (continuity of `τ ↦ epsRHSP τ z θ` from
  `WeakRHS.continuousOn_epsRHSP_joint`), then `EpsSq_intervalIntegral_le_gen` with the `hbd` of
  `EpsRHSPLipX_Sq`.
* `deriv`: `rem = ∫_τ^s (Feps g_r − Feps g_τ) dr` priced by `HkMem_intervalIntegralPerz`, gates from
  `Feps_gates_six`/`perz_Feps_six`.  Cautions: (i) that lemma quantifies over the whole window, so
  apply it to the reparametrised family `r ↦ H(τ+r)` on `[0, s−τ]` (symmetrically for `s < τ`);
  (ii) the joint measurability is needed for the DIFFERENCE family — expose the slot-level `hjoint`
  inside `hjoint_HkIntegrand_epsRHSP_fam_of_gate`.
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

/-- **OPEN LEAF-A (producer): a regular solution whose slices stay in a fixed `X`-ball carries
`EpsFlowP`** (at fixed `ε`, with the packages and `MuLamOK` at the ball radius `C₁`).  See the
module docstring for the route.  No `ε`-uniformity is claimed. -/
theorem epsFlowP_of_xball {α C₁ Ce Cs R ε δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {h₀ : Fn} {g : Fam}
    (hα : α ∈ Ioc (0 : ℝ) 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : MuLamOK α C₁ Φs E)
    (hδ : 0 < δ) (hsol : IsEpsSolP α ρ ε δ Φs E h₀ g) (hreg : EpsRegP α ρ ε δ g)
    (hX : ∀ τ ∈ Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R C₁ (slice g τ)) :
    EpsFlowP α ρ ε δ Φs E g :=
  Work.FTS.StrongEps.EpsE4Thr.Leaves.epsFlowP_of_xball hα hρ hε hε1 hR hEll hstar hml hδ hsol
    hreg hX

end Work.FTS.StrongEps.EpsE4Thr.E4R5
