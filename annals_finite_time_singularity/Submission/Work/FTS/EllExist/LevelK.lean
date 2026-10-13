/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS.EllExist.LevelK` — the existence node at an arbitrary weak-class level

The lead design of 2026-10-08 (`FTS/FTS_HARD_DESIGN.md`, §(A) item **A2**) needs the corrected
existence node of this area **at the weak-class level `EllWeakPos α 7`** (the `U`-slot of the
estimates is one order short at level `4`), with its inputs supplied by the new linear class
`ClassC` (`Submission/Work/FTS/FTS_HARD_STMTS.lean.txt`): `SmoothOpen g`, `HkMem α 7 g`, F_* ∈
C^∞(0,∞), the axis condition as a limit, `L₁₂(g)(0) = 0`.

This module therefore carries the two statements of `Main.lean`/`Exists.lean`/`ExistsFstar.lean`
at a *general* level `k`:

* `EllClassOk k α g Ψ` — `EllClassO` with `TT.EllWeakPos α k` in place of `α 4`;
* `ellClassOk_of_bslOp_node k` — the assembly (unconditional);
* `ellClassOk_exists_of_inputs k` — the corrected existence node, from the elliptic node
  `bslOp_sol_exists k` applied to `orthSource g` plus the explicit analytic inputs;
* `ellClassOk_exists_of_Fstar_smooth k` — the same with the three `Gsing` facts *derived* from
  three natural hypotheses on the angular moment (`F_* ∈ C^∞(0,∞)`, `F_*(r)/r ∈ L¹`, `g ∈ L²`).

The instantiation `k = 7` is `Work.FTS.EllExist.ellClassOk_exists_of_Fstar_smooth 7`; the consumer
supplies

* `SmoothOpen (orthSource g)` and `HkMem α 7 (orthSource g)` — from `ClassC.reg` and
  `ClassC.fsm` (`orthSource g = g - (15/4) sin 2θ · F_*(g)`, so `SmoothOpen` comes from
  `ClassC.reg` + `ClassC.fsm` and the honesty from `HkMem` plus a `Ly`-type majorant);
* the decay of `orthSource g` — from the pointwise decay of `g` and `F_*`;
* `F_* ∈ C^∞(0,∞)` (directly) and `IntegrableOn (F_*(r)/r) (Ioi 0)`, `L2Mem g`.

All the algebra of the shift is in `FTS/EllExist/Shift.lean` (`bslOp_shiftSing`,
`bslOp_shiftSing_of_ode`, `bslOp_eq_of_shiftSing_of_ode`, `Fstar_shiftSing`,
`Fstar_orthSource_zero`, `smoothOpen_shiftSing`, `tendsto_shiftSing`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.PhiStar.bslOp_sol_exists
import Submission.Work.FTS.PhiStar.bslOp_sol_exists_pp
import Submission.Work.FTS.PhiStar.EllNode8tr
import Submission.Work.FTS.EllipticEst.Gsing_contDiffOn_ode_of_Fstar_facts
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts
import Submission.Work.FTS.EllipticEst.Gsing_tendsto_atTop_zero
import Submission.Work.FTS.EllExist.Defs
import Submission.Work.FTS.EllExist.Shift
import Submission.Work.FTS.EllExist.Main

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllExist

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The existence class at an arbitrary weak-class level.**

`EllClassOk k α g Ψ` is the design's `EllClassO` with `TT.EllWeakPos α k` in place of
`TT.EllWeakPos α 4`: `Ψ` solves `bslOp α Ψ = g` on the open quadrant with the Dirichlet data and
the decay, is `C^∞` on the open quadrant, and the shifted unknown `Ψ + Gsing α g · sin 2θ` is a
datum of the weak hypothesis class of the `ℋ^k` estimate for the orthogonalised source
`orthSource g`. -/
def EllClassOk (k : ℕ) (α : ℝ) (g Ψ : Fn) : Prop :=
  Work.Elliptic.IsBslSol α g Ψ ∧ Work.FTS.EllipticEst.SmoothOpen Ψ ∧
  Work.FTS.EllipticEst.TT.EllWeakPos α k (Work.Elliptic.orthSource g) (shiftSing α g Ψ)

/-- `EllClassO` is the case `k = 4`. -/
theorem ellClassO_iff_ellClassOk_four (α : ℝ) (g Ψ : Fn) :
    EllClassO α g Ψ ↔ EllClassOk 4 α g Ψ := Iff.rfl

/-- **The assembly at level `k`**: from the elliptic node for the orthogonalised source and the
three singular-term facts about `Gsing α g`, the unshifted function `unshift α g Ψ'` is an element
of `EllClassOk k α g`. -/
theorem ellClassOk_of_bslOp_node (k : ℕ) {α : ℝ} {g : Fn}
    (hNode : ∃ Ψ' : Fn,
      Work.FTS.EllipticEst.TT.EllWeakPos α k (Work.Elliptic.orthSource g) Ψ' ∧
        Work.Elliptic.IsBslSol α (Work.Elliptic.orthSource g) Ψ')
    (hGsm : ∀ n : ℕ, ContDiffOn ℝ (n : WithTop ℕ∞) (Work.Elliptic.Gsing α g) (Set.Ioi 0))
    (hGode : ∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α g) z') z
        + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α g) z
      = (15 / 4) * Work.Elliptic.Fstar g z)
    (hGdec : Tendsto (fun z => Work.Elliptic.Gsing α g z) atTop (𝓝 0)) :
    ∃ Ψ : Fn, EllClassOk k α g Ψ := by
  obtain ⟨Ψ', hWeak, hSol⟩ := hNode
  have hΨ'Sm : Work.FTS.EllipticEst.SmoothOpen Ψ' :=
    Work.FTS.EllipticEst.smoothOpen_of_forall
      (fun n => Work.FTS.EllipticEst.TT.EllWeakPos.smooth hWeak n)
  have hSmU : Work.FTS.EllipticEst.SmoothOpen (unshift α g Ψ') :=
    smoothOpen_unshift α g Ψ' hΨ'Sm hGsm
  refine ⟨unshift α g Ψ', ?_, hSmU, ?_⟩
  · refine ⟨?_, unshift_zero α g Ψ' hSol.2.1, unshift_pi_half α g Ψ' hSol.2.2.1, ?_⟩
    · intro z hz θ hθ0 hθ1
      have hcos : Real.cos θ ≠ 0 :=
        ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
      have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
      have hAt : ContDiffAt ℝ 2 (Function.uncurry (unshift α g Ψ')) (z, θ) :=
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall (unshift α g Ψ')).mp hSmU 2).contDiffAt
          (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
      have hGAt : ContDiffAt ℝ 2 (Work.Elliptic.Gsing α g) z :=
        (hGsm 2).contDiffAt (isOpen_Ioi.mem_nhds hz)
      have hsol : Work.Elliptic.bslOp α (shiftSing α g (unshift α g Ψ')) z θ
          = Work.Elliptic.orthSource g z θ := by
        rw [shiftSing_unshift α g Ψ']
        exact hSol.1 z hz θ hθ0 hθ1
      exact bslOp_eq_of_shiftSing_of_ode α g (unshift α g Ψ') z θ hAt hGAt hcos
        (hGode z hz) hsol
    · intro θ hθ
      exact tendsto_unshift α g Ψ' θ (hSol.2.2.2 θ hθ) hGdec
  · show Work.FTS.EllipticEst.TT.EllWeakPos α k (Work.Elliptic.orthSource g)
      (shiftSing α g (unshift α g Ψ'))
    rw [shiftSing_unshift α g Ψ']
    exact hWeak

/-- **The corrected existence node at level `k`.**  Every `g` whose orthogonalised source lies in
the weak class of the `ℋ^k` estimate and whose angular moment satisfies the three analytic inputs
has a stream function in `EllClassOk k α g`. -/
theorem ellClassOk_exists_of_inputs (k : ℕ) : ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ →
    ∀ g : Fn,
      Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) →
      Work.Spaces.HkMem α k (Work.Elliptic.orthSource g) →
      (∀ θ ∈ Work.Spaces.Iθ,
        Tendsto (fun z => Work.Elliptic.orthSource g z θ) atTop (𝓝 0)) →
      (∀ n : ℕ, ContDiffOn ℝ (n : WithTop ℕ∞) (Work.Elliptic.Gsing α g) (Set.Ioi 0)) →
      (∀ z ∈ Set.Ioi (0 : ℝ),
        α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α g) z') z
          + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α g) z
        = (15 / 4) * Work.Elliptic.Fstar g z) →
      Tendsto (fun z => Work.Elliptic.Gsing α g z) atTop (𝓝 0) →
      ∃ Ψ : Fn, EllClassOk k α g Ψ := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro α hα hα4 g hSm hHk hDec hGsm hGode hGdec
  refine ellClassOk_of_bslOp_node k ?_ hGsm hGode hGdec
  exact Work.FTS.PhiStar.bslOp_sol_exists k α (Work.Elliptic.orthSource g) hα hα4 hSm hHk
    (fun z _ => Fstar_orthSource_zero g z) hDec

/-- **The corrected existence node at level `k`, repaired input level `k+2`** (lead install
2026-10-11, `cbc/fts_phistar_REVIEW.md`).  Identical to `ellClassOk_exists_of_inputs` except that
the orthogonalised source is assumed in `ℋ^{k+2}` and the node is the repaired
`PhiStar.bslOp_sol_exists_pp k` (the original node is false). -/
theorem ellClassOk_exists_of_inputs_pp (k : ℕ) : ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ →
    ∀ g : Fn,
      Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) →
      Work.Spaces.HkMem α (k + 2) (Work.Elliptic.orthSource g) →
      (∀ θ ∈ Work.Spaces.Iθ,
        Tendsto (fun z => Work.Elliptic.orthSource g z θ) atTop (𝓝 0)) →
      (∀ n : ℕ, ContDiffOn ℝ (n : WithTop ℕ∞) (Work.Elliptic.Gsing α g) (Set.Ioi 0)) →
      (∀ z ∈ Set.Ioi (0 : ℝ),
        α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α g) z') z
          + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α g) z
        = (15 / 4) * Work.Elliptic.Fstar g z) →
      Tendsto (fun z => Work.Elliptic.Gsing α g z) atTop (𝓝 0) →
      ∃ Ψ : Fn, EllClassOk k α g Ψ := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro α hα hα4 g hSm hHk hDec hGsm hGode hGdec
  refine ellClassOk_of_bslOp_node k ?_ hGsm hGode hGdec
  exact Work.FTS.PhiStar.bslOp_sol_exists_pp k α (Work.Elliptic.orthSource g) hα hα4 hSm hHk
    (fun z _ => Fstar_orthSource_zero g z) hDec

/-- **The existence node at level `8` from the trace-strengthened node** (lead install R6,
2026-10-11, `cbc/fts_ellnode_ruling.md` §4.4(1)).  As `ellClassOk_exists_of_inputs_pp 8`, with the
extra hypothesis `ThetaTraces α 10 (orthSource g)`; the node is `PhiStar.EllNode8tr_holds`
(Route B′) instead of `bslOp_sol_exists_pp 8`. -/
theorem ellClassOk_exists_of_inputs_tr : ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ →
    ∀ g : Fn,
      Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) →
      Work.Spaces.HkMem α 10 (Work.Elliptic.orthSource g) →
      Work.FTS.PhiStar.ThetaTraces α 10 (Work.Elliptic.orthSource g) →
      (∀ θ ∈ Work.Spaces.Iθ,
        Tendsto (fun z => Work.Elliptic.orthSource g z θ) atTop (𝓝 0)) →
      (∀ n : ℕ, ContDiffOn ℝ (n : WithTop ℕ∞) (Work.Elliptic.Gsing α g) (Set.Ioi 0)) →
      (∀ z ∈ Set.Ioi (0 : ℝ),
        α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α g) z') z
          + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α g) z
        = (15 / 4) * Work.Elliptic.Fstar g z) →
      Tendsto (fun z => Work.Elliptic.Gsing α g z) atTop (𝓝 0) →
      ∃ Ψ : Fn, EllClassOk 8 α g Ψ := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro α hα hα4 g hSm hHk hTr hDec hGsm hGode hGdec
  refine ellClassOk_of_bslOp_node 8 ?_ hGsm hGode hGdec
  exact Work.FTS.PhiStar.EllNode8tr_holds α (Work.Elliptic.orthSource g) hα hα4 hSm hHk hTr
    (fun z _ => Fstar_orthSource_zero g z) hDec

/-- **The corrected existence node at level `k`, in terms of the angular moment.**  The three
`Gsing` facts are derived from `F_* ∈ C^∞(0,∞)`, `IntegrableOn (F_*(r)/r) (Ioi 0)` and `L2Mem g`
via `Gsing_contDiffOn_ode_of_Fstar_facts`, `HasDerivAt_L12_of_Fstar_facts` and
`Gsing_tendsto_atTop_zero`. -/
theorem ellClassOk_exists_of_Fstar_smooth (k : ℕ) : ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ →
    ∀ g : Fn,
      Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.orthSource g) →
      Work.Spaces.HkMem α k (Work.Elliptic.orthSource g) →
      (∀ θ ∈ Work.Spaces.Iθ,
        Tendsto (fun z => Work.Elliptic.orthSource g z θ) atTop (𝓝 0)) →
      (∀ m : ℕ, ContDiffOn ℝ (m : WithTop ℕ∞) (Work.Elliptic.Fstar g) (Set.Ioi 0)) →
      MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar g r / r) (Set.Ioi 0) →
      Work.Spaces.L2Mem g →
      ∃ Ψ : Fn, EllClassOk k α g Ψ := by
  obtain ⟨α₀, hα₀, hmain⟩ := ellClassOk_exists_of_inputs k
  refine ⟨α₀, hα₀, fun α hα hα4 g hSm hHk hDec hFstSm hFint hL2 => ?_⟩
  have hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 g) (-(3 * Work.Elliptic.Fstar g z / z)) z :=
    Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts g hFstSm hFint
  obtain ⟨hGsm, hGode⟩ :=
    Work.FTS.EllipticEst.Gsing_contDiffOn_ode_of_Fstar_facts α g hα hFstSm hFint hL12
  exact hmain α hα hα4 g hSm hHk hDec hGsm hGode
    (Work.FTS.EllipticEst.Gsing_tendsto_atTop_zero α g hα hL2)

end Work.FTS.EllExist
