import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.PhiStar.EllNode8tr
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sq_mul_div_rpow

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


end Work.FTS.EllExist
