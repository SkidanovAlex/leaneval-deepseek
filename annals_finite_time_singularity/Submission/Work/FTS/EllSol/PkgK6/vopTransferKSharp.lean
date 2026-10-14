import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.EllSol.PkgK5.VopcPth2Transfer
import Submission.Work.FTS.EllSol.PkgK5.VopcPth2TransferGen
import Submission.Work.FTS.EllSol.PkgK5.tracesK5_sharp
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.StrongEps.PZeroAux.mixed_Pz
import Submission.Work.FTS.StrongPersist.SP6.F0SixYblk
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.mixed_mul_le
-- ===== merged: Submission.Work.FTS.ClassC.RopGen.Transfer =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## The definitional identification with the residual -/

/-- `Construction.PhiTil α g Ψ = Elliptic.EllResid α g Ψ` (definitional). -/
theorem phiTil_eq_EllResid_gen (α : ℝ) (g Ψ : Fn) :
    Work.Construction.PhiTil α g Ψ = Work.Elliptic.EllResid α g Ψ := by
  funext z θ
  simp only [Work.Construction.PhiTil, Work.Elliptic.EllResid, Work.Construction.Theta,
    Work.Construction.s2_eq]
  rw [show Work.Elliptic.L12 g z = Work.Construction.L12 g z from rfl]

/-! ## Smoothness on the open quadrant, at general solution level -/

/-- `Ḡ(α,g)·sin 2θ` is `C^∞` on the open quadrant for every `g` of the class `C`
(the level-parametric form of `smoothOpen_GbarSin_classC`, whose `7` was incidental). -/
theorem smoothOpen_GbarSin_gen' {α : ℝ} (hα : 0 < α) {g : Fn} (hg : ClassC α g) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) :=
  Work.FTS.EllSol.PkgK5.smoothOpen_GbarSin_gen hα 7 hg.reg hg.fsm hg.mem

/-- **The residual `PhiTil α g Ψ` is `C^∞` on the open quadrant** at *any* solution level
(the level-`K` form of `smoothOpen_phiTil`; only `ClassC α g` and the open-quadrant smoothness
carried by `EllClassOk K` are used). -/
theorem smoothOpen_phiTil_gen {α : ℝ} {K : ℕ} {g Ψ : Fn} (hα : 0 < α) (hg : ClassC α g)
    (h : Work.FTS.EllExist.EllClassOk K α g Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.PhiTil α g Ψ) := by
  have hSmW : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllExist.shiftSing α g Ψ) :=
    Work.FTS.EllipticEst.smoothOpen_of_forall
      (Work.FTS.EllipticEst.TT.EllWeakPos.smooth h.2.2)
  have hGnegSm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(Work.Elliptic.Gbar α g z)) * Real.sin (2 * θ)) := by
    have hL := smoothOpen_GbarSin_gen' hα hg
    refine Work.FTS.EllipticEst.SmoothOpen.congr (hL.const_mul' (-1)) ?_
    intro z' θ' _ _ _
    ring
  have hdecomp : Work.Construction.PhiTil α g Ψ
      = fun z' θ' => Work.FTS.EllExist.shiftSing α g Ψ z' θ'
          + (-(Work.Elliptic.Gbar α g z')) * Real.sin (2 * θ') := by
    funext z' θ'
    rw [phiTil_eq_EllResid_gen]
    simp only [Work.Elliptic.EllResid, Work.FTS.EllExist.shiftSing_apply, Work.Elliptic.Gsing,
      Work.Elliptic.Gstar]
    ring
  refine Work.FTS.EllipticEst.SmoothOpen.congr
    (Work.FTS.EllipticEst.SmoothOpen.add hSmW hGnegSm) ?_
  intro z' θ' _ _ _
  exact (congrFun (congrFun hdecomp z') θ').symm





/-! ## The two pieces of the transfer, and the transfer itself -/




end Work.FTS.ClassC
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK6.vopTransferKSharp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK6

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Two book-keeping helpers (the `k`-independent clone of `vopcK5c_resid_smooth` /
`vopcK5c_slice_smooth`) -/

/-- **`EllResid α g Φg` is `C^∞` on the open quadrant** for a source `g` of the class `C` and a
straightened unknown `Ψ̂ = ellShift α g Φg` smooth there: `Ξ = Ψ̂ − Ḡ(α,g)·sin 2θ`, and both
summands are smooth (`ClassC` supplies the all-order smoothness of `F_*(g)` and `HkMem α 7 g`,
i.e. precisely the hypotheses of `smoothOpen_negGbarSin_classC`). -/
theorem vopK6_resid_smooth {α : ℝ} {g Φg : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hC : Work.FTS.EllSol.ClassC α g)
    (hX : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllSol.ellShift α g Φg)) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.EllResid α g Φg) := by
  have hG := Work.FTS.EllSol.PkgK5.smoothOpen_negGbarSin_classC (α := α) (g := g) hα
    hC.reg hC.fsm hC.mem
  refine Work.FTS.EllipticEst.SmoothOpen.congr
    (Work.FTS.EllipticEst.smoothOpen_add hX hG) ?_
  intro z θ _ _ _
  rw [Work.FTS.EllSol.EllResid_eq_ellShift_sub_Gbar_point]
  simp only [Work.FTS.EllSol.ellShift_apply]
  ring

/-- **The angular slices of the radial iterates are `C^∞`** on `(0,π/2)`.  This is the
smoothness hypothesis consumed by `divSinK5` (whose interface asks for `C^∞` in the honest
order `Work.Stability.smoothOrder`). -/
theorem vopK6_slice_smooth {Ξ : ℝ → ℝ → ℝ} (hΞ : Work.FTS.EllipticEst.SmoothOpen Ξ)
    (j : ℕ) {z : ℝ} (hz : 0 < z) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Work.Spaces.DzIter j Ξ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have h1 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DzIter j Ξ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp (hΞ.DzIter j) n
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.DzIter j Ξ)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    intro x hx m _
    exact h1 m x hx m le_rfl
  exact Work.FTS.LocData.contDiffOn_slice_θ (s := Set.Ioi 0)
    (t := Set.Ioo 0 (Real.pi / 2)) h2 hz

theorem vopTransferKSharp (k : ℕ) (hk : 2 ≤ k) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g Φg : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllSol.ClassC α g →
      Work.Spaces.HkMem α k g →
      Work.FTS.StrongGlobal.IsBslSolPos α g Φg →
      Work.FTS.EllipticEst.SmoothOpen Φg →
      Work.FTS.EllipticEst.TT.EllWeakPos α k (Work.Elliptic.orthSource g)
        (Work.FTS.EllSol.ellShift α g Φg) →
      Work.Spaces.HkMem α (k + 2) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
        (Work.FTS.EllSol.ellShift α g Φg) z θ) →
      Work.Spaces.HkMem α (k + 2) (Work.Elliptic.orthSource g) →
      Work.FTS.VocabO.HQo α k (Work.Construction.Vop (Work.Construction.PhiTil α g Φg)) ∧
      Work.Spaces.HkNorm α k (Work.Construction.Vop (Work.Construction.PhiTil α g Φg))
        ≤ C * (α ^ 2 * Work.Spaces.HkNorm α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Φg) z θ)
            + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
            + Work.Spaces.HkNorm α k g) := by
  -- ## the two independent pieces
  obtain ⟨CB, hCB0, hB⟩ := Work.FTS.EllSol.PkgK5.VopcPth2TransferGen k
  obtain ⟨CV, hCV0, hV⟩ := Work.FTS.EllSol.PkgK5.VopcCore k (by omega)
  refine ⟨CV * CB, mul_pos hCV0 hCB0, ?_⟩
  intro α g Φg hα hα4 hC hmemg hsol hsmo hweak hAh hFmem
  -- ## the straight unknown is smooth and carries the traces
  have hXsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllSol.ellShift α g Φg) :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hweak.smooth
  have htrX := Work.FTS.EllSol.PkgK5.tracesK5_sharp k hk α g Φg hα hα4 hC hsol hsmo
    hweak hAh hFmem
  have htrΞ := Work.FTS.EllSol.PkgK5.residTracesK5 k α g Φg hα hα4 hC hXsm htrX
  -- ## the smoothness of the residual and of its slices
  have hΞsm : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.EllResid α g Φg) :=
    vopK6_resid_smooth (α := α) (g := g) (Φg := Φg) hα hC hXsm
  have hslice : ∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Work.Spaces.DzIter j (Work.Elliptic.EllResid α g Φg) z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    fun z hz j _ => vopK6_slice_smooth hΞsm j hz
  -- ## the two pieces
  have hBk := hB α g Φg hα hα4 hC.reg hC.fsm hmemg hXsm hweak.memB
  have hVk := hV α (Work.Elliptic.EllResid α g Φg) hα hα4 hΞsm
    (fun j hj z hz => htrΞ j (by omega) z hz) hslice hBk.1
  rw [Work.FTS.EllipticEst.Vop_PhiTil_eq]
  refine ⟨hVk.1, ?_⟩
  -- ## the arithmetic of the constants
  have hA0 : (0 : ℝ) ≤ α ^ 2 * Work.Spaces.HkNorm α k
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Φg) z θ) :=
    mul_nonneg (sq_nonneg α) (Work.Spaces.HkNorm_nonneg α k _)
  have hCVnn : (0 : ℝ) ≤ CV := le_of_lt hCV0
  calc Work.Spaces.HkNorm α k (Work.FTS.EllipticEst.Vop α (Work.Elliptic.EllResid α g Φg))
      ≤ CV * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α g Φg)) :=
        hVk.2
    _ ≤ CV * (CB * (Work.Spaces.HkNorm α k
            (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
          + Work.Spaces.HkNorm α k g)) :=
        mul_le_mul_of_nonneg_left hBk.2 hCVnn
    _ = CV * CB * (Work.Spaces.HkNorm α k
            (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
          + Work.Spaces.HkNorm α k g) := by ring
    _ ≤ CV * CB * (α ^ 2 * Work.Spaces.HkNorm α k
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Φg) z θ)
          + Work.Spaces.HkNorm α k
            (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
          + Work.Spaces.HkNorm α k g) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith [hA0]

end Work.FTS.EllSol.PkgK6
end
end
