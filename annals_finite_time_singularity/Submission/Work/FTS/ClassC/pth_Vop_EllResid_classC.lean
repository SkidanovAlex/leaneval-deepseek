import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.EllSol.VthAuxC.helpersC
import Submission.Work.Elliptic.Algebra
import Submission.Work.FTS.EllipticEst.Cert.HkMem_pthIter2_EllResid
import Submission.Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen
import Submission.Work.FTS.EllipticEst.EllHyp_certificates

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The pointwise identity `∂_θ(Vop α Ξ) = -orthSource g - α²z²∂_z²Ψ̂ - α(5+α)z∂_zΨ̂ - 6Ξ`

For a datum `g` of the linear class `C` (`Work.FTS.ClassC.ClassC α g`) and a stream function
`Ψ` in the elliptic class at level `7` (`Work.FTS.EllExist.EllClassOk 7 α g Ψ`), write

* `Ψ̂ := shiftSing α g Ψ = Ψ + Gsing α g · sin 2θ` — the *straight* unknown, the one whose
  equation is `bslOp α Ψ̂ = orthSource g` on the open quadrant (`EllWeakPos.eq`, a field of
  `EllClassOk`), and
* `Ξ := EllResid α g Ψ = Ψ - (1/(4α))·sin 2θ·L₁₂(g) = Ψ̂ - Ḡ(α,g)·sin 2θ` — the residual.

Then, on the open quadrant,

`∂_θ(Vop α Ξ) = -(L₀Ξ + 6Ξ) = -(L₀Ψ̂ + 6Ξ)`, since `L₀(Ḡ·sin 2θ) = 0` (`Lzero_sin_two_mul`)
and `L₀` is additive on the open quadrant; and the equation for `Ψ̂` turns `L₀Ψ̂` into
`orthSource g + α²z²∂_z²Ψ̂ + α(5+α)z∂_zΨ̂`.  This is the `ClassC`/`EllClassOk`-`shiftSing`
instance of `Work.FTS.EllSol.pth_Vop_PhiTil_eq`, the `V`-slot companion of Theorem
`RemovingL12`: the singular terms cancel and **no `α^{-1}` survives**.

The only smoothness input not already a field of the two classes is the `C^∞`-regularity of the
layer `Ḡ(α,g)·sin 2θ` on the open quadrant, obtained from the all-order smoothness of the
angular moment `F_*(g)` (`ClassC.fsm`) and the honesty `HkMem α 7 g`. -/

/-- **`Ḡ(α,g)·sin 2θ` is `C^∞` on the open quadrant** for a datum of the class `C` (no
restriction on `α` beyond `0 < α`): `Ḡ(α,g) ∈ C^∞((0,∞))` because `Gsing` is smooth on `(0,∞)`
and `L₁₂(g)` is (its derivative is `-3F_*(g)(z)/z`, which is smooth on `(0,∞)`). -/
theorem smoothOpen_GbarSin_classC {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hreg : Work.FTS.EllipticEst.SmoothOpen g) (hfsm : ∀ m : ℕ, ContDiffOn ℝ m
      (Work.Elliptic.Fstar g) (Set.Ioi 0)) (hmem : Work.Spaces.HkMem α 7 g) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) := by
  have hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar g r / r)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen α 7 g hreg hmem
  have hGbsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Gbar α g) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.Cert.Gbar_contDiffOn_Ioi α g hα hfsm hFint
  exact Work.FTS.EllipticEst.SmoothOpen.sep_mul hGbsm (by fun_prop)

theorem pth_Vop_EllResid_classC {α : ℝ} {g Ψ : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hg : Work.FTS.ClassC.ClassC α g) (hO : Work.FTS.EllExist.EllClassOk 7 α g Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pth (Work.FTS.EllipticEst.Vop α (Work.Elliptic.EllResid α g Ψ)) z θ
      = -(Work.Elliptic.orthSource g z θ)
        - α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllExist.shiftSing α g Ψ) z θ
        - (α * (5 + α) * z) * Work.Spaces.pz (Work.FTS.EllExist.shiftSing α g Ψ) z θ
        - 6 * Work.Elliptic.EllResid α g Ψ z θ := by
  have hcos : Real.cos θ ≠ 0 := by
    have h1 : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo h1)
  -- the weak class of the shifted unknown, a field of `EllClassOk`
  have hweak : Work.FTS.EllipticEst.TT.EllWeakPos α 7 (Work.Elliptic.orthSource g)
      (Work.FTS.EllExist.shiftSing α g Ψ) := hO.2.2
  have hSmW : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllExist.shiftSing α g Ψ) :=
    Work.FTS.EllipticEst.smoothOpen_of_forall
      (Work.FTS.EllipticEst.TT.EllWeakPos.smooth hweak)
  -- smoothness of the layer `-(Ḡ)·sin 2θ`
  have hGnegSm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-(Work.Elliptic.Gbar α g z)) * Real.sin (2 * θ)) := by
    have hL := smoothOpen_GbarSin_classC (α := α) (g := g) hα hg.reg hg.fsm hg.mem
    refine Work.FTS.EllipticEst.SmoothOpen.congr (hL.const_mul' (-1)) ?_
    intro z' θ' _ _ _
    ring
  -- the decomposition `Ξ = Ψ̂ - Ḡ·sin 2θ`
  have hdecomp : Work.Elliptic.EllResid α g Ψ
      = fun z' θ' => Work.FTS.EllExist.shiftSing α g Ψ z' θ'
          + (-(Work.Elliptic.Gbar α g z')) * Real.sin (2 * θ') := by
    funext z' θ'
    simp only [Work.Elliptic.EllResid, Work.FTS.EllExist.shiftSing_apply, Work.Elliptic.Gsing,
      Work.Elliptic.Gstar]
    ring
  have hSmΞ : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.EllResid α g Ψ) := by
    refine Work.FTS.EllipticEst.SmoothOpen.congr
      (Work.FTS.EllSol.vthC_smoothOpen_add hSmW hGnegSm) ?_
    intro z' θ' _ _ _
    exact (congrFun (congrFun hdecomp z') θ').symm
  -- (1) `∂_θ(Vop Ξ) = -(L₀Ξ + 6Ξ)`
  have h1 : Work.Spaces.pth (Work.FTS.EllipticEst.Vop α (Work.Elliptic.EllResid α g Ψ)) z θ
      = -(Work.Elliptic.Lzero (Work.Elliptic.EllResid α g Ψ) z θ
          + 6 * Work.Elliptic.EllResid α g Ψ z θ) :=
    Work.FTS.EllSol.vthC_pth_Vop_eq (α := α) (U := Work.Elliptic.EllResid α g Ψ) hSmΞ hz hθ
  -- (2) `L₀` is insensitive to the layer `Ḡ·sin 2θ`
  have h2 : Work.Elliptic.Lzero (Work.Elliptic.EllResid α g Ψ) z θ
      = Work.Elliptic.Lzero (Work.FTS.EllExist.shiftSing α g Ψ) z θ := by
    rw [hdecomp, Work.FTS.EllSol.vthC_Lzero_add hSmW hGnegSm hz hθ,
      Work.Elliptic.Lzero_sin_two_mul (fun z => -(Work.Elliptic.Gbar α g z)) z θ hcos,
      add_zero]
  -- (3) the equation `bslOp α Ψ̂ = orthSource g` read as a formula for `L₀Ψ̂`
  have h3 : Work.Elliptic.Lzero (Work.FTS.EllExist.shiftSing α g Ψ) z θ
      = Work.Elliptic.orthSource g z θ
        + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllExist.shiftSing α g Ψ) z θ)
        + (α * (5 + α)) * Work.Spaces.Dz (Work.FTS.EllExist.shiftSing α g Ψ) z θ := by
    have hb := Work.FTS.EllipticEst.TT.EllWeakPos.eq hweak z hz θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp_apply] at hb
    simp only [Work.Spaces.Dz]
    linarith [hb]
  rw [h1, h2, h3]
  simp only [Work.Spaces.Dz]
  ring

end Work.FTS.ClassC
