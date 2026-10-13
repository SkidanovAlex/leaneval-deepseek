import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_StreamBdry.SB1.Engine
import Submission.Work.FTS_StreamBdry.SB3.psiP_DzLe
import Submission.Work.FTS.ClassC.RopGen.Transfer
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.GalBasis.GalApprox.poly2_aux1
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

/-- **The second `z`-derivative of the shifted singular unknown, split off from `PhiTil`.**
`shiftSing α g Ψ = PhiTil α g Ψ + Gbar α g · sin 2θ` on the open quadrant (`Gbar` is the `z`-only
`Elliptic.Gbar`).  Hence at `z = 1` the `θ`-only factor pulls out of `pzIter 2 = ∂_z²`:
`∂_z²(shiftSing) = ∂_z²(PhiTil) + (Gbar)''(1) · sin 2θ`.
Route: the function identity `Construction.PhiTil α g Ψ = shiftSing α g Ψ - Gbar α g · sin 2θ`
(unfold `PhiTil`, `Theta`, `Gsing`, `Gstar`; note `Work.Elliptic.EllResid = Construction.PhiTil`
definitionally, and there may already be a proved identity such as `ellResid_eq_shiftSing_add`),
then rewriting `pzIter` on the open set and `GalBasis.GalApprox.pzIter_add`
(needs `ContDiffAt ℝ 2` of both `z`-slices at `1`, from `SmoothOpen` resp. `ContDiffOn ℝ 2` at
`1 ∈ Ioi 0`), finally `H2.STFacts.pzIter_const_mul` with the `θ`-only factor `c θ = sin 2θ`
(after commuting the product) and two `deriv_const_mul`-style steps.  Consumed by
`Work.FTS_EllLimOK.ProducerH.kappa_eq_zero`. -/
theorem pzIterTwo_shiftSing_eq_PhiTil_add {α : ℝ} {g Ψ : ℝ → ℝ → ℝ}
    (hΦ : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.PhiTil α g Ψ))
    (hG : ContDiffOn ℝ 2 (Work.Elliptic.Gbar α g) (Set.Ioi 0))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pzIter 2 (Work.FTS.EllExist.shiftSing α g Ψ) 1 θ
      = Work.Spaces.pzIter 2 (Work.Construction.PhiTil α g Ψ) 1 θ
        + (deriv (fun z => deriv (Work.Elliptic.Gbar α g) z) 1) * Real.sin (2 * θ) := by
  -- `shiftSing α g Ψ = PhiTil α g Ψ + Gbar α g · sin 2θ`, by unfolding the four definitions
  -- (`Elliptic.L12` and `Construction.L12` are definitionally equal).
  have hid : Work.FTS.EllExist.shiftSing α g Ψ
      = fun z θ => Work.Construction.PhiTil α g Ψ z θ
        + Work.Elliptic.Gbar α g z * Real.sin (2 * θ) := by
    funext z θ
    have hL : Work.Elliptic.L12 g z = Work.Construction.L12 g z := rfl
    simp only [Work.FTS.EllExist.shiftSing_apply, Work.Construction.PhiTil,
      Work.Construction.Theta, Work.Construction.s2, Work.Elliptic.Gsing,
      Work.Elliptic.Gstar, hL]
    ring
  rw [hid]
  -- the two `z`-slices are `C²` at `z = 1`: `PhiTil` from `SmoothOpen` on the open quadrant,
  -- `Gbar · sin 2θ` from `ContDiffOn` at `1 ∈ Ioi 0` and a constant `θ`-factor.
  have hsliceA : ContDiffAt ℝ 2 (fun z' => Work.Construction.PhiTil α g Ψ z' θ) 1 := by
    have hQ0 : (1, θ) ∈ Work.FTS.EllipticEst.Q0 := by
      rw [Work.FTS.EllipticEst.mem_Q0]
      exact ⟨by norm_num, hθ.1, hθ.2⟩
    have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Construction.PhiTil α g Ψ)) (1, θ) :=
      (hΦ.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hQ0)
    have hlin : ContDiffAt ℝ 2 (fun z' : ℝ => (z', θ)) (1 : ℝ) := by fun_prop
    have hcomp := hcd.comp (1 : ℝ) hlin
    simpa only [Function.comp_def, Function.uncurry] using hcomp
  have hsliceB : ContDiffAt ℝ 2 (fun z' => Work.Elliptic.Gbar α g z' * Real.sin (2 * θ)) 1 := by
    have h1 : ContDiffAt ℝ 2 (Work.Elliptic.Gbar α g) 1 :=
      hG.contDiffAt (isOpen_Ioi.mem_nhds (by norm_num : (1 : ℝ) ∈ Set.Ioi 0))
    exact h1.mul contDiffAt_const
  rw [Work.FTS.GalBasis.GalApprox.pzIter_add (i := 2)
    (X := Work.Construction.PhiTil α g Ψ)
    (Y := fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) (z := 1) (θ := θ)
    hsliceA hsliceB]
  -- the `θ`-only factor pulls out of `∂_z²`
  have hB : Work.Spaces.pzIter 2 (fun z θ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ)) 1 θ
      = (deriv (fun z => deriv (Work.Elliptic.Gbar α g) z) 1) * Real.sin (2 * θ) := by
    have hGB : Work.Spaces.pzIter 2 (fun z θ => Work.Elliptic.Gbar α g z) 1 θ
        = deriv (fun z => deriv (Work.Elliptic.Gbar α g) z) 1 := rfl
    rw [show (fun z θ : ℝ => Work.Elliptic.Gbar α g z * Real.sin (2 * θ))
        = (fun z θ => Real.sin (2 * θ) * Work.Elliptic.Gbar α g z) from by
          funext z θ; ring]
    rw [Work.FTS.H2.pzIter_const_mul (fun θ => Real.sin (2 * θ))
      (fun z _ => Work.Elliptic.Gbar α g z) 2 1 θ]
    rw [hGB]
    ring
  rw [hB]

end Work.FTS_EllLimOK.ProducerH
