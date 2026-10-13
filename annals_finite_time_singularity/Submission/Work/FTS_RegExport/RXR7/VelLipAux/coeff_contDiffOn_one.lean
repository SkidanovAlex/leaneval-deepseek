import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS_RegExport.RXT.C2Assemble
import Submission.Work.FTS_RegExport.RXT.C2Final

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXR7.VelLipAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The order-one elementary calculus on the open quadrant

These are the order-one counterparts of the `C²`-calculus lemmas of
`Work.FTS_RegExport.RXT.C2Assemble` (whose inputs are `C³` stream functions): the partial
derivatives lose exactly one order and `tan` is `C¹` on the open quadrant. -/

/-- `∂_z` on the open quadrant lowers the differentiability order by one. -/
theorem contDiffOn_uncurry_pz_one {G : ℝ → ℝ → ℝ}
    (hG : ContDiffOn ℝ 2 (Function.uncurry G) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz G)) Work.FTS.EllipticEst.Q0 :=
  Work.FTS.StrongEps.contDiffOn_uncurry_pz_fin Work.FTS.EllipticEst.isOpen_Q0 hG

/-- `∂_θ` on the open quadrant lowers the differentiability order by one. -/
theorem contDiffOn_uncurry_pth_one {G : ℝ → ℝ → ℝ}
    (hG : ContDiffOn ℝ 2 (Function.uncurry G) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth G)) Work.FTS.EllipticEst.Q0 :=
  Work.FTS.StrongEps.contDiffOn_uncurry_pth_fin Work.FTS.EllipticEst.isOpen_Q0 hG

/-- `tan θ` is `C¹` on the open quadrant. -/
theorem contDiffOn_one_tan_Q0 :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => Real.tan p.2) Work.FTS.EllipticEst.Q0 :=
  Work.FTS_RegExport.RXT.contDiffOn_tan_Q0.of_le (by norm_num)

/-- `Uop α Ψ = -3Ψ - α z ∂_zΨ` is `C¹` on the open quadrant for a `C²` stream function. -/
theorem contDiffOn_uncurry_Uop_one {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Construction.Uop α Ψ))
      Work.FTS.EllipticEst.Q0 := by
  have hpz : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz Ψ))
      Work.FTS.EllipticEst.Q0 := contDiffOn_uncurry_pz_one hΨ
  have h1 : ContDiffOn ℝ 1 (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0 :=
    hΨ.of_le (by norm_num)
  have h2 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => α * p.1 * Work.Spaces.pz Ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    ((contDiffOn_const (c := α)).mul contDiffOn_fst).mul hpz
  refine (((contDiffOn_const (c := (-3 : ℝ))).mul h1).sub h2).congr ?_
  intro p _
  simp only [Function.uncurry, Work.Construction.Uop]

/-- `Vop Ψ = ∂_θΨ - tan θ · Ψ` is `C¹` on the open quadrant for a `C²` stream function. -/
theorem contDiffOn_uncurry_Vop_one {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 1 (Function.uncurry (Work.Construction.Vop Ψ))
      Work.FTS.EllipticEst.Q0 := by
  have hpth : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth Ψ))
      Work.FTS.EllipticEst.Q0 := contDiffOn_uncurry_pth_one hΨ
  have h1 : ContDiffOn ℝ 1 (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0 :=
    hΨ.of_le (by norm_num)
  exact hpth.sub (contDiffOn_one_tan_Q0.mul h1)

/-- `sin (2θ)` is `C¹` on the open quadrant. -/
theorem contDiffOn_one_sin_two_Q0 :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
  (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn

/-- **`C¹`-regularity of the two R7 coefficient slices.**  From the `C²`-regularity of the
stream-function slice `slice Φ τ` on the open quadrant and the `C²`-regularity of the radial
profile `L₁₂(Ftau αG G τ)` on `(0,∞)`, the two transport coefficients `Vz7 αG μ G Φ · · τ` and
`Vθ7 αG Φ · · τ / sin(2θ)` are `C¹` (jointly in `(z,θ)`) on the open quadrant `Q0`.

Route: this is the order-1 shadow of the already-proved
`Work.FTS_RegExport.RXT.coeff_C2_assembly` (which is the order-2 statement and needs a `C³`
stream function). Unfold `Vz7 = (1 - μ τ) + L12(Ftau αG G τ)·c2m + 2αG·Vop Φ̃` with
`Φ̃ = PhiTil αG (Ftau αG G τ) (slice Φ τ)` and `Vθ7/sin 2θ = 2·Uop αG (slice Φ τ)/sin 2θ`:
* `Theta αG (Ftau αG G τ) = (1/(4αG))·sin(2θ)·L₁₂(Ftau αG G τ)(z)` is `C²` on `Q0` (product of a
  smooth `θ`-factor with the `C²` radial function `hL12`, pulled back along `fst`), so
  `Φ̃ = slice Φ τ − Theta` is `C²` there;
* `pth Φ̃` is therefore `C¹`, and `Vop Φ̃ = pth Φ̃ − tan θ · Φ̃` is `C¹`
  (`Work.FTS_RegExport.RXT.contDiffOn_tan_Q0`, and order-reduction lemmas such as
  `Work.FTS.StrongEps.contDiffOn_uncurry_pth_fin`,
  `Work.FTS.StrongEps.contDiffOn_uncurry_pz_fin` — see `RXT/C2Assemble.lean`);
* `L₁₂(F)(z)·c2m θ` is `C¹` (indeed `C²`) since `L₁₂` is `C²` on `(0,∞)` and `c2m` is
  `C²` (`RXT.contDiffOn_c2m`);
* `Uop αG (slice Φ τ) = −3·slice Φ τ − αG·z·pz(slice Φ τ)` is `C¹` from `hΦ2` (the `z`-partial
  loses exactly one order), and division by `sin(2θ)` is legitimate on `Q0`
  (`RXT.sin_two_pos_Q0`).

The `αG ≠ 0` hypothesis is needed only for the constant `1/(4αG)` in `Theta`. -/
theorem coeff_contDiffOn_one {αG : ℝ} {μ : ℝ → ℝ}
    {G Φ : Work.FTS.Galerkin.Fam} {τ : ℝ} (hαG : αG ≠ 0)
    (hΦ2 : ContDiffOn ℝ 2 (Function.uncurry (Work.FTS.Galerkin.slice Φ τ))
      Work.FTS.EllipticEst.Q0)
    (hL12 : ContDiffOn ℝ 2
      (Work.Construction.L12 (Work.Construction.Ftau αG G τ)) (Set.Ioi 0)) :
    ContDiffOn ℝ 1 (Function.uncurry (fun z θ =>
        Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ)) Work.FTS.EllipticEst.Q0 ∧
    ContDiffOn ℝ 1 (Function.uncurry (fun z θ =>
        Work.FTS.RegExportIface.Vθ7 αG Φ z θ τ / Real.sin (2 * θ)))
      Work.FTS.EllipticEst.Q0 := by
  have hc2m : ContDiffOn ℝ 1 Work.Construction.c2m (Set.Ioo 0 (π / 2)) :=
    Work.FTS_RegExport.RXT.contDiffOn_c2m.of_le (by norm_num)
  -- `Θ` is `C²` on the open quadrant
  have hsin2 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (1 / (4 * αG)) * Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    contDiffOn_const.mul
      ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn)
  have hL12fst : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      Work.Construction.L12 (Work.Construction.Ftau αG G τ) p.1)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS_RegExport.RXT.contDiffOn_slice_fst hL12
  have hTheta : ContDiffOn ℝ 2
      (Function.uncurry (Work.Construction.Theta αG (Work.Construction.Ftau αG G τ)))
      Work.FTS.EllipticEst.Q0 := by
    refine (hsin2.mul hL12fst).congr ?_
    intro p _
    simp only [Function.uncurry, Work.Construction.Theta, Work.Construction.s2]
  -- `Φ̃ = Φ - Θ` is `C²` on the open quadrant
  have hPsi : ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.PhiTil αG
      (Work.Construction.Ftau αG G τ) (Work.FTS.Galerkin.slice Φ τ)))
      Work.FTS.EllipticEst.Q0 := hΦ2.sub hTheta
  have hVop : ContDiffOn ℝ 1 (Function.uncurry (Work.Construction.Vop
      (Work.Construction.PhiTil αG (Work.Construction.Ftau αG G τ)
        (Work.FTS.Galerkin.slice Φ τ)))) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_Vop_one hPsi
  have hUop : ContDiffOn ℝ 1 (Function.uncurry (Work.Construction.Uop αG
      (Work.FTS.Galerkin.slice Φ τ))) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_Uop_one hΦ2
  refine ⟨?_, ?_⟩
  · -- `Vz7`
    have hLmul : ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
        Work.Construction.L12 (Work.Construction.Ftau αG G τ) p.1
          * Work.Construction.c2m p.2) Work.FTS.EllipticEst.Q0 :=
      (Work.FTS_RegExport.RXT.contDiffOn_slice_fst
        (hL12.of_le (by norm_num))).mul
        (hc2m.comp contDiffOn_snd (fun p hp => hp.2))
    have hV : ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
        (2 * αG) * Work.Construction.Vop (Work.Construction.PhiTil αG
          (Work.Construction.Ftau αG G τ) (Work.FTS.Galerkin.slice Φ τ)) p.1 p.2)
        Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const.mul hVop
    refine (((contDiffOn_const (c := 1 - μ τ)).add hLmul).add hV).congr ?_
    intro p _
    simp only [Function.uncurry, Work.FTS.RegExportIface.Vz7,
      Work.FTS.RegExportIface.phiTil]
  · -- `Vθ7 / sin (2θ)`
    refine (((contDiffOn_const (c := (2 : ℝ))).mul hUop).div contDiffOn_one_sin_two_Q0
      (fun p hp => ne_of_gt (Work.FTS_RegExport.RXT.sin_two_pos_Q0 hp))).congr ?_
    intro p _
    simp only [Pi.div_apply, Function.uncurry, Work.FTS.RegExportIface.Vθ7]

end Work.FTS_RegExport.RXR7.VelLipAux
