import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_RegExport.RXT.MixedUniform
import Submission.Work.FTS_RegExport.RXT.C2Assemble
import Submission.Work.FTS_RegExport.RXT.C2Psi
import Submission.Work.FTS_RegExport.RXT.C2Final
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.contDiffOn_two_integral_Itheta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.coeff_C2` — S4: spatial `C²` of the coefficient slices

The three transport coefficients `VR`, `bR`, `cR` of `(E)` are jointly `C²` in `(z,θ)` on the
open quadrant `Q0`, for every `τ ≥ 0`.  The inputs are

* `psiCan_C3` (the stream function is `C³`, `C2Psi.contDiffOn_slice_PhiR_Q0`);
* `LimApprox` + the class-`C` interior trade-off (`MixedUniform.mixed_uniform`), which give
  uniform bounds for `F(τ) = F_* + g(τ)` and its `D_z`-derivatives (`Ftau_bounds`);
* the parametric-integral lemma `contDiffOn_two_integral_Itheta` (`𝔽K(F(τ))` is `C²`) and
  the primitive lemma `contDiffOn_succ_integral_Ioi` (`L₁₂(F(τ))` is `C³`, `C2Radial`).

The assembly is `C2Final.coeff_C2_assembly`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.RegExportIface.RXT (GR ΦR μR VR bR cR)

set_option autoImplicit false

theorem continuousOn_K_Iθ : ContinuousOn Work.Spaces.K Work.Spaces.Iθ :=
  ((continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)).continuousOn

theorem coeff_C2 {α C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ τ : ℝ, 0 ≤ τ →
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
          Work.FTS.RegExportIface.RXT.VR α Φs E g z θ τ)) Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
          Work.FTS.RegExportIface.RXT.bR α Φs E g z θ τ)) Work.FTS.EllipticEst.Q0 ∧
      ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
          Work.FTS.RegExportIface.RXT.cR α Φs E g z θ τ)) Work.FTS.EllipticEst.Q0 := by
  intro τ hτ
  have hαG : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαGne : Work.FTS.Regularity.pExp α ≠ 0 := ne_of_gt hαG
  have hΦ3 := contDiffOn_slice_PhiR_Q0 (α := α) hEL3 hStar hOK τ hτ
  have hF2 := contDiffOn_Ftau_Q0 (C₀ := C₀) hα hα13 hOK τ hτ
  obtain ⟨C, hC0, hbd⟩ := Ftau_bounds (C₀ := C₀) hα hα13 hOK τ hτ
  have hFK2 : ContDiffOn ℝ 2
      (Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ))
      (Set.Ioi 0) :=
    contDiffOn_two_integral_Itheta (φ := Work.Spaces.K) continuousOn_K_Iθ hF2 hbd
  have hL12 : ContDiffOn ℝ 3
      (Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ))
      (Set.Ioi 0) := contDiffOn_three_L12 hFK2
  exact coeff_C2_assembly (α := α) (αG := Work.FTS.Regularity.pExp α) (C₀ := C₀) (Cs := Cs)
    hαGne hΦ3 hFK2 hL12

end Work.FTS_RegExport.RXT
