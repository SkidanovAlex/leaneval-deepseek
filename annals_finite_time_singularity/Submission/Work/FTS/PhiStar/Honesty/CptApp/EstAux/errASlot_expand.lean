import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The binomial expansion of the `z`-derivative of the `(χζ − 1)`-slot

`D_z = z ∂_z` is a derivation, hence its iterates satisfy the binomial (Leibniz) rule

`D_z^i (f · g) = ∑_{b ≤ i} C(i,b) · (D_z^b f · D_z^{i-b} g)`

as soon as both factors are `C^∞` on the open quadrant `(0,∞) × (0,π/2)`.  This file applies
the rule to the slot function `f = (χ_n(z) ζ_n(θ) − 1)` and to the datum `g = F`, which is
the binomial expansion consumed downstream by `errASlot_le` (`EstAux/errASlot_le.lean`).

The Leibniz rule itself is `Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz`, i.e. the version
stated in the open-quadrant class `Work.FTS.EllipticEst.SmoothOpen` (the class in which the
statement's hypothesis on `F` lives — the `C^∞`-order variant
`Work.FTS.LocData.DzIter_mul_smoothQuad` asks for smoothness on the *larger* set `(-1,∞)`,
which `SmoothOpen` does not provide).  Here the factor `χ_n(z) ζ_n(θ) − 1` is `C^∞` on the
whole plane (`Work.FTS.PhiStar.Honesty.CptApp.contDiff_chiR`, `…contDiff_zetaR`), and `F` is
`SmoothOpen` by hypothesis.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp.EstAux

theorem errASlot_expand {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (n i : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter i (fun z θ => (Work.FTS.PhiStar.Honesty.CptApp.chiR n z
        * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) * F z θ) z θ
      = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
          * (Work.Spaces.DzIter b (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
            * Work.Spaces.DzIter (i - b) F z θ) := by
  have hG : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
        * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) := by
    refine (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr fun m => ?_
    exact ((Work.FTS.PhiStar.Honesty.CptApp.contDiff_chiR n m).contDiffOn.comp
        contDiffOn_fst (fun p _ => Set.mem_univ p.1)).mul
        ((Work.FTS.PhiStar.Honesty.CptApp.contDiff_zetaR n m).contDiffOn.comp contDiffOn_snd
          (fun p _ => Set.mem_univ p.2)) |>.sub contDiffOn_const
  exact Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz i _ F hG hsm z θ hz hθ.1 hθ.2

end Work.FTS.PhiStar.Honesty.CptApp.EstAux
