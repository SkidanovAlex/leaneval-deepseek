import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.FTS_RegExport.RXR1.classC_sub_hyp
import Submission.Work.FTS_RegExport.RXT.Slots.v2_theta_sup_uniform
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_RegExport.RXT.st1_stdata
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS_RegExport.RXT.SlotJetsTendsto =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT


end Work.FTS_RegExport.RXT
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.Standing =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12FKaux.Standing` — the standing bounds for the limit family and its approximants

For a family `g` with `LimApprox β C₀ Φs E g` (and `β = pExp α`), the approximating families
`gn` of the clause are class-`C` with uniformly bounded `ℋ⁴`-norm and `ℋ⁴`-Lipschitz in the fake
time.  Feeding those three facts into the interior weighted `L^∞`–`ℋ⁴` trade-off
(`RXA1w.abs_mixed_le_HkNorm_C4_w_proved`) gives the weighted slot bounds
`|D_z^bD_θ^a (slice (gn n) τ)| ≤ C · z^{3/2}/(1+z)²` and the weighted τ-modulus
`|D_z^bD_θ^a(slice (gn n) τ) − D_z^bD_θ^a(slice (gn n) τ')| ≤ C·z^{3/2}/(1+z)²·|τ−τ'|`
for `a + b ≤ 2`, which are the hypotheses of the `L₁₂`-calculus of `RXT.L12Iter`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- The radial weight `z^{3/2}/(1+z)²` of the standing bound. -/
abbrev SW (z : ℝ) : ℝ := z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2

theorem SW_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ SW z :=
  Work.FTS_RegExport.RXT.L12Iter.Rwt_nonneg hz





/-- `|K(θ)| ≤ 3`. -/
theorem abs_K_le_three (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 :=
  Work.FTS_RegExport.RXT.L12Iter.abs_Ktheta_le_three θ

end Work.FTS_RegExport.RXT.Sys.L12FKaux
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT0.SJC.slotJetContinuousOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT0.SJC

open scoped Real Topology
open Set Filter
set_option autoImplicit false
variable {α : ℝ}

theorem slotJetContinuousOn {X : ℝ → ℝ → ℝ} {α : ℝ}
    (hX : ContDiffOn ℝ 3 (Function.uncurry X) Work.FTS.EllipticEst.Q0)
    (j i : ℕ) (hji : j + i ≤ 2) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i
        (fun z θ => Work.Construction.Vop X z θ) p.1 p.2) Work.FTS.EllipticEst.Q0 ∧
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i
        (fun z θ => Work.Construction.Rop α X z θ) p.1 p.2) Work.FTS.EllipticEst.Q0 ∧
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i
        (fun z θ => Work.Construction.Uop α X z θ / Real.sin (2 * θ)) p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
  -- `j + i ≤ 2` in the order matching `continuousOn_mixed_of_contDiffOn`
  have hji' : i + j ≤ 2 := by omega
  -- the three slot functions are `C²` on the open quadrant `Q0`: `Q0` is open, so the
  -- plain derivative lowers the order by one, `tan` and `1/cos`, `1/sin(2·)` are smooth
  -- there, and the coefficients `Uop, Vop, Rop` are *linear* in `Ψ, ∂_zΨ, ∂_θΨ`.
  have hV := Work.FTS_RegExport.RXT.contDiffOn_uncurry_Vop hX
  have hR := Work.FTS_RegExport.RXT.contDiffOn_uncurry_Rop (α := α) hX
  have hU := Work.FTS_RegExport.RXT.contDiffOn_uncurry_div_sin_two
    (Work.FTS_RegExport.RXT.contDiffOn_uncurry_Uop (α := α) hX)
  -- a mixed slot `D_z^jD_θ^i` of a `C²` function on the open quadrant is continuous there
  exact ⟨Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn hV hji',
    Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn hR hji',
    Work.FTS.StrongEps.continuousOn_mixed_of_contDiffOn hU hji'⟩

end Work.FTS_RegExport.RXT0.SJC
end
