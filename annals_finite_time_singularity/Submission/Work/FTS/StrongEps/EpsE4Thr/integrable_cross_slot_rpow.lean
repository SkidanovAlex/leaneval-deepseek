import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc
import Submission.Work.FTS.StrongEps.EpsE4Thr.JepsJoint.Jeps_fam_continuous
import Submission.Work.FTS.StrongEps.EpsE4Thr.SlotWt.mixedSlot_weight_le_HkIntegrand4
import Submission.Work.FTS.StrongEps.EpsE4Thr.WipEqIntegral
import Submission.Work.FTS.StrongEps.EpsE4Thr.integrable_wip_slot_cross
import Submission.Work.FTS.StrongEps.Jeps_contDiffOn
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.R1G.DecayInZ_gA
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.AesmJfamP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## Linearity of `mixed` under a constant multiple

(The unconditional version: `deriv_const_mul_field` is `deriv (fun y => u * v y) x = u * deriv v x`
for any `v : ℝ → ℝ`, no differentiability hypothesis needed.) -/

private theorem DthIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Work.Spaces.DthIter i (fun z θ : ℝ => c * f z θ)
      = fun z θ : ℝ => c * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth, deriv_const_mul_field]
      ring

private theorem DzIter_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ : ℝ => c * f z θ)
      = fun z θ : ℝ => c * Work.Spaces.DzIter j f z θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      simp only [Work.Spaces.Dz, Work.Spaces.pz, deriv_const_mul_field]
      ring

private theorem mixed_const_mul (c : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z θ : ℝ => c * f z θ)
      = fun z θ : ℝ => c * Work.Spaces.mixed j i f z θ := by
  rw [Work.Spaces.mixed, DthIter_const_mul c f i]
  exact DzIter_const_mul c (Work.Spaces.DthIter i f) j

/-! ## The `Pz`-correction of a slot -/

/-- **A mixed slot of the projection `Pz w = w − (L₁₂ w 0 / pzNorm) • bump`.**  Both `w` and
`bump` are smooth on the open quadrant, so the sum splits
(`Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn` + the constant-multiple rule). -/
theorem mixed_Pz_eq {a b n : ℕ} {w : ℝ → ℝ → ℝ}
    (hw : ContDiffOn ℝ n (Function.uncurry w) Work.FTS.StrongEps.Quad) (hab : a + b ≤ n)
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.StrongEps.Quad) :
    Work.Spaces.mixed a b (Pz w) z θ
      = Work.Spaces.mixed a b w z θ
        - (Work.Construction.L12 w 0 / pzNorm) * Work.Spaces.mixed a b bump z θ := by
  have hbump : ContDiffOn ℝ n (Function.uncurry (fun z θ : ℝ => bump z θ))
      Work.FTS.StrongEps.Quad := by
    have hfun : Function.uncurry (fun z θ : ℝ => bump z θ)
        = fun p : ℝ × ℝ => bump p.1 p.2 := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact (Work.FTS.StrongEps.contDiff_bump n).contDiffOn
  have hsplit : ContDiffOn ℝ n
      (Function.uncurry (fun z θ : ℝ => -(Work.Construction.L12 w 0 / pzNorm) * bump z θ))
      Work.FTS.StrongEps.Quad := by
    have hfun : Function.uncurry
        (fun z θ : ℝ => -(Work.Construction.L12 w 0 / pzNorm) * bump z θ)
        = fun p : ℝ × ℝ => -(Work.Construction.L12 w 0 / pzNorm) * bump p.1 p.2 := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [hfun]
    exact contDiffOn_const.mul hbump
  have hfun : Pz w = w + fun z θ : ℝ => -(Work.Construction.L12 w 0 / pzNorm) * bump z θ := by
    funext z θ
    rw [Pz_apply]
    simp only [Pi.add_apply]
    ring
  rw [hfun]
  rw [Work.FTS.CoercivityFix.Transfer.E2pkg.mixed_add_of_contDiffOn
    (V := Work.FTS.StrongEps.Quad) Work.FTS.StrongEps.isOpen_Quad hw hsplit b a (by omega)
    (z, θ) hzθ, mixed_const_mul]
  simp only [Prod.fst, Prod.snd]
  ring

/-! ## The joint a.e. strong measurability of the `J_ε`-mollified slots -/


/-! ## The projected slot -/


/-! ## The same for the scheme's right-hand side `xdot = Pz (J_ε (epsRHSP …))` -/


/-! ## Consequence of the joint smoothness of the flow on the closed slab -/



end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.SlotHkGen.integral_slot_sq_rpow_le_HkSq_gen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.SlotHkGen

set_option autoImplicit false

/-! ## A single pure `D_z`-slot of the strong weight, in `ℋ^k` -/


/-! ## A single mixed slot of the strong weight, in `ℋ^k` -/


/-! ## The target -/


end Work.FTS.StrongEps.EpsE4Thr.SlotHkGen
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.SlotL2LeHkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false


end Work.FTS.StrongEps.EpsE4Thr
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.integrable_cross_slot_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false



end Work.FTS.StrongEps.EpsE4Thr
end
