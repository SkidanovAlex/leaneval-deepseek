import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.Dth_LGammaT_eq
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.Dth_Lhat_O

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
# `D_θ(𝓛_Γ^T f) = 𝓛̂(D_θ f) + E1 α f` — the transfer of the `D_θ`-commutator, open class

The open-class (`Work.FTS.EllipticEst.SmoothOpen`, i.e. genuine `C^∞` on the *open* quadrant
`(0,∞) × (0,π/2)`) twin of `Work.FTS.CoercivityFix.Transfer.Dth_LGammaT_eq` (whose hypothesis is
the interior class `Work.FTS.LocData.SmoothQuad`).

The route is the same three-step assembly as in the interior class:

* `D_θ(𝓛_Γ^T f) = D_θ(𝓛̂ f) + T2 α f + T4 α f` — the pointwise `θ`-expansion, proved here directly
  from `𝓛_Γ^T = 𝓛̂ + Corr` (`CoercivityFix.LGammaT_eq_Lhat_add_Corr`) and the fact that `Corr` is a
  `θ`-dependent factor `Γ(θ)` times a `θ`-independent radial profile `slotK α f z`; it is the
  open-class adaptation of `Work.FTS.CoercivityFix.Coer1T.Dth_LGammaT_eq`;
* `D_θ(𝓛̂ f) = 𝓛̂(D_θ f)` — `Work.FTS.CoercivityFix.LhatCalc.Dth_Lhat_open`, already stated for
  `SmoothOpen`;
* `T2 α f + T4 α f = E1 α f` — purely algebraic,
  `Work.FTS.CoercivityFix.Transfer.T2_add_T4_eq_E1`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TransO

theorem Dth_LGammaT_eq_O (α : ℝ) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.Dth (Work.Coercivity.LGammaT α f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ
        + Work.FTS.CoercivityFix.Transfer.E1 α f z θ := by
  have hθI : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hθ2⟩
  -- Step 1: the pointwise `θ`-expansion `D_θ(𝓛_Γ^T f) = D_θ(𝓛̂ f) + T2 + T4` on the open
  -- quadrant, from `SmoothOpen f` alone.
  have key : Work.Spaces.Dth (Work.Coercivity.LGammaT α f) z θ
      = Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
        + Work.Coercivity.T2 α f z θ + Work.Coercivity.T4 α f z θ := by
    have hslice : (fun θ' => Work.Coercivity.LGammaT α f z θ')
        = (fun θ' => Work.FTS.CoercivityFix.Lhat f z θ'
            + Work.FTS.CoercivityFix.Coer1T.slotK α f z * Work.Spaces.Gam α θ') := by
      funext θ'
      rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α f]
      simp only [Pi.add_apply, Work.FTS.CoercivityFix.Corr_eq,
        Work.FTS.CoercivityFix.Coer1T.slotK]
      rw [Work.Coercivity.C0]
      ring
    have hf_diff : DifferentiableAt ℝ (fun θ' => f z θ') θ :=
      ((hf.curry_θ hz).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
        (isOpen_Ioo.mem_nhds hθI)
    have hpz_diff : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz f z θ') θ :=
      ((hf.pz.curry_θ hz).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
        (isOpen_Ioo.mem_nhds hθI)
    have hDth_diff : DifferentiableAt ℝ (fun θ' => Work.Spaces.Dth f z θ') θ :=
      ((hf.Dth.curry_θ hz).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
        (isOpen_Ioo.mem_nhds hθI)
    have hLhat_diff : DifferentiableAt ℝ (fun θ' => Work.FTS.CoercivityFix.Lhat f z θ') θ := by
      have hfun : (fun θ' => Work.FTS.CoercivityFix.Lhat f z θ') = (fun θ' => f z θ'
          + z * Work.Spaces.pz f z θ' - (2 / (1 + z)) * f z θ'
          - (3 / (1 + z)) * Work.Spaces.Dth f z θ') := by
        funext θ'
        rw [Work.FTS.CoercivityFix.Lhat_eq]
        simp only [Work.Spaces.Dz]
        ring
      rw [hfun]
      exact ((hf_diff.add (hpz_diff.const_mul z)).sub (hf_diff.const_mul (2 / (1 + z)))).sub
        (hDth_diff.const_mul (3 / (1 + z)))
    have hG_diff : DifferentiableAt ℝ (fun θ' => Work.Spaces.Gam α θ') θ :=
      Work.Coercivity.differentiableAt_Gam α hθI
    have hderiv : deriv (fun θ' => Work.Coercivity.LGammaT α f z θ') θ
        = deriv (fun θ' => Work.FTS.CoercivityFix.Lhat f z θ') θ
          + Work.FTS.CoercivityFix.Coer1T.slotK α f z
            * deriv (fun θ' => Work.Spaces.Gam α θ') θ := by
      rw [hslice]
      have hd2 : DifferentiableAt ℝ
          (fun θ' => Work.FTS.CoercivityFix.Coer1T.slotK α f z * Work.Spaces.Gam α θ') θ :=
        hG_diff.const_mul _
      rw [show deriv (fun θ' => Work.FTS.CoercivityFix.Lhat f z θ'
            + Work.FTS.CoercivityFix.Coer1T.slotK α f z * Work.Spaces.Gam α θ') θ
          = deriv ((fun θ' => Work.FTS.CoercivityFix.Lhat f z θ')
              + fun y => Work.FTS.CoercivityFix.Coer1T.slotK α f z * Work.Spaces.Gam α y) θ from
        rfl]
      rw [deriv_add hLhat_diff hd2, deriv_const_mul_field]
    have hkey : Work.Spaces.Dth (Work.Coercivity.LGammaT α f) z θ
        = Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
          + Real.sin (2 * θ)
            * (Work.FTS.CoercivityFix.Coer1T.slotK α f z
                * deriv (fun t => Work.Spaces.Gam α t) θ) := by
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [hderiv]
      ring
    rw [hkey]
    have hT2T4 : Real.sin (2 * θ)
          * (Work.FTS.CoercivityFix.Coer1T.slotK α f z
              * deriv (fun t => Work.Spaces.Gam α t) θ)
        = Work.Coercivity.T2 α f z θ + Work.Coercivity.T4 α f z θ := by
      rw [Work.Coercivity.T2, Work.Coercivity.T4, Work.Coercivity.DthGam_eq (α := α) z θ,
        Work.FTS.CoercivityFix.Coer1T.slotK]
      ring
    rw [hT2T4]
    ring
  -- Step 2 + 3: `D_θ` commutes with `𝓛̂`, and `T2 + T4 = E1`.
  have hcomm := Work.FTS.CoercivityFix.LhatCalc.Dth_Lhat_open (f := f) hf hz hθ hθ2
  have hT24 := Work.FTS.CoercivityFix.Transfer.T2_add_T4_eq_E1 α f z θ
  rw [key, hcomm]
  linarith [hT24]

end Work.FTS.StrongEps.EpsE4Thr.TransO
