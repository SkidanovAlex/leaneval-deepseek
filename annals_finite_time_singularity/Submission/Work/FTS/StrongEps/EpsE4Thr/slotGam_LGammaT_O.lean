import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgO
import Submission.Work.FTS.CoercivityFix.Coer1T.slotGam_LGammaT
import Submission.Work.FTS.StrongEps.EpsE4Thr.wip_transport_le_O
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.Dth_Lhat_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.est_D_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.wip_T2_ge_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.wip_T4_ge_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.intDth_Lhat_gam_O

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
# `slotGam_LGammaT_O` — the `D_θ`-slot of the level-one coercivity of `𝓛_Γ^T`, **open class**

The open-class (`CoerAdmO`, i.e. `SmoothOpen` instead of `SmoothQuad`) twin of
`Work.FTS.CoercivityFix.Coer1T.slotGam_LGammaT`.  The proof is the frozen one with the three
analytic inputs replaced by their open-class ports:

* `Dth_LGammaT_eq_O` (below) — the pointwise expansion `D_θ(𝓛_Γ^T f) = D_θ(𝓛̂f) + T2 + T4` on the
  open quadrant, from `SmoothOpen f` alone;
* `OClass.est_D_O` — the coercivity of the clean operator on the `γ`-slot;
* `OClass.wip_T2_ge_O`, `OClass.wip_T4_ge_O` — the two `D_θΓ`-terms;
* `OClass.intDth_Lhat_gam_O` — the integrability of the clean pairing.
-/

namespace Work.FTS.StrongEps.EpsE4Thr

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The pointwise expansion of `D_θ(𝓛_Γ^T f)` on the open quadrant, in the open class
`SmoothOpen`.**  This is the open-class twin of
`Work.FTS.CoercivityFix.Coer1T.Dth_LGammaT_eq` (whose hypothesis is `SmoothQuad f`); the coercive
part is again written with the clean operator `𝓛̂`, which is what `D_θ` commutes with. -/
theorem Dth_LGammaT_eq_O (α : ℝ) {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.Dth (Work.Coercivity.LGammaT α f) z θ
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
      (isOpen_Ioo.mem_nhds hθ)
  have hpz_diff : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz f z θ') θ :=
    ((hf.pz.curry_θ hz).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  have hDth_diff : DifferentiableAt ℝ (fun θ' => Work.Spaces.Dth f z θ') θ :=
    ((hf.Dth.curry_θ hz).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
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
    Work.Coercivity.differentiableAt_Gam α hθ
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
  have key : Work.Spaces.Dth (Work.Coercivity.LGammaT α f) z θ
      = Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
        + Real.sin (2 * θ)
          * (Work.FTS.CoercivityFix.Coer1T.slotK α f z
              * deriv (fun t => Work.Spaces.Gam α t) θ) := by
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    rw [hderiv]
    ring
  rw [key]
  have hT2T4 : Real.sin (2 * θ)
        * (Work.FTS.CoercivityFix.Coer1T.slotK α f z
            * deriv (fun t => Work.Spaces.Gam α t) θ)
      = Work.Coercivity.T2 α f z θ + Work.Coercivity.T4 α f z θ := by
    rw [Work.Coercivity.T2, Work.Coercivity.T4, Work.Coercivity.DthGam_eq (α := α) z θ,
      Work.FTS.CoercivityFix.Coer1T.slotK]
    ring
  rw [hT2T4]
  ring

/-- **The `D_θ`-slot of the level-one coercivity of `𝓛_Γ^T` in the open class.**

The open-class twin of `Work.FTS.CoercivityFix.Coer1T.slotGam_LGammaT`: the same estimate with
`CoerAdm` replaced by `CoerAdmO` (i.e. `SmoothOpen` in place of `SmoothQuad`, the class that the
route's projected slices actually satisfy) and the analytic inputs supplied by
`OClass.est_D_O`, `OClass.wip_T2_ge_O`, `OClass.wip_T4_ge_O`, `OClass.intDth_Lhat_gam_O`. -/
theorem slotGam_LGammaT_O {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14)
    {f : Work.FTS.Galerkin.Fn} (hf : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f)
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f)
    (hHH : Work.Coercivity.HardyHyp f) (hG2 : Work.Coercivity.GammaPointwiseBnd α) :
    (17 / 40 - 1 / 100) * Work.Coercivity.EDth α f - (1 / 10 ^ 6) * Work.Coercivity.Ef f
      ≤ Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dth f) := by
  have hα4 : α ≤ 1 / 4 := by linarith
  have hα1' : α ≤ 1 := by linarith
  have hα9 : α ≤ 1 / 10 ^ 9 := by linarith
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hf.1.1
  have hf2 : Work.FTS.StrongEps.EpsE4Thr.RegQo α 2 f :=
    Work.FTS.StrongEps.EpsE4Thr.regQo_mono (by norm_num) hf.1
  -- the three open-class analytic inputs
  have hT2b := Work.FTS.StrongEps.EpsE4Thr.OClass.wip_T2_ge_O α hα hα1' hf2 hHH hG2
  have hT4b := Work.FTS.StrongEps.EpsE4Thr.OClass.wip_T4_ge_O α hα hα9 hf2 hIP hG2
  have hLint := Work.FTS.StrongEps.EpsE4Thr.OClass.intDth_Lhat_gam_O α hα hα1' hf2 hIP
  have hD := Work.FTS.StrongEps.EpsE4Thr.OClass.est_D_O α hα hα4 hf2 hIP
  -- the a.e. pointwise expansion of the `D_θ`-derivative
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Dth (Work.Coercivity.LGammaT α f) z θ
        = Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
          + Work.Coercivity.T2 α f z θ + Work.Coercivity.T4 α f z θ := by
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iz_pos] with z hz
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo] with θ hθ
    exact Dth_LGammaT_eq_O α hso hz hθ
  -- integrability of the two-term sum `D_θ𝓛̂ f + T2 f`
  have hA2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
          + Work.Coercivity.T2 α f z θ) * Work.Spaces.Dth f z θ
        * Work.Coercivity.thetaW α z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have h := hLint.add hT2b.1
    refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p _ => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Pi.add_apply]
    ring
  -- the split of the pairing into its three summands
  have hsplit : Work.Coercivity.wip (Work.Coercivity.thetaW α)
        (fun z θ => Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
          + Work.Coercivity.T2 α f z θ + Work.Coercivity.T4 α f z θ) (Work.Spaces.Dth f)
      = Work.Coercivity.wip (Work.Coercivity.thetaW α)
          (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dth f)
        + Work.Coercivity.wip (Work.Coercivity.thetaW α)
            (Work.Coercivity.T2 α f) (Work.Spaces.Dth f)
        + Work.Coercivity.wip (Work.Coercivity.thetaW α)
            (Work.Coercivity.T4 α f) (Work.Spaces.Dth f) := by
    rw [Work.Coercivity.wip_add_left (g := fun z θ =>
          Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ + Work.Coercivity.T2 α f z θ)
        (h := Work.Coercivity.T4 α f) (k := Work.Spaces.Dth f) hA2 hT4b.1,
      Work.Coercivity.wip_add_left (g := Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f))
        (h := Work.Coercivity.T2 α f) (k := Work.Spaces.Dth f) hLint hT2b.1]
  -- the two energies are nonnegative
  have hEfnn : 0 ≤ Work.Coercivity.Ef f := by
    rw [Work.Coercivity.Ef, Work.Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  -- the smallness of `3.2·10⁷ α`
  have hαb : (32000000 : ℝ) * α ≤ 1 / 10 ^ 6 := by
    have h1 : (32000000 : ℝ) * (1 / 10 ^ 14) = 32 / 10 ^ 8 := by norm_num
    calc (32000000 : ℝ) * α ≤ 32000000 * (1 / 10 ^ 14) :=
          mul_le_mul_of_nonneg_left hα1 (by norm_num)
      _ = 32 / 10 ^ 8 := h1
      _ ≤ 1 / 10 ^ 6 := by norm_num
  have hsmall : 32000000 * α * Work.Coercivity.Ef f
      ≤ (1 / 10 ^ 6) * Work.Coercivity.Ef f :=
    mul_le_mul_of_nonneg_right hαb hEfnn
  change (17 / 40 - 1 / 100) * Work.Coercivity.EDth α f
      - (1 / 10 ^ 6) * Work.Coercivity.Ef f
    ≤ Work.Coercivity.wip (Work.Coercivity.thetaW α)
        (Work.Spaces.Dth (Work.Coercivity.LGammaT α f)) (Work.Spaces.Dth f)
  rw [Work.Coercivity.wip_congr_ae hae, hsplit]
  linarith [hD, hT2b.2, hT4b.2, hsmall]

end Work.FTS.StrongEps.EpsE4Thr
