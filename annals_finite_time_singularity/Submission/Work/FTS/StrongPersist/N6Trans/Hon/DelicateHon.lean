import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.CoercivityFix.Assembly.step2_data
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.coerData2_four =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (RegQ)

set_option autoImplicit false

/-! ## The `α`-uniform defect constant in the `HkNorm` form -/


/-! ## The step, in the paper's range `α ≥ -1/10` -/


/-! ## The three iterations -/


end Work.FTS.CoercivityFix.Assembly
end
end
-- ===== merged: Submission.Work.FTS.CoercivityFix.Transfer.stepT =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (RegQ CoerAdm)

set_option autoImplicit false
set_option maxHeartbeats 800000



end Work.FTS.CoercivityFix.Transfer
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.HkIntegrand_perz_six_noTraces =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

theorem HkIntegrand_perz_six_noTraces :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ {f : ℝ → ℝ → ℝ},
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 8 f →
      ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 f z θ)
        ≤ C * (1 + (Work.Spaces.w z) ^ 2) * (1 + Work.Spaces.HkNorm α 8 f) ^ 2 := by
  obtain ⟨Cz, hCzpos, hCz⟩ := HkIntegrand_zslot_perz_six_noTraces
  obtain ⟨Cm, hCmpos, hCm⟩ := mixed_slot_perz_le8
  exact HkIntegrand_perz_le_of_halves 6 Cz Cm hCzpos hCmpos hCz hCm

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.est_C_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.OClass

open Work.FTS.Galerkin (Fn)

set_option maxHeartbeats 1600000

/-- **The plain `L²`-pairing of `𝓛̂` in the open class.**
`⟨𝓛̂f, f⟩_{w²} ≥ (1/8)·E_1(f) - 6·E_1(D_θ f)`: `(LW)` gives `⟨𝓛f,f⟩ = ½E_1(f)`, and the
transport pairing in the plain radial weight costs at most `6·E_1(D_θ f)`.

This is `Work.FTS.CoercivityFix.Coer1.est_C` with the interior class `RegQ α 2` replaced by
the open class `RegQo α 2` and the integrability bundle `IntPkg` by `IntPkgO`. -/
theorem est_C_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.RegQo α 2 f)
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f) :
    (1 / 8) * Work.FTS.CoercivityFix.Coer1.EnOne f - 6 * Work.Coercivity.EDthW f
      ≤ Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
          (Work.FTS.CoercivityFix.Lhat f) f := by
  have hp := hIP
  -- ## the three integrability certificates, in the shapes the pairing lemmas ask for
  have hU : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (f z θ) ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q (A := fun z θ =>
      (Work.Spaces.DzIter 0 f z θ) ^ 2 * Work.Spaces.w z ^ 2)
      (hp.sqDzOne 0 (by norm_num)) (fun z θ => by
        simp only [Work.Spaces.DzIter_zero])
  have hD : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q (A := fun z θ =>
      (Work.Spaces.mixed 0 1 f z θ) ^ 2 * Work.Spaces.w z ^ 2)
      (hp.sqMixedOne 1 0 (by norm_num) (by norm_num)) (fun z θ => by
        simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero,
          Work.Spaces.DthIter_succ]
        ring)
  have hT : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.Transport f z θ * f z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q (A := fun z θ =>
      3 * (Work.Spaces.Dth f z θ * f z θ * Work.Spaces.w z ^ 2 / (1 + z)))
      (hp.hint_f_one.const_mul 3) (fun z θ => by
        simp only [Work.Coercivity.Transport]; ring)
  -- ## the `(LW)` identity at `σ = 1`
  have hU1 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      f z θ ^ 2 * Work.Spaces.w z ^ 2 * (1 : ℝ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q hU (fun z θ => by ring)
  have hL1 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.L f z θ * f z θ * Work.Spaces.w z ^ 2 * (1 : ℝ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q (A := fun z θ =>
      Work.Coercivity.L f z θ * f z θ * Work.Spaces.w z ^ 2)
      hp.intL_f_one (fun z θ => by ring)
  have hL := Work.FTS.CoercivityFix.Coer1SO.wip_L_self_QO f hp.zibp_f (fun _ => 1) hU1 hL1
  simp only [mul_one] at hL
  have hw : Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) f f
      = Work.FTS.CoercivityFix.Coer1.EnOne f :=
    Work.FTS.CoercivityFix.Coer1.wip_one_self f
  -- ## the transport pairing bound in the plain radial weight
  have hbd := Work.FTS.CoercivityFix.Coer1.transport_w2_bound hT hD hU
  have hsplit : Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
      (Work.FTS.CoercivityFix.Lhat f) f
      = Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) (Work.Coercivity.L f) f
        - Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
            (Work.Coercivity.Transport f) f := by
    have h := Work.FTS.CoercivityFix.Coer1.wip_sub_left (ρ := fun z _ => Work.Spaces.w z ^ 2)
      (A := Work.Coercivity.L f) (B := Work.Coercivity.Transport f) (C := f)
      hp.intL_f_one hT
    show Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
      (fun z θ => Work.Coercivity.L f z θ - Work.Coercivity.Transport f z θ) f = _
    exact h
  rw [hsplit, hL, hw]
  linarith [hbd]

end Work.FTS.StrongEps.EpsE4Thr.OClass
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.Dth_LGammaT_eq_O =====
section

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
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.Dz_LGammaT_eq_O =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
# `D_z(𝓛_Γ^T f) = 𝓛̂(D_z f) + E₂ α f` — the transfer of the `D_z`-commutator, open class

The open-class (`Work.FTS.EllipticEst.SmoothOpen`, i.e. genuine `C^∞` on the *open* quadrant
`(0,∞) × (0,π/2)`) twin of `Work.FTS.CoercivityFix.Transfer.Dz_LGammaT_eq`, whose hypothesis is
the interior class `Work.FTS.LocData.SmoothQuad` (`C^∞` on the strip `z > -1`).

With the split `𝓛_Γ^T = 𝓛̂ + Corr` (`CoercivityFix.LGammaT_eq_Lhat_add_Corr`), differentiating the
two `z`-slices at an interior point splits the identity into

* `D_z(𝓛̂ f) = 𝓛̂(D_z f) + Ê₂ f` — `Work.FTS.StrongPersist.H6Aux.Dz_Lhat_of_open`, already stated
  for `SmoothOpen` (the interior character of the `𝒟_z`-commutator of `𝓛̂`);
* `D_z(Corr α f) z θ = Γ(θ)·radS α f z` — `Transfer.Dz_Corr_eq`, which needs only
  `Work.Coercivity.HardyHyp f` and `0 < z` (nothing about smoothness), because `Corr` is an
  angular factor times a purely *radial* profile and `D_z` falls on the radial factor only;
* `Ê₂ f + Γ·radS = E₂ α f` — definitional (`Transfer.E2_eq`).

The two `z`-slices `t ↦ 𝓛̂ f t θ` and `t ↦ Corr α f t θ` are differentiable at `z > 0`: the first
from `SmoothOpen f` (all its summands are slices of `SmoothOpen` functions, differentiated by
`SmoothOpen.hasDerivAt_slice`), the second from `Transfer.hasDerivAt_Corr_slice` (`HardyHyp`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TransO

theorem Dz_LGammaT_eq_O (α : ℝ) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hfH : Work.Coercivity.HardyHyp f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.Dz (Work.Coercivity.LGammaT α f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
        + Work.FTS.CoercivityFix.Transfer.E2 α f z θ := by
  have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ, hθ2⟩
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩
  -- ## the `z`-slices are differentiable at `z`
  have hfz : HasDerivAt (fun t : ℝ => f t θ) (Work.Spaces.pz f z θ) z :=
    hf.hasDerivAt_slice hθI hz
  have hDzz : HasDerivAt (fun t : ℝ => Work.Spaces.Dz f t θ)
      (Work.Spaces.pz (Work.Spaces.Dz f) z θ) z :=
    hf.Dz.hasDerivAt_slice hθI hz
  have hDthz : HasDerivAt (fun t : ℝ => Work.Spaces.Dth f t θ)
      (Work.Spaces.pz (Work.Spaces.Dth f) z θ) z :=
    hf.Dth.hasDerivAt_slice hθI hz
  have hLz : DifferentiableAt ℝ (fun t : ℝ => Work.FTS.CoercivityFix.Lhat f t θ) z := by
    have hne : (1 + z : ℝ) ≠ 0 := by positivity
    have hfun : (fun t : ℝ => Work.FTS.CoercivityFix.Lhat f t θ)
        = fun t : ℝ => f t θ + Work.Spaces.Dz f t θ - 2 * f t θ / (1 + t)
            - 3 * Work.Spaces.Dth f t θ / (1 + t) :=
      funext fun t => Work.FTS.CoercivityFix.Lhat_eq f t θ
    rw [hfun]
    exact (((hfz.differentiableAt.add hDzz.differentiableAt).sub
      (((differentiableAt_const (2 : ℝ)).mul hfz.differentiableAt).div
        ((differentiableAt_const (1 : ℝ)).add differentiableAt_id) hne)).sub
      (((differentiableAt_const (3 : ℝ)).mul hDthz.differentiableAt).div
        ((differentiableAt_const (1 : ℝ)).add differentiableAt_id) hne))
  have hhasC := Work.FTS.CoercivityFix.Transfer.hasDerivAt_Corr_slice (z := z) (θ := θ)
    α f hfH hz
  have hdiffC : DifferentiableAt ℝ (fun t : ℝ => Work.FTS.CoercivityFix.Corr α f t θ) z :=
    hhasC.differentiableAt
  -- ## the two commutators
  have hL : Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
        + Work.FTS.CoercivityFix.E2hat f z θ :=
    Work.FTS.StrongPersist.H6Aux.Dz_Lhat_of_open Work.FTS.EllipticEst.isOpen_Q0 hf hmem hz
  have hC : Work.Spaces.Dz (Work.FTS.CoercivityFix.Corr α f) z θ
      = Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z :=
    Work.FTS.CoercivityFix.Transfer.Dz_Corr_eq α f hfH hz
  -- ## the slices add
  have hslice : (fun t : ℝ => Work.Coercivity.LGammaT α f t θ)
      = (fun t : ℝ => Work.FTS.CoercivityFix.Lhat f t θ)
        + (fun t : ℝ => Work.FTS.CoercivityFix.Corr α f t θ) := by
    funext t
    rw [Work.FTS.CoercivityFix.LGammaT_eq_Lhat_add_Corr α f]
    rfl
  -- ## the conclusion
  rw [show Work.Spaces.Dz (Work.Coercivity.LGammaT α f) z θ
      = z * deriv (fun t : ℝ => Work.Coercivity.LGammaT α f t θ) z from rfl]
  rw [hslice, deriv_add hLz hdiffC, mul_add]
  rw [show z * deriv (fun t : ℝ => Work.FTS.CoercivityFix.Lhat f t θ) z
        = Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ from rfl, hL]
  rw [show z * deriv (fun t : ℝ => Work.FTS.CoercivityFix.Corr α f t θ) z
        = Work.Spaces.Dz (Work.FTS.CoercivityFix.Corr α f) z θ from rfl, hC]
  rw [Work.FTS.CoercivityFix.Transfer.E2_eq]
  ring

end Work.FTS.StrongEps.EpsE4Thr.TransO
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.Hon.DelicateHon =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

open Work.FTS.TransportS.T2Sup

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The honest delicate estimate -/

theorem DelicateHon : Work.FTS.StrongPersist.N6Trans.Hon.DelicateHonProp := by
  unfold Work.FTS.StrongPersist.N6Trans.Hon.DelicateHonProp
  obtain ⟨CΦ, hCΦpos, hΦall⟩ := Work.FTS.TransportS.SlotT2.supThetaIntOpen
  refine ⟨10 * CΦ + 2, by positivity, ?_⟩
  intro α q f g hα hα1 hq0 hqγ hsmf hmf hcoef hsmg hmg4 hmg5 hdec
  have hγpos : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  have hγ1pos : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  -- the auxiliary functions
  set Φ : ℝ → ℝ := fun z => sSup {y : ℝ | ∃ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
    y = |Work.Spaces.DzIter 3 f z θ|} with hΦdef
  set Ψ : ℝ → ℝ := fun θ => ∫ s in Work.Spaces.Iz,
    (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2 with hΨdef
  set Q : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.mixed 3 1 g z θ) ^ 2
    with hQdef
  set A : ℝ := ∫ z in Work.Spaces.Iz, (Φ z) ^ 2 * (Work.Spaces.w z) ^ 2 with hAdef
  set I4 : ℝ := ∫ θ in Work.Spaces.Iθ,
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ with hI4def
  set Bq : ℝ := ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Q z with hBqdef
  set 𝔉 : ℝ → ℝ → ℝ := fun z θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
    * |Work.Spaces.mixed 3 0 f z θ| * |Work.Spaces.mixed 1 1 g z θ|
    * |Work.Spaces.mixed 3 1 g z θ| with h𝔉def
  -- nonnegativity
  have hΨnn : ∀ θ, 0 ≤ Ψ θ := by
    intro θ
    rw [hΨdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ici
      (fun s _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hQnn : ∀ z, 0 ≤ Q z := by
    intro z
    rw [hQdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)
        (sq_nonneg _))
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ici
      (fun z _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hI4nn : 0 ≤ I4 := by
    rw [hI4def]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)
        (hΨnn θ))
  have hBqnn : 0 ≤ Bq := by
    rw [hBqdef]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ici
      (fun z _ => mul_nonneg (sq_nonneg _) (hQnn z))
  have h𝔉nn : ∀ z, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ 𝔉 z θ := by
    intro z θ hθ
    rw [h𝔉def]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _))
      (abs_nonneg _)) (abs_nonneg _)) (abs_nonneg _)
  -- the f-side: the angular supremum of `D_z³f`
  obtain ⟨hΦInt, hΦLe⟩ := hΦall α f 3 hα hα1 (le_refl 3) hsmf hmf
  have hΦbdd : ∀ z ∈ Set.Ioi (0 : ℝ), BddAbove {y : ℝ |
      ∃ θ ∈ Set.Ioo (0 : ℝ) (π / 2), y = |Work.Spaces.DzIter 3 f z θ|} :=
    fun z hz => Work.FTS.TransportS.SlotT2.supOpen_slice_bddAbove hsmf hmf
      hα hα1 (by norm_num) hz
  have hΦge : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.DzIter 3 f z θ| ≤ Φ z := by
    intro z hz θ hθ
    rw [hΦdef]
    exact le_csSup (hΦbdd z hz) ⟨θ, hθ, rfl⟩
  have hΦnn : ∀ z ∈ Set.Ioi (0 : ℝ), 0 ≤ Φ z := by
    intro z hz
    rw [hΦdef]
    exact le_trans (abs_nonneg _) (le_csSup (hΦbdd z hz)
      ⟨Real.pi / 4, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, rfl⟩)
  have hA0 : A ≤ CΦ / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f := by
    rw [hAdef]
    simpa only [hΦdef] using hΦLe
  -- the g-side: the Hardy inequality and the two `ℋ⁴`-slots
  have hHardy := hardyG_ae_open hα hsmg hmg4 hdec
  obtain ⟨hPsiInt0, hPsiLe0⟩ := psiMarginal_le_open hα hsmg hmg4
  have hPsiInt : MeasureTheory.IntegrableOn
      (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ) Work.Spaces.Iθ := by
    simpa only [hΨdef] using hPsiInt0
  have hI4le : I4 ≤ Work.Spaces.HkSq α 4 g := by
    rw [hI4def]
    simpa only [hΨdef] using hPsiLe0
  obtain ⟨hQslice, hQint, hQle⟩ := qFun_le_open hα hsmg hmg4
  have hBqle : Bq ≤ Work.Spaces.HkSq α 4 g := by
    rw [hBqdef]
    simpa only [hQdef] using hQle
  have hΨaesm : MeasureTheory.AEStronglyMeasurable (fun θ => Real.sqrt (Ψ θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h0 := delicate_psiTheta_aesm hsmg
    have h1 : (fun θ => Real.sqrt (Ψ θ))
        = fun θ => Real.sqrt (∫ s in Work.Spaces.Iz,
            (Work.Spaces.w s) ^ 2 * (Work.Spaces.mixed 2 1 g s θ) ^ 2) := by
      funext θ
      simp only [hΨdef]
    rw [h1]
    exact Real.continuous_sqrt.comp_aestronglyMeasurable h0
  -- the good angles
  have hgoodθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (π / 2) ∧
        ∀ z ∈ Set.Ioi (0 : ℝ), (Work.Spaces.mixed 1 1 g z θ) ^ 2 ≤ Ψ θ := by
    have hIoo : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
      rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iθ]
      exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
    filter_upwards [hIoo, hHardy] with θ h1 h2
    refine ⟨h1, fun z hz => ?_⟩
    rw [hΨdef]
    exact h2 z hz
  -- the main chain
  have hmain : ∀ t : ℝ, 0 < t →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, 𝔉 z θ)
        ≤ (t * A + (I4 * Bq) / t) / 2 := by
    intro t ht
    have hPtwise : ∀ z ∈ Set.Ioi (0 : ℝ),
        (∫ θ in Work.Spaces.Iθ, 𝔉 z θ)
          ≤ (t * ((Φ z) ^ 2 * (Work.Spaces.w z) ^ 2)
              + I4 * ((Work.Spaces.w z) ^ 2 * Q z) / t) / 2 := by
      intro z hz
      have hz0 : (0 : ℝ) < z := hz
      -- the integrability of the Hardy majorant
      have haesmS : MeasureTheory.AEStronglyMeasurable
          (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sqrt (Ψ θ)
            * |Work.Spaces.mixed 3 1 g z θ|)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        have h1 : MeasureTheory.AEStronglyMeasurable
            (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
          have h := delicate_aesm_weight_mul (α := α) (v := fun _ : ℝ => (1 : ℝ))
            continuousOn_const
          simpa only [mul_one] using h
        have h3 : MeasureTheory.AEStronglyMeasurable
            (fun θ => |Work.Spaces.mixed 3 1 g z θ|)
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
          have hcont : ContinuousOn (fun θ => |Work.Spaces.mixed 3 1 g z θ|)
              (Set.Ioo 0 (π / 2)) :=
            ((hsmg.mixed 3 1).curry_θ hz).continuousOn.abs
          rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iθ]
          exact hcont.aestronglyMeasurable measurableSet_Ioo
        exact (h1.mul hΨaesm).mul h3
      have hdomInt : MeasureTheory.IntegrableOn
          (fun θ => (1 / 2) * ((Work.Spaces.w z) ^ 2 * Φ z)
            * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ
              + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 3 1 g z θ) ^ 2)) Work.Spaces.Iθ :=
        (hPsiInt.add (hQslice z (le_of_lt hz0))).const_mul _
      have hIntM : MeasureTheory.IntegrableOn
          (fun θ => (Work.Spaces.w z) ^ 2 * Φ z
            * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sqrt (Ψ θ)
              * |Work.Spaces.mixed 3 1 g z θ|)) Work.Spaces.Iθ := by
        refine hdomInt.mono' ?_ ?_
        · refine (haesmS.const_mul ((Work.Spaces.w z) ^ 2 * Φ z)).congr ?_
          filter_upwards with θ
          ring
        · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
          rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (hΦnn z hz))
            (mul_nonneg (mul_nonneg (Real.rpow_nonneg
              (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _) (Real.sqrt_nonneg _))
              (abs_nonneg _)))]
          have hσ0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ
          have hsq : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)) ^ 2
              = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
            delicate_sq_half_rpow (x := Real.sin (2 * θ)) (β := Work.Spaces.gam α) hσ0
          have ham := delicate_amgm
            (a := (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2) * Real.sqrt (Ψ θ))
            (b := (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)
              * |Work.Spaces.mixed 3 1 g z θ|) (t := 1) (by norm_num)
          have hrhs : (1 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)
                * Real.sqrt (Ψ θ)) ^ 2
              + ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)
                * |Work.Spaces.mixed 3 1 g z θ|) ^ 2 / 1) / 2
              = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ
                + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed 3 1 g z θ) ^ 2) / 2 := by
            rw [mul_pow, mul_pow, hsq, Real.sq_sqrt (hΨnn θ), sq_abs]
            ring
          rw [hrhs] at ham
          have hcongr : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sqrt (Ψ θ)
                * |Work.Spaces.mixed 3 1 g z θ|
              = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2) * Real.sqrt (Ψ θ))
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)
                  * |Work.Spaces.mixed 3 1 g z θ|) := by
            rw [← hsq]
            ring
          have hinner : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sqrt (Ψ θ)
                * |Work.Spaces.mixed 3 1 g z θ|
              ≤ ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ
                + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed 3 1 g z θ) ^ 2) / 2 := by
            rw [hcongr]
            exact ham
          calc (Work.Spaces.w z) ^ 2 * Φ z
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sqrt (Ψ θ)
                  * |Work.Spaces.mixed 3 1 g z θ|)
              ≤ (Work.Spaces.w z) ^ 2 * Φ z
                * (((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ
                  + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                    * (Work.Spaces.mixed 3 1 g z θ) ^ 2) / 2) :=
                mul_le_mul_of_nonneg_left hinner (mul_nonneg (sq_nonneg _) (hΦnn z hz))
            _ = (1 / 2) * ((Work.Spaces.w z) ^ 2 * Φ z)
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ
                  + (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                    * (Work.Spaces.mixed 3 1 g z θ) ^ 2) := by ring
      -- step (a): the θ-integral against the Hardy majorant
      have ha : (∫ θ in Work.Spaces.Iθ, 𝔉 z θ)
          ≤ (Work.Spaces.w z) ^ 2 * Φ z
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * Real.sqrt (Ψ θ) * |Work.Spaces.mixed 3 1 g z θ|) := by
        have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
            𝔉 z θ ≤ (Work.Spaces.w z) ^ 2 * Φ z
              * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sqrt (Ψ θ)
                * |Work.Spaces.mixed 3 1 g z θ|) := by
          filter_upwards [hgoodθ] with θ hθ
          obtain ⟨hθIoo, hθhardy⟩ := hθ
          have hsin : 0 < Real.sin (2 * θ) :=
            Real.sin_pos_of_pos_of_lt_pi (by show (0 : ℝ) < 2 * θ; linarith [hθIoo.1])
              (by show 2 * θ < Real.pi; linarith [hθIoo.2, Real.pi_pos])
          have hσle : (Real.sin (2 * θ)) ^ (-q) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
            delicate_rpow_neg_le hsin (Real.sin_le_one _) hqγ
          have hF : |Work.Spaces.mixed 3 0 f z θ| ≤ Φ z := by
            rw [Work.Spaces.mixed_zero_right]
            exact hΦge z hz θ hθIoo
          have hG : |Work.Spaces.mixed 1 1 g z θ| ≤ Real.sqrt (Ψ θ) := by
            rw [← Real.sqrt_sq_eq_abs]
            exact Real.sqrt_le_sqrt (hθhardy z hz)
          have h1 := delicate_mul_four_le (a := (Real.sin (2 * θ)) ^ (-q))
            (a' := (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
            (b := |Work.Spaces.mixed 3 0 f z θ|) (b' := Φ z)
            (c := |Work.Spaces.mixed 1 1 g z θ|) (c' := Real.sqrt (Ψ θ))
            (d := |Work.Spaces.mixed 3 1 g z θ|) (d' := |Work.Spaces.mixed 3 1 g z θ|)
            hσle hF hG le_rfl (Real.rpow_nonneg (le_of_lt hsin) _) (abs_nonneg _)
            (abs_nonneg _) (abs_nonneg _)
            (Real.rpow_nonneg (le_of_lt hsin) _) (hΦnn z hz) (Real.sqrt_nonneg _)
          have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (Work.Spaces.w z))
          calc 𝔉 z θ = (Work.Spaces.w z) ^ 2
                * ((Real.sin (2 * θ)) ^ (-q) * |Work.Spaces.mixed 3 0 f z θ|
                  * |Work.Spaces.mixed 1 1 g z θ| * |Work.Spaces.mixed 3 1 g z θ|) := by
                rw [h𝔉def]; ring
            _ ≤ (Work.Spaces.w z) ^ 2
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Φ z
                  * Real.sqrt (Ψ θ) * |Work.Spaces.mixed 3 1 g z θ|) := h2
            _ = (Work.Spaces.w z) ^ 2 * Φ z
                * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sqrt (Ψ θ)
                  * |Work.Spaces.mixed 3 1 g z θ|) := by ring
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.integral_mono_of_nonneg
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ hθ => h𝔉nn z θ hθ)) hIntM hpt
      -- step (b): the angular Cauchy–Schwarz
      have hb : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * Real.sqrt (Ψ θ) * |Work.Spaces.mixed 3 1 g z θ|)
          ≤ Real.sqrt (I4 * Q z) := by
        refine delicate_le_sqrt_mul hI4nn (hQnn z) (fun r hr => ?_)
        have hdomInt : MeasureTheory.IntegrableOn
            (fun θ => (1 / 2) * (r * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ)
              + ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 3 1 g z θ) ^ 2) / r)) Work.Spaces.Iθ :=
          ((hPsiInt.const_mul r).add ((hQslice z (le_of_lt hz0)).div_const r)).const_mul (1 / 2)
        have hmono : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * Real.sqrt (Ψ θ) * |Work.Spaces.mixed 3 1 g z θ|)
            ≤ ∫ θ in Work.Spaces.Iθ, (1 / 2)
              * (r * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ)
                + ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed 3 1 g z θ) ^ 2) / r) := by
          refine MeasureTheory.setIntegral_mono_of_nonneg (fun θ hθ => ?_) (fun θ hθ => ?_)
            hdomInt
          · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg
              (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _) (Real.sqrt_nonneg _))
              (abs_nonneg _)
          · have hσ0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ
            have hsq : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)) ^ 2
                = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
              delicate_sq_half_rpow (x := Real.sin (2 * θ)) (β := Work.Spaces.gam α) hσ0
            have ham := delicate_amgm
              (a := (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2) * Real.sqrt (Ψ θ))
              (b := (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)
                * |Work.Spaces.mixed 3 1 g z θ|) (t := r) hr
            have hrhs : (r * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)
                  * Real.sqrt (Ψ θ)) ^ 2
                + ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)
                  * |Work.Spaces.mixed 3 1 g z θ|) ^ 2 / r) / 2
                = (r * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ)
                  + ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                    * (Work.Spaces.mixed 3 1 g z θ) ^ 2) / r) / 2 := by
              rw [mul_pow, mul_pow, hsq, Real.sq_sqrt (hΨnn θ), sq_abs]
            rw [hrhs] at ham
            have hcongr : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sqrt (Ψ θ)
                  * |Work.Spaces.mixed 3 1 g z θ|
                = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2) * Real.sqrt (Ψ θ))
                  * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α) / 2)
                    * |Work.Spaces.mixed 3 1 g z θ|) := by
              rw [← hsq]
              ring
            have hinner : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sqrt (Ψ θ)
                  * |Work.Spaces.mixed 3 1 g z θ|
                ≤ (r * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ)
                  + ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                    * (Work.Spaces.mixed 3 1 g z θ) ^ 2) / r) / 2 := by
              rw [hcongr]
              exact ham
            calc (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Real.sqrt (Ψ θ)
                  * |Work.Spaces.mixed 3 1 g z θ|
                ≤ (r * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ)
                  + ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                    * (Work.Spaces.mixed 3 1 g z θ) ^ 2) / r) / 2 := hinner
              _ = (1 / 2) * (r * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ)
                  + ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                    * (Work.Spaces.mixed 3 1 g z θ) ^ 2) / r) := by ring
        have hval : (∫ θ in Work.Spaces.Iθ, (1 / 2)
              * (r * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * Ψ θ)
                + ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed 3 1 g z θ) ^ 2) / r))
            = (r * I4 + Q z / r) / 2 := by
          rw [MeasureTheory.integral_const_mul,
            MeasureTheory.integral_add (hPsiInt.const_mul r) ((hQslice z (le_of_lt hz0)).div_const r),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_div, hI4def, hQdef]
          ring
        linarith [hmono, hval]
      -- step (c): the radial Young inequality
      have hc : (Work.Spaces.w z) ^ 2 * Φ z * Real.sqrt (I4 * Q z)
          ≤ (t * ((Φ z) ^ 2 * (Work.Spaces.w z) ^ 2)
              + I4 * ((Work.Spaces.w z) ^ 2 * Q z) / t) / 2 := by
        have hprod := delicate_amgm
          (a := Work.Spaces.w z * Φ z) (b := Work.Spaces.w z * Real.sqrt (I4 * Q z)) ht
        have e1 : (Work.Spaces.w z * Φ z) ^ 2 = (Φ z) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
        have e2 : (Work.Spaces.w z * Real.sqrt (I4 * Q z)) ^ 2
            = I4 * ((Work.Spaces.w z) ^ 2 * Q z) := by
          rw [mul_pow, Real.sq_sqrt (mul_nonneg hI4nn (hQnn z))]
          ring
        have e3 : (Work.Spaces.w z * Φ z) * (Work.Spaces.w z * Real.sqrt (I4 * Q z))
            = (Work.Spaces.w z) ^ 2 * Φ z * Real.sqrt (I4 * Q z) := by ring
        rwa [e1, e2, e3] at hprod
      calc (∫ θ in Work.Spaces.Iθ, 𝔉 z θ)
          ≤ (Work.Spaces.w z) ^ 2 * Φ z
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * Real.sqrt (Ψ θ) * |Work.Spaces.mixed 3 1 g z θ|) := ha
        _ ≤ (Work.Spaces.w z) ^ 2 * Φ z * Real.sqrt (I4 * Q z) :=
            mul_le_mul_of_nonneg_left hb (mul_nonneg (sq_nonneg _) (hΦnn z hz))
        _ ≤ _ := hc
    -- integrate the pointwise-in-`z` bound
    have hIntG : MeasureTheory.IntegrableOn
        (fun z => (t * ((Φ z) ^ 2 * (Work.Spaces.w z) ^ 2)
          + I4 * ((Work.Spaces.w z) ^ 2 * Q z) / t) / 2) Work.Spaces.Iz := by
      have h1 : MeasureTheory.IntegrableOn
          (fun z => t * ((Φ z) ^ 2 * (Work.Spaces.w z) ^ 2)) Work.Spaces.Iz :=
        hΦInt.const_mul t
      have h2 : MeasureTheory.IntegrableOn
          (fun z => I4 * ((Work.Spaces.w z) ^ 2 * Q z)) Work.Spaces.Iz :=
        MeasureTheory.IntegrableOn.congr_fun (hQint.const_mul I4)
          (fun z _ => rfl) measurableSet_Ici
      exact (h1.add (h2.div_const t)).div_const 2
    have hzm : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, 𝔉 z θ)
        ≤ ∫ z in Work.Spaces.Iz, (t * ((Φ z) ^ 2 * (Work.Spaces.w z) ^ 2)
          + I4 * ((Work.Spaces.w z) ^ 2 * Q z) / t) / 2 := by
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun z => MeasureTheory.setIntegral_nonneg
          measurableSet_Icc (fun θ hθ => h𝔉nn z θ hθ))) hIntG ?_
      rw [Work.FTS.TransportS.SlotT2.supOpen_restrict_Iz]
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      exact hPtwise z hz
    have hval : (∫ z in Work.Spaces.Iz, (t * ((Φ z) ^ 2 * (Work.Spaces.w z) ^ 2)
          + I4 * ((Work.Spaces.w z) ^ 2 * Q z) / t) / 2) = (t * A + (I4 * Bq) / t) / 2 := by
      have h1 : MeasureTheory.IntegrableOn
          (fun z => t * ((Φ z) ^ 2 * (Work.Spaces.w z) ^ 2)) Work.Spaces.Iz :=
        hΦInt.const_mul t
      have h2 : MeasureTheory.IntegrableOn
          (fun z => I4 * ((Work.Spaces.w z) ^ 2 * Q z)) Work.Spaces.Iz :=
        MeasureTheory.IntegrableOn.congr_fun (hQint.const_mul I4)
          (fun z _ => rfl) measurableSet_Ici
      rw [MeasureTheory.integral_div,
        MeasureTheory.integral_add h1 (h2.div_const t),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_div,
        MeasureTheory.integral_const_mul, ← hAdef, ← hBqdef]
    linarith [hzm, hval]
  -- the final arithmetic
  have hfin2 := delicate_le_sqrt_mul hAnn (mul_nonneg hI4nn hBqnn) hmain
  have hHkg : 0 ≤ Work.Spaces.HkSq α 4 g := Work.Spaces.HkSq_nonneg α 4 g
  have hrp : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hK : 0 ≤ Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f :=
    add_nonneg (Work.Spaces.HkNorm_nonneg α 4 f) (Work.FTS.TransportS.coefTh_nonneg 1 f)
  have hXnK : Work.Spaces.HkNorm α 4 f
      ≤ Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f := by
    rw [Work.FTS.Nonlin.Xn]
    linarith [Work.FTS.TransportS.coefTh_nonneg 1 f]
  -- `√(CΦ/(γ-1)) = √(10 CΦ) · α^{-1/2}`
  have hsqα : α ^ (-(1 / 2 : ℝ)) * α ^ (-(1 / 2 : ℝ)) = α ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hα]
    norm_num
  have hsqrtgam : Real.sqrt (CΦ / (Work.Spaces.gam α - 1))
      = Real.sqrt (10 * CΦ) * α ^ (-(1 / 2 : ℝ)) := by
    rw [Work.Spaces.gam_sub_one]
    have h1 : CΦ / (α / 10)
        = (Real.sqrt (10 * CΦ) * α ^ (-(1 / 2 : ℝ))) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), sq, hsqα, Real.rpow_neg_one]
      field_simp
    rw [h1, Real.sqrt_sq (by positivity)]
  have hsq_le : Real.sqrt (10 * CΦ) ≤ 10 * CΦ + 1 := by
    have h0 : 0 ≤ 10 * CΦ := by positivity
    have h1 : (Real.sqrt (10 * CΦ)) ^ 2 = 10 * CΦ := Real.sq_sqrt h0
    nlinarith [sq_nonneg (Real.sqrt (10 * CΦ) - 1 / 2), Real.sqrt_nonneg (10 * CΦ)]
  -- the `√`-bound
  have hsqrt_le : Real.sqrt (A * (I4 * Bq))
      ≤ Real.sqrt (CΦ / (Work.Spaces.gam α - 1)) * Work.Spaces.HkNorm α 4 f
        * Work.Spaces.HkSq α 4 g := by
    have h1 : I4 * Bq ≤ Work.Spaces.HkSq α 4 g * Work.Spaces.HkSq α 4 g :=
      mul_le_mul hI4le hBqle hBqnn hHkg
    have h2 : A * (I4 * Bq) ≤ (CΦ / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f)
        * (Work.Spaces.HkSq α 4 g * Work.Spaces.HkSq α 4 g) :=
      mul_le_mul hA0 h1 (mul_nonneg hI4nn hBqnn)
        (mul_nonneg (div_nonneg hCΦpos.le hγ1pos.le) (Work.Spaces.HkSq_nonneg α 4 f))
    have h3 : (CΦ / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f)
        * (Work.Spaces.HkSq α 4 g * Work.Spaces.HkSq α 4 g)
        = ((CΦ / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f)
            * Work.Spaces.HkSq α 4 g ^ 2) := by ring
    rw [h3] at h2
    calc Real.sqrt (A * (I4 * Bq))
        ≤ Real.sqrt ((CΦ / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f)
            * Work.Spaces.HkSq α 4 g ^ 2) := Real.sqrt_le_sqrt h2
      _ = Real.sqrt (CΦ / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f)
            * Real.sqrt (Work.Spaces.HkSq α 4 g ^ 2) := by
          rw [Real.sqrt_mul (mul_nonneg (div_nonneg hCΦpos.le hγ1pos.le)
            (Work.Spaces.HkSq_nonneg α 4 f))]
      _ = Real.sqrt (CΦ / (Work.Spaces.gam α - 1)) * Work.Spaces.HkNorm α 4 f
            * Work.Spaces.HkSq α 4 g := by
          rw [Real.sqrt_mul (div_nonneg hCΦpos.le hγ1pos.le), Real.sqrt_sq hHkg,
            Work.Spaces.HkNorm]
  -- the remaining arithmetic
  have hstep : Real.sqrt (CΦ / (Work.Spaces.gam α - 1)) * Work.Spaces.HkNorm α 4 f
        * Work.Spaces.HkSq α 4 g
      ≤ (10 * CΦ + 2) * α ^ (-(1 / 2 : ℝ))
        * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f) * Work.Spaces.HkSq α 4 g := by
    rw [hsqrtgam]
    have h1 : Real.sqrt (10 * CΦ) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 f
          * Work.Spaces.HkSq α 4 g
        ≤ (10 * CΦ + 1) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 f
          * Work.Spaces.HkSq α 4 g := by
      nlinarith [hsq_le, hrp, Work.Spaces.HkNorm_nonneg α 4 f, hHkg,
        mul_nonneg (mul_nonneg hrp (Work.Spaces.HkNorm_nonneg α 4 f)) hHkg]
    have h2 : (10 * CΦ + 1) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 f
          * Work.Spaces.HkSq α 4 g
        ≤ (10 * CΦ + 2) * α ^ (-(1 / 2 : ℝ))
          * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f) * Work.Spaces.HkSq α 4 g := by
      have hC1 : 0 ≤ 10 * CΦ + 1 := by positivity
      have hC2 : 0 ≤ 10 * CΦ + 2 := by positivity
      have hle : (10 * CΦ + 1) * Work.Spaces.HkNorm α 4 f ≤ (10 * CΦ + 2)
          * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f) := by
        nlinarith [hXnK, hC1, hC2, Work.Spaces.HkNorm_nonneg α 4 f, hK]
      calc (10 * CΦ + 1) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 f
            * Work.Spaces.HkSq α 4 g
          = α ^ (-(1 / 2 : ℝ)) * ((10 * CΦ + 1) * Work.Spaces.HkNorm α 4 f)
            * Work.Spaces.HkSq α 4 g := by ring
        _ ≤ α ^ (-(1 / 2 : ℝ)) * ((10 * CΦ + 2)
              * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f))
            * Work.Spaces.HkSq α 4 g := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hrp) hHkg
        _ = (10 * CΦ + 2) * α ^ (-(1 / 2 : ℝ))
            * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f) * Work.Spaces.HkSq α 4 g := by
            ring
    linarith [h1, h2]
  have hgoal : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, 𝔉 z θ)
      ≤ (10 * CΦ + 2) * α ^ (-(1 / 2 : ℝ))
        * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f) * Work.Spaces.HkSq α 4 g :=
    le_trans hfin2 (le_trans hsqrt_le hstep)
  simpa only [h𝔉def] using hgoal

end Work.FTS.StrongPersist.N6Trans.Hon
end
end
