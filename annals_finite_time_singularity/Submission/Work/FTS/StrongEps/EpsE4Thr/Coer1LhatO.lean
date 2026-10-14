import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.BdryAbstract
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.ExtData
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.ExtDeriv
import Submission.Work.FTS.PressureOn.PoissonAux.kernelGradAux2
import Submission.Work.FTS.PressureOn.PoissonAux.kernelIntegral
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.CoerDataTO
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.est_D_O
import Submission.Work.FTS.StrongEps.EpsRLX.WpUniformBound
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.DelicateHon
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.SlotData
import Submission.Work.FTS.StrongPersist.N6_fkH
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_FinalLeaves.profDerivData_min_proved
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2W.FstarDzIterFourPsiAe
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.BoundaryTime.BdryDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Filter
open Work.FTS.Physical (physVel)
open scoped Topology NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.PressureOn.Connect

noncomputable section

variable {α : NNReal} {ω : R3 → ℝ → R3} {T : ℝ}

theorem hasFDerivWithinAt_potOn_uncurry_boundary (hT : 0 < T)
    (hstrips : ∀ S ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S))
    (hcurl : ∀ t ∈ Set.Ico 0 T, ∀ x, vorticity (fun z => physVel ω z t) x = ω x t)
    (hsupp : ∀ S ∈ Set.Ioo 0 T, ∃ R, ∀ t ∈ Set.Icc 0 S, ∀ x, ω x t ≠ 0 → ‖x‖ ≤ R)
    (hcontDt : ContinuousOn (fun q : R3 × ℝ => timeDeriv ω q.1 q.2) (Set.univ ×ˢ Set.Ico 0 T))
    (hderiv : ∀ x, ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω x) (timeDeriv ω x t) (Set.Ici t) t)
    (hgq : ∀ t ∈ Set.Ioo 0 T, ∀ x, HasFDerivAt (potOn ω · t) (potGradCLM ω x t) x) :
    ∀ x₀ : R3, ∀ y₀ ∈ Metric.ball x₀ 1,
      HasFDerivWithinAt (fun p : R3 × ℝ => potOn ω p.1 p.2)
        (potFDerivExt ω T (y₀, 0)) (bbox x₀ T) (y₀, 0) := by
  have hT2T : T / 2 ≤ T := by linarith
  intro x₀ y₀ hy₀
  have hmain := hasFDerivWithinAt_of_boundary_data
    (F := fun p : R3 × ℝ => potOn ω p.1 p.2)
    (A := potGradExt ω T) (c := fun p : R3 × ℝ => potTDerivExt ω T p.1 p.2)
    hT hy₀
    (potOn_uncurry_continuousOn_strip (α := α) hT hstrips hcurl hsupp)
    (potGradExt_continuousOn_strip (α := α) hT hstrips hcurl)
    (potTDerivExt_continuousOn_strip (α := α) hT hstrips hcurl hsupp hcontDt hderiv)
    (fun σ hσ z => by
      have hpg : potGradExt ω T (z, σ) = timeDeriv (physVel ω) z σ
          - crossVec (physVel ω z σ) (ω z σ) := by
        simp only [potGradExt, if_neg (ne_of_gt hσ.1)]
      rw [hpg]
      simpa only [potGradCLM] using hgq σ ⟨hσ.1, lt_of_lt_of_le hσ.2 hT2T⟩ z)
    (fun σ hσ => by
      rw [potTDerivExt_eq_potTDeriv ω T y₀ hσ.1]
      exact hasDerivAt_potOn_time_aux hstrips hcurl hsupp hcontDt hderiv y₀
        ⟨hσ.1, lt_of_lt_of_le hσ.2 hT2T⟩)
  simpa only [bbox, potFDerivExt] using hmain

end

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.Coer1LhatO =====
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

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The level-one coercivity of `𝓛̂` on the open class**: the frozen `Coer1.coer1_Lhat` with
`RegQ α 2` replaced by `RegQo α 2`. -/
theorem coer1_Lhat_O {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) {f : Fn}
    (hf : RegQo α 2 f) (hIP : IntPkgO α f) :
    2 * Work.Spaces.HkSq α 1 f
      ≤ Work.Coercivity.H1IP α (Work.FTS.CoercivityFix.Lhat f) f := by
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hf.1
  have hm1 : Work.Spaces.HkMem α 1 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hso 1 (by norm_num) hf.2.1
  -- the `ℋ¹`-energy is the sum of the three weighted energies
  have hHk : Work.Spaces.HkSq α 1 f
      = Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta (Work.Spaces.Dz f)
        + Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta f
        + Work.FTS.CoercivityFix.Coer1.En (Work.Spaces.gam α) (Work.Spaces.Dth f) := by
    rw [Work.FTS.StrongPersist.HkSq_one_eq_SO α hso hm1,
      Work.FTS.CoercivityFix.Coer1.EDz_eq_En,
      Work.FTS.CoercivityFix.Coer1.EfEta_eq_En,
      Work.FTS.CoercivityFix.Coer1.EDth_eq_En]
    ring
  -- the two integrability certificates consumed by `EDthW_le_En_gam`
  have hDθW : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dth f z θ) ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q
      (A := fun z θ => (Work.Spaces.mixed 0 1 f z θ) ^ 2 * Work.Spaces.w z ^ 2)
      (hIP.sqMixedOne 1 0 (by norm_num) (by norm_num)) (fun z θ => by
        simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero,
          Work.Spaces.DthIter_succ])
  have hDθG : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dth f z θ) ^ 2 * Work.Spaces.w z ^ 2
        * Work.FTS.CoercivityFix.Coer1.sig (Work.Spaces.gam α) θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q
      (A := fun z θ => (Work.Spaces.mixed 0 1 f z θ) ^ 2
        * Work.Spaces.w z ^ 2 * Work.FTS.CoercivityFix.Coer1.sig (Work.Spaces.gam α) θ)
      (Work.FTS.CoercivityFix.Coer1.to_h1
        (hIP.sqMixedGam 1 0 (by norm_num) (by norm_num))) (fun z θ => by
        simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero,
          Work.Spaces.DthIter_succ])
  have hW : Work.Coercivity.EDthW f
      ≤ Work.FTS.CoercivityFix.Coer1.En (Work.Spaces.gam α) (Work.Spaces.Dth f) :=
    Work.FTS.CoercivityFix.Coer1.EDthW_le_En_gam α hα f hDθW hDθG
  have hD : (17 / 40) * Work.FTS.CoercivityFix.Coer1.En (Work.Spaces.gam α) (Work.Spaces.Dth f)
      ≤ Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α))
          (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dth f) := by
    have h := OClass.est_D_O α hα hα1 hf hIP
    rw [Work.FTS.CoercivityFix.Coer1.EDth_eq_En] at h
    have hw : Work.Coercivity.thetaW α = Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) := by
      funext z θ
      rfl
    rw [hw] at h
    exact h
  exact Work.FTS.CoercivityFix.Coer1.assembly α hα hα1 hHk hW
    (OClass.est_A_O α hα hα1 hf hIP) (est_B_O α hα hα1 hf hIP)
    (OClass.est_C_O α hα hα1 hf hIP) hD

/-- **The clean level-1 data of the coercivity induction on the open class** — the open-class
analogue of `Assembly.coerData2_one_H1IP`: the level-`1` `CoerData2O` for `H1IP`, with coercivity
constant `2` (as in `coer1_Lhat`/`ledger`) and the Cauchy–Schwarz constant of `H1IP_cs_Q_O`. -/
theorem coerData2_one_H1IP_O :
    ∃ CC₁ : ℝ, 0 < CC₁ ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 (1 / 4) →
      CoerData2O α 1 (Work.Coercivity.H1IP α) 2 CC₁ := by
  obtain ⟨C, hC, hcs⟩ := H1IP_cs_Q_O
  refine ⟨C, hC, fun α hα => ?_⟩
  have hα4 : α ≤ 1 / 4 := hα.2
  refine
    { hcc := by norm_num
      hCC := hC
      cs := fun f g hf hg =>
        hcs α hα.1 f g (regQo_mono (by norm_num) hf) (regQo_mono (by norm_num) hg)
      coer := fun f hf => ?_ }
  have hreg : RegQo α 2 f := hf
  have h := coer1_Lhat_O hα.1 hα4 hreg (IntPkg_O hα.1 hreg)
  simpa using h


end Work.FTS.StrongEps.EpsE4Thr
end
end
