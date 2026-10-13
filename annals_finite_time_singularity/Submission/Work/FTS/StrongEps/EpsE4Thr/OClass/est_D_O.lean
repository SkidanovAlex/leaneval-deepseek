import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgO
import Submission.Work.FTS.StrongEps.EpsE4Thr.OClass.Dth_Lhat_O
import Submission.Work.FTS.CoercivityFix.Coer1SO.wip_Dz_self_le_SO
import Submission.Work.FTS.StrongEps.EpsE4Thr.wip_transport_le_O
import Submission.Work.FTS.CoercivityFix.Coer1.Estimates

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

/-- The **open-class** twin of `Work.FTS.CoercivityFix.Coer1.est_D`
(`CoercivityFix/Coer1/Estimates.lean`, proved): the coercivity of the clean operator `𝓛̂` on the
`γ`-slot `D_θ`, with `RegQ α 2` replaced by `RegQo α 2` (= `SmoothOpen` instead of `SmoothQuad`)
and the integrability bundle `IntPkg` replaced by its open counterpart `IntPkgO`.
The open counterparts of the three ingredients of the frozen proof already exist:
`OClass.Dth_Lhat_open` (`D_θ(𝓛̂ f) = 𝓛̂(D_θ f)`), `Coer1SO.wip_L_self_QO` (the `(LW)` identity) and
`EpsE4Thr.wip_transport_le_O` (the transport bound).  The statement below is the frozen
conclusion rewritten from `En (gam α)`/`Rho (gam α)` to `EDth α`/`thetaW α`
(`Coer1.EDth_eq_En`, `Coer1.Rho_gam` are `rfl`-level).

Proof recipe: copy `Coer1/Estimates.lean:est_D` verbatim, replacing
`IntPkg_Q α hα hf` by the hypothesis `hIP : IntPkgO α f`,
`LhatCalc.Dth_Lhat hsq hz hθ.1 hθ.2` by `OClass.Dth_Lhat_open hf.1 hz hθ.1 hθ.2`,
`LhatCalc`'s `SmoothQuad.DthIter hsq 1` by `Work.FTS.EllipticEst.SmoothOpen.DthIter hf.1 1`, and
`wip_transport_le_Q` by `wip_transport_le_O` (its `SmoothOpen` hypothesis for `Dth f` is
`Work.FTS.EllipticEst.SmoothOpen.Dth hf.1`; the two endpoint hypotheses are
`((hf.2.2 1 0 (by norm_num)).2 z hz).1/.2`, i.e. the `BdryTraces α 2 f` field of `RegQo`). -/
theorem est_D_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.RegQo α 2 f)
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f) :
    (17 / 40) * Work.Coercivity.EDth α f
      ≤ Work.Coercivity.wip (Work.Coercivity.thetaW α)
          (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dth f) := by
  -- the open class unfolds into its three ingredients
  obtain ⟨hso, hm, hb⟩ := hf
  -- rewrite the frozen conclusion into its `En`/`Rho` shape
  rw [Work.FTS.CoercivityFix.Coer1.EDth_eq_En α f,
    ← Work.FTS.CoercivityFix.Coer1.Rho_gam α]
  -- ### the integrability certificate in the `w²σ` shape of the two `wip` identities
  have hp := hIP
  have h0 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dth f z θ) ^ 2
        * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (hp.sqMixedGam 1 0 (by norm_num) (by norm_num)).congr
      (MeasureTheory.ae_restrict_of_forall_mem (measurableSet_Ici.prod measurableSet_Icc)
        (fun p hpp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.Spaces.mixed, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_zero, Work.Spaces.DthIter_succ]
  have h1 := Work.FTS.CoercivityFix.Coer1.to_h1 (β := Work.Spaces.gam α) h0
  have h2 := Work.FTS.CoercivityFix.Coer1.to_tr_hint2 (β := Work.Spaces.gam α) h0
  have hL2 := Work.FTS.CoercivityFix.Coer1.to_h2 (β := Work.Spaces.gam α) hp.intL_Dth_gam
  have hT2 := Work.FTS.CoercivityFix.Coer1.to_tr_hint (β := Work.Spaces.gam α) hp.hint_Dth_gam
  -- ### the exact angular commutator identity, a.e.
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ := by
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iz_pos] with z hz
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo] with θ hθ
    exact Work.FTS.CoercivityFix.LhatCalc.Dth_Lhat_open hso hz hθ.1 hθ.2
  -- ### the two Euler–Lagrange inputs, in the open class
  have hL := Work.FTS.CoercivityFix.Coer1SO.wip_L_self_QO (Work.Spaces.Dth f) hp.zibp_Dth
    (Work.FTS.CoercivityFix.Coer1.sig (Work.Spaces.gam α)) h1 hL2
  have hw : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α))
      (Work.Spaces.Dth f) (Work.Spaces.Dth f)
      = Work.FTS.CoercivityFix.Coer1.En (Work.Spaces.gam α) (Work.Spaces.Dth f) :=
    Work.FTS.CoercivityFix.Coer1.wip_Rho_self (Work.Spaces.gam α) (Work.Spaces.Dth f)
  have hTr := wip_transport_le_O (Work.Spaces.gam α) (Work.Spaces.Dth f)
    (Work.FTS.EllipticEst.SmoothOpen.Dth hso)
    (fun z hz => ((hb 1 0 (by norm_num)).2 z hz).1)
    (fun z hz => ((hb 1 0 (by norm_num)).2 z hz).2) hT2 h2
  have hTr' : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α))
      (Work.Coercivity.Transport (Work.Spaces.Dth f)) (Work.Spaces.Dth f)
      ≤ (3 / 40) * Work.FTS.CoercivityFix.Coer1.En (Work.Spaces.gam α) (Work.Spaces.Dth f) := by
    rw [hw] at hTr
    have hg : (3 : ℝ) * |Work.Spaces.gam α - 1| ≤ 3 / 40 := by
      rw [Work.Spaces.gam]
      rw [show |(1 : ℝ) + α / 10 - 1| = α / 10 by
        rw [show (1 : ℝ) + α / 10 - 1 = α / 10 by ring, abs_of_nonneg (by linarith)]]
      linarith
    have hEn := Work.FTS.CoercivityFix.Coer1.En_nonneg (Work.Spaces.gam α)
      (Work.Spaces.Dth f)
    have h2' := mul_le_mul_of_nonneg_right hg hEn
    linarith [hTr, h2']
  -- ### the split of `𝓛̂ = 𝓛 - Transport`
  have hT : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.Transport (Work.Spaces.Dth f) z θ * Work.Spaces.Dth f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.intTransport_of hp.hint_Dth_gam
  have hsplit : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α))
      (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dth f)
      = Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α))
          (Work.Coercivity.L (Work.Spaces.Dth f)) (Work.Spaces.Dth f)
        - Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α))
            (Work.Coercivity.Transport (Work.Spaces.Dth f)) (Work.Spaces.Dth f) := by
    have h := Work.FTS.CoercivityFix.Coer1.wip_sub_left
      (ρ := Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α))
      (A := Work.Coercivity.L (Work.Spaces.Dth f))
      (B := Work.Coercivity.Transport (Work.Spaces.Dth f)) (C := Work.Spaces.Dth f)
      hp.intL_Dth_gam hT
    rw [Work.Coercivity.wip_congr_ae hae]
    show Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α))
      (fun z θ => Work.Coercivity.L (Work.Spaces.Dth f) z θ
        - Work.Coercivity.Transport (Work.Spaces.Dth f) z θ) (Work.Spaces.Dth f) = _
    exact h
  have hwc : ∀ A B : Fn,
      Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α)) A B
      = Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2
            * Work.FTS.CoercivityFix.Coer1.sig (Work.Spaces.gam α) θ) A B := by
    intro A B
    simp only [Work.Coercivity.wip, Work.FTS.CoercivityFix.Coer1.Rho]
  rw [hsplit, hwc (Work.Coercivity.L (Work.Spaces.Dth f)) (Work.Spaces.Dth f), hL,
    ← hwc (Work.Spaces.Dth f) (Work.Spaces.Dth f), hw]
  linarith [hTr']

end Work.FTS.StrongEps.EpsE4Thr.OClass
