/-
# `est_A_O` — the `η`-weighted `D_z`-pairing of `𝓛̂` in the **open** class

`Work.FTS.CoercivityFix.Coer1.est_A` proves

  `(47/100)·E_η(D_z f) - (E_η(f) + 4·E_γ(D_θ f) + (1/8)·E_η(D_z f)) ≤ ⟨D_z(𝓛̂f), D_z f⟩_{w²sin^{-η}}`

for `f ∈ RegQ α 2` (i.e. `C^∞` on the *strip* `z > -1`, `HkMem`, `BdryTraces`), by splitting
`D_z(𝓛̂f) = 𝓛̂(D_z f) + Ê₂f` and combining

* the coercivity of `𝓛̂` on `D_z f` — the paper's identity `(LW)` plus the angular-transport bound;
* the commutator defect `Ê₂f`, dominated by Cauchy–Schwarz and two Young inequalities.

The route's data only carries `SmoothOpen` (the *open* quadrant `(0,∞) × (0,π/2)`), which is
*strictly weaker* than `LocData.SmoothQuad` (no flatness at `z = 0` is available; indeed
`SmoothQuad` is false for the projected slices of the route).  So this file re-runs the estimate
on the open class, with the open-class versions of the three ingredients:

* `RegQo α 2 f` in place of `RegQ α 2 f` (supplying `SmoothOpen f` and `BdryTraces α 2 f`);
* `IntPkgO α f` in place of `IntPkg α f` (the same `IntegrableOn` certificates, with the three
  `z`-integration-by-parts fields in the open class `Coer1SO.ZIBPO`);
* `Coer1SO.wip_L_self_QO` for `(LW)`, `EpsE4Thr.wip_transport_le_O` for the transport bound, and
  `StrongPersist.H6Aux.Dz_Lhat_of_open` for the commutator identity.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgO
import Submission.Work.FTS.CoercivityFix.Coer1.Estimates
import Submission.Work.FTS.StrongEps.EpsE4Thr.wip_transport_le_O
import Submission.Work.FTS.CoercivityFix.Coer1SO.wip_Dz_self_le_SO
import Submission.Work.FTS.StrongPersist.H6Aux.LhatCommOpen

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

/-- **The coercivity of `𝓛̂` on the `η`-slot `D_z`, in the open class.**
The open-class twin of `Work.FTS.CoercivityFix.Coer1.est_A`, with `RegQ α 2` replaced by
`RegQo α 2` and the integrability bundle `IntPkg` by its open counterpart `IntPkgO`. -/
theorem est_A_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {f : Work.FTS.Galerkin.Fn}
    (hf : Work.FTS.StrongEps.EpsE4Thr.RegQo α 2 f)
    (hIP : Work.FTS.StrongEps.EpsE4Thr.IntPkgO α f) :
    (47 / 100) * Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta (Work.Spaces.Dz f)
      - (Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta f
          + 4 * Work.FTS.CoercivityFix.Coer1.En (Work.Spaces.gam α) (Work.Spaces.Dth f)
          + (1 / 8) * Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta (Work.Spaces.Dz f))
      ≤ Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f) := by
  have hp := hIP
  obtain ⟨hso, hm, hb⟩ := hf
  -- ## the `𝓛̂`-pairing of `D_z f`
  have hsoDz : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz f) := hso.Dz
  have hvan := Work.FTS.CoercivityFix.Coer1.hvan_eta_of_gam α hα
    (fun z hz => ((hb 0 1 (by norm_num)).2 z hz).1)
    (fun z hz => ((hb 0 1 (by norm_num)).2 z hz).2)
  have h1 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dz f z θ) ^ 2 * Work.Spaces.w z ^ 2
        * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q (A := fun z θ =>
      (Work.Spaces.DzIter 1 f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ)
      (hp.sqDzEta 1 (by norm_num)) (fun z θ => by
        simp only [Work.FTS.CoercivityFix.Coer1.Rho, Work.Spaces.DzIter_succ,
          Work.Spaces.DzIter_zero]; ring)
  have h2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.L (Work.Spaces.Dz f) z θ * Work.Spaces.Dz f z θ
        * Work.Spaces.w z ^ 2 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q (A := fun z θ =>
      Work.Coercivity.L (Work.Spaces.Dz f) z θ * Work.Spaces.Dz f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ)
      hp.intL_Dz_eta (fun z θ => by simp only [Work.FTS.CoercivityFix.Coer1.Rho]; ring)
  have h3 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
        * Work.Spaces.Dth (Work.Spaces.Dz f) z θ * Work.Spaces.Dz f z θ / (1 + z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q (A := fun z θ =>
      Work.Spaces.Dth (Work.Spaces.Dz f) z θ * Work.Spaces.Dz f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ / (1 + z))
      hp.hint_Dz_eta (fun z θ => by simp only [Work.FTS.CoercivityFix.Coer1.Rho,
        Work.FTS.CoercivityFix.Coer1.sig]; ring)
  have h4 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
        * (Work.Spaces.Dz f z θ) ^ 2)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q h1 (fun z θ => by
      simp only [Work.FTS.CoercivityFix.Coer1.sig]; ring)
  have h5 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.Transport (Work.Spaces.Dz f) z θ * Work.Spaces.Dz f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q (A := fun z θ =>
      3 * (Work.Spaces.Dth (Work.Spaces.Dz f) z θ * Work.Spaces.Dz f z θ
        * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ / (1 + z)))
      (hp.hint_Dz_eta.const_mul 3) (fun z θ => by
        simp only [Work.Coercivity.Transport]; ring)
  have hwc : ∀ A B : Fn, Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta) A B
      = Work.Coercivity.wip (fun z θ => Work.Spaces.w z ^ 2
          * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ) A B :=
    fun A B => rfl
  have hwDz : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
        (Work.Spaces.Dz f) (Work.Spaces.Dz f)
      = Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta (Work.Spaces.Dz f) :=
    Work.FTS.CoercivityFix.Coer1.wip_Rho_self Work.Spaces.eta (Work.Spaces.Dz f)
  have hL0 := Work.FTS.CoercivityFix.Coer1SO.wip_L_self_QO (Work.Spaces.Dz f) hp.zibp_Dz
    (Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta) h1 h2
  have hTr := Work.FTS.StrongEps.EpsE4Thr.wip_transport_le_O Work.Spaces.eta (Work.Spaces.Dz f)
    hsoDz hvan.1 hvan.2 h3 h4
  have hTr' : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      (Work.Coercivity.Transport (Work.Spaces.Dz f)) (Work.Spaces.Dz f)
      ≤ (3 / 100) * Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta (Work.Spaces.Dz f) := by
    rw [hwDz] at hTr
    have heta : (3 : ℝ) * |Work.Spaces.eta - 1| ≤ 3 / 100 := by
      rw [Work.Spaces.eta]
      rw [show |(99 : ℝ) / 100 - 1| = 1 / 100 by norm_num]
      norm_num
    have hEn := Work.FTS.CoercivityFix.Coer1.En_nonneg Work.Spaces.eta (Work.Spaces.Dz f)
    have h2' := mul_le_mul_of_nonneg_right heta hEn
    linarith [hTr, h2']
  have hL : (47 / 100) * Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta (Work.Spaces.Dz f)
      ≤ Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f) := by
    have hsplit : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
        (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f)
        = Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
            (Work.Coercivity.L (Work.Spaces.Dz f)) (Work.Spaces.Dz f)
          - Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
              (Work.Coercivity.Transport (Work.Spaces.Dz f)) (Work.Spaces.Dz f) := by
      have h := Work.FTS.CoercivityFix.Coer1.wip_sub_left
        (ρ := Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
        (A := Work.Coercivity.L (Work.Spaces.Dz f))
        (B := Work.Coercivity.Transport (Work.Spaces.Dz f)) (C := Work.Spaces.Dz f)
        hp.intL_Dz_eta h5
      show Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
        (fun z θ => Work.Coercivity.L (Work.Spaces.Dz f) z θ
          - Work.Coercivity.Transport (Work.Spaces.Dz f) z θ) (Work.Spaces.Dz f) = _
      exact h
    rw [hsplit, hwc (Work.Coercivity.L (Work.Spaces.Dz f)) (Work.Spaces.Dz f), hL0,
      ← hwc (Work.Spaces.Dz f) (Work.Spaces.Dz f), hwDz]
    linarith [hTr']
  -- ## the `D_z`-commutator defect
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f) z θ
        = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f) z θ
          + Work.FTS.CoercivityFix.E2hat f z θ := by
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iz_pos] with z hz
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_restrict_Iθ_mem_Ioo] with θ hθ
    exact Work.FTS.StrongPersist.H6Aux.Dz_Lhat_of_open Work.FTS.EllipticEst.isOpen_Q0 hso
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩) hz
  have hsplitE : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f)
      = Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f)) (Work.Spaces.Dz f)
        + Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
            (Work.FTS.CoercivityFix.E2hat f) (Work.Spaces.Dz f) := by
    rw [Work.Coercivity.wip_congr_ae hae]
    exact Work.Coercivity.wip_add_left (ρ := Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      (g := Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f))
      (h := Work.FTS.CoercivityFix.E2hat f) (k := Work.Spaces.Dz f)
      hp.intLhat_Dz_eta hp.intE2hat_Dz_eta
  have hU0 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q (A := fun z θ =>
      (Work.Spaces.DzIter 0 f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ)
      (hp.sqDzEta 0 (by norm_num)) (fun z θ => by
        simp only [Work.Spaces.DzIter_zero])
  have hDη : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dth f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q (A := fun z θ =>
      (Work.Spaces.mixed 0 1 f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ)
      (hp.sqMixedEta 1 0 (by norm_num) (by norm_num)) (fun z θ => by
        simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero,
          Work.Spaces.DthIter_succ])
  have hDγ : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dth f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q (A := fun z θ =>
      (Work.Spaces.mixed 0 1 f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho (Work.Spaces.gam α) z θ)
      (hp.sqMixedGam 1 0 (by norm_num) (by norm_num)) (fun z θ => by
        simp only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero,
          Work.Spaces.DthIter_succ])
  have hG : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dz f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.integrableOn_congr_fun_Q (A := fun z θ =>
      (Work.Spaces.DzIter 1 f z θ) ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta z θ)
      (hp.sqDzEta 1 (by norm_num)) (fun z θ => by
        simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero])
  have hE := Work.FTS.CoercivityFix.Coer1.E2hat_wip_lower α hα hp.intE2hat_Dz_eta hU0 hDγ hG
  rw [hsplitE]
  linarith [hL, hE]

end Work.FTS.StrongEps.EpsE4Thr.OClass
