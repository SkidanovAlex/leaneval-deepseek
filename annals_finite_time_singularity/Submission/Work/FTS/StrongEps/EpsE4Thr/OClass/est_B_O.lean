/-
# `est_B_O` — the `η`-weighted `L²`-pairing of `𝓛̂` in the **open** class

`Work.FTS.CoercivityFix.Coer1.est_B` proves

  `(47/100)·E_η(f) ≤ ⟨𝓛̂f, f⟩_{w² sin^{-η}}`

for `f ∈ RegQ α 2` (i.e. `C^∞` on the *strip* `z > -1`, `HkMem`, `BdryTraces`), using the two
elementary integrations by parts of §6:

* the paper's identity `(LW)`, `⟨𝓛u,u⟩_{w²σ} = ½⟨u,u⟩_{w²σ}` (here the **open**-class copy
  `Coer1SO.wip_L_self_QO`, driven by `ZIBPO`);
* the angular-transport bound `⟨3D_θu/(1+z),u⟩_{w²sin^{-β}} ≤ 3|β-1|·⟨u,u⟩_{w²sin^{-β}}`
  (here the **open**-class copy `wip_transport_le_O`, driven by `SmoothOpen`).

The route's data only carries `SmoothOpen` (the *open* quadrant), so this file re-runs the
estimate on the open class: `RegQo α 2 f` (which supplies `SmoothOpen f` and `BdryTraces α 2 f`,
the two hypotheses the angular `z`-free limits need) together with the open-class
integrability bundle `IntPkgO α f`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgO
import Submission.Work.FTS.StrongEps.EpsE4Thr.wip_transport_le_O
import Submission.Work.FTS.CoercivityFix.Coer1SO.wip_Dz_self_le_SO
import Submission.Work.FTS.CoercivityFix.Coer1.Estimates
import Submission.Work.Coercivity.Defs

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
set_option maxHeartbeats 1600000

/-- **The `η`-weighted `L²`-pairing of `𝓛̂` in the open class.**
`⟨𝓛̂f, f⟩_{w² sin^{-η}} ≥ (47/100)·E_η(f)`: `(LW)` gives `⟨𝓛f,f⟩ = ½E_η(f)`, and the transport
pairing costs at most `3|η-1| = 3/100` of `E_η(f)`.

This is `Work.FTS.CoercivityFix.Coer1.est_B` with the interior class `RegQ α 2` replaced by the
open class `RegQo α 2` and the integrability bundle `IntPkg` by `IntPkgO`. -/
theorem est_B_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {f : Fn}
    (hf : RegQo α 2 f) (hp : IntPkgO α f) :
    (47 / 100) * Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta f
      ≤ Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (Work.FTS.CoercivityFix.Lhat f) f := by
  obtain ⟨hso, hm, hb⟩ := hf
  -- ### the integrability certificates in the `w²σ` shape of the two `wip` identities
  have h0 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ ^ 2 * Work.FTS.CoercivityFix.Coer1.Rho
        Work.Spaces.eta z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine (hp.sqDzEta 0 (by norm_num)).congr (MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p hpp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.Spaces.DzIter_zero]
  have h1 := Work.FTS.CoercivityFix.Coer1.to_h1 (β := Work.Spaces.eta) h0
  have h2 := Work.FTS.CoercivityFix.Coer1.to_tr_hint2 (β := Work.Spaces.eta) h0
  have hL2 := Work.FTS.CoercivityFix.Coer1.to_h2 (β := Work.Spaces.eta) hp.intL_f_eta
  have hT2 := Work.FTS.CoercivityFix.Coer1.to_tr_hint (β := Work.Spaces.eta) hp.hint_f_eta
  -- ### the angular vanishing limits at the `η` exponent, from the `γ` ones
  have hvan := Work.FTS.CoercivityFix.Coer1.hvan_eta_of_gam α hα
    (fun z hz => ((hb 0 0 (by norm_num)).2 z hz).1)
    (fun z hz => ((hb 0 0 (by norm_num)).2 z hz).2)
  -- ### the two Euler–Lagrange inputs
  have hL := Work.FTS.CoercivityFix.Coer1SO.wip_L_self_QO f hp.zibp_f
    (Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta) h1 hL2
  have hw : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta) f f
      = Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta f :=
    Work.FTS.CoercivityFix.Coer1.wip_Rho_self Work.Spaces.eta f
  have hTr := wip_transport_le_O Work.Spaces.eta f hso hvan.1 hvan.2 hT2 h2
  have hTr' : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      (Work.Coercivity.Transport f) f
      ≤ (3 / 100) * Work.FTS.CoercivityFix.Coer1.En Work.Spaces.eta f := by
    rw [hw] at hTr
    have heta : (3 : ℝ) * |Work.Spaces.eta - 1| ≤ 3 / 100 := by
      rw [Work.Spaces.eta]
      rw [show |(99 : ℝ) / 100 - 1| = 1 / 100 by norm_num]
      norm_num
    have hEn := Work.FTS.CoercivityFix.Coer1.En_nonneg Work.Spaces.eta f
    have h2' := mul_le_mul_of_nonneg_right heta hEn
    linarith [hTr, h2']
  -- ### the split of `𝓛̂ = 𝓛 - Transport`
  have hT : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.Transport f z θ * f z θ * Work.FTS.CoercivityFix.Coer1.Rho
        Work.Spaces.eta z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Work.FTS.CoercivityFix.Coer1.intTransport_of hp.hint_f_eta
  have hsplit : Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
        (Work.FTS.CoercivityFix.Lhat f) f
      = Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (Work.Coercivity.L f) f
        - Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
          (Work.Coercivity.Transport f) f := by
    have h := Work.FTS.CoercivityFix.Coer1.wip_sub_left
      (ρ := Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      (A := Work.Coercivity.L f) (B := Work.Coercivity.Transport f) (C := f)
      hp.intL_f_eta hT
    show Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta)
      (fun z θ => Work.Coercivity.L f z θ - Work.Coercivity.Transport f z θ) f = _
    exact h
  have hwc : ∀ A B : Fn, Work.Coercivity.wip (Work.FTS.CoercivityFix.Coer1.Rho Work.Spaces.eta) A B
      = Work.Coercivity.wip
          (fun z θ => Work.Spaces.w z ^ 2 * Work.FTS.CoercivityFix.Coer1.sig Work.Spaces.eta θ)
          A B := by
    intro A B
    simp only [Work.Coercivity.wip, Work.FTS.CoercivityFix.Coer1.Rho]
  rw [hsplit, hwc (Work.Coercivity.L f) f, hL, ← hwc f f, hw]
  linarith [hTr']

end Work.FTS.StrongEps.EpsE4Thr
