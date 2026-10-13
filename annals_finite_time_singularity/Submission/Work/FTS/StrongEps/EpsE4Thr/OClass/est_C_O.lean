/-
# `est_C_O` — the plain `L²`-pairing of `𝓛̂` in the **open** class

`Work.FTS.CoercivityFix.Coer1.est_C` proves

  `(1/8)·E_1(f) - 6·E_1(D_θ f) ≤ ⟨𝓛̂f, f⟩_{w²}`

for `f ∈ RegQ α 2` (i.e. `C^∞` on the *strip* `z > -1`, `HkMem`, `BdryTraces`), from

* the paper's identity `(LW)`, `⟨𝓛u,u⟩_{w²} = ½⟨u,u⟩_{w²}` (the **open**-class copy
  `Coer1SO.wip_L_self_QO`, driven by `ZIBPO`);
* the transport pairing bound `⟨Transport f, f⟩_{w²} ≤ 6·E_1(D_θ f)` in the *plain* radial
  weight `w²` (`Coer1.transport_w2_bound`), which is the only place where the weight
  `sin(2θ)^{-β}` is absent and hence where the `D_θ`-energy and not the `L²`-energy bounds
  the transport term.

The route's data only carries `SmoothOpen` (the *open* quadrant `(0,∞) × (0,π/2)`), which is
*strictly weaker* than `LocData.SmoothQuad` (no flatness at `z = 0` is available; indeed
`SmoothQuad` is false for the projected slices of the route).  So this file re-runs the
estimate on the open class: `RegQo α 2 f` supplies `SmoothOpen f` and `BdryTraces α 2 f`, and
`IntPkgO α f` supplies the same `IntegrableOn` certificates with the three
`z`-integration-by-parts fields taken in the open class `Coer1SO.ZIBPO`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.StrongEps.EpsE4Thr.IntPkgO
import Submission.Work.FTS.CoercivityFix.Coer1.Estimates
import Submission.Work.FTS.CoercivityFix.Coer1SO.wip_Dz_self_le_SO

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
