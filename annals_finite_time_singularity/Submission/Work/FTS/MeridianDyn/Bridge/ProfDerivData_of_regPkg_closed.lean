import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.MeridianDyn.Bridge.mainLHS_sub_N_eq
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.OpenPkg.l12_open_bundle
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.SolutionDelivery.DatumEuler
import Submission.Work.SolutionDelivery.Scaling.Main
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Stability.CutFactorFderivZero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.MeridianDyn.Bridge

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# The *closed* derivation data of the meridian bridge: the two `L₁₂`-facts from `RegPkg`

`Work.FTS.MeridianDyn.Bridge.ProfDerivData_of_regPkg` assembles the seven fields of
`Work.FTS.MeridianDyn.ProfDerivData α Φ g` from the regularity package `RegPkg α g`, the
`C²`-regularity of `Φ` on the open quadrant, and two analytic facts about the `L₁₂`-density of
the *full* profile `F_τ = F_* + g(·,·,τ)`:

* `hL12i` — the density `L12dens K (F_τ)` is integrable on `(0,∞)`;
* `hL12c` — it is continuous at every `z > 0`.

This module derives those two facts from `RegPkg` alone (plus `0 < α ≤ 1`), so that the consumer
`ProfDerivData_of_regPkg_closed` needs no extra hypothesis.

## The route

Fix `τ > 0` and write `h = g(·,·,τ)`.  `RegPkg` supplies

* `SmoothOpen h` — the `τ`-slice of the joint interior `C^∞` of `RegPkg.smooth` is `C^∞` on the
  open quadrant (`smoothOpen_slice_of_regPkg`);
* `HkMem α 4 h` (`RegPkg.mem4`), i.e. honest weighted integrability of the `ℋ⁴`-integrand.

The `L₁₂`-density is *additive* in the profile (`Work.FTS.LocData.L12dens_add_of_integrableOn`),
the angular slices of `F_*` are integrable on `Iθ` for **every** `s`
(`Work.Stability.integrableOn_slice_Fstar`), and those of `h` are integrable for `s > 0`
(`Pieces.sliceK_integrableOn`, whose only inputs are `SmoothOpen h` and `HkMem α 4 h`).  Hence

  `L12dens K (F_* + h) s = L12dens K (F_*) s + L12dens K h s`     for `s > 0`,

and it suffices to treat the two summands separately:

* `L12dens K (F_*) = α·F_{*,rad}(s)/s` (`Construction.L12dens_Fstar`), hence integrable on
  `(0,∞)` (`Pieces.L12dens_Fstar_integrableOn`) and continuous at every `z > 0`;
* for `h`, `L12dens K h = 3·F_*(h)(s)/s` (`Elliptic.L12dens_eq_three_Fstar_div`,
  `H2.L12dens_eq_FM_K`), and

  - `s ↦ F_*(h)(s)/s` is integrable on `(0,∞)`
    (`EllipticEst.UopHk.integrableOn_Fstar_div_of_smoothOpen_Hk`);
  - `F_*(h)` is `C³` on `(0,∞)`
    (`EllipticEst.UopHk.contDiffOn_Fstar_of_smoothOpen_Hk`), so `s ↦ 3·F_*(h)(s)/s` is
    continuous at every `z > 0`.

The interior class is the *honest* one: neither step needs the analytic neighbourhood class
`SmoothNbhd` nor the neighbourhood-quadrant class `SmoothQuad` (which the localised data of the
route never satisfies), only `SmoothOpen` and `HkMem`.
-/

section Facts

/-- The `L₁₂`-density of a datum of the interior class — `C^∞` on the open quadrant and `ℋ⁴` —
is integrable on `(0,∞)`.  Via `L12dens = 3 F_*/s` this is the integrability of the weighted
angular moment `F_*(h)(s)/s`. -/
theorem integrableOn_L12dens_of_smoothOpen_Hk {α : ℝ} {h : ℝ → ℝ → ℝ}
    (hSO : Work.FTS.EllipticEst.SmoothOpen h) (hHk : Work.Spaces.HkMem α 4 h) :
    MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K h) (Set.Ioi (0 : ℝ)) := by
  have hdiv : MeasureTheory.IntegrableOn
      (fun r : ℝ => Work.Elliptic.Fstar h r / r) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.EllipticEst.UopHk.integrableOn_Fstar_div_of_smoothOpen_Hk α 4 h hSO hHk
  have hEll : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens h) (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.IntegrableOn.congr_fun (hdiv.const_mul 3)
      (fun r _ => (Work.Elliptic.L12dens_eq_three_Fstar_div h r).symm) measurableSet_Ioi
  exact hEll.congr_fun (fun r _ => Work.FTS.H2.L12dens_eq_FM_K h r) measurableSet_Ioi

/-- The `L₁₂`-density of a datum of the interior class is continuous at every `z > 0`: it is
`3·F_*(h)(s)/s`, and the angular moment `F_*(h)` is `C³` on `(0,∞)`. -/
theorem continuousAt_L12dens_of_smoothOpen_Hk {α : ℝ} {h : ℝ → ℝ → ℝ}
    (hSO : Work.FTS.EllipticEst.SmoothOpen h) (hHk : Work.Spaces.HkMem α 4 h)
    {z : ℝ} (hz : 0 < z) :
    ContinuousAt (Work.FM.L12dens Work.Spaces.K h) z := by
  have hFstar :=
    Work.FTS.EllipticEst.UopHk.contDiffOn_Fstar_of_smoothOpen_Hk α 4 h hSO hHk
      (by norm_num : 1 ≤ 4)
  have hcontF : ContinuousAt (Work.Elliptic.Fstar h) z :=
    hFstar.continuousOn.continuousAt (isOpen_Ioi.mem_nhds hz)
  have hcont : ContinuousAt (fun s : ℝ => (3 * Work.Elliptic.Fstar h s) / s) z :=
    (hcontF.const_mul 3).div continuousAt_id (ne_of_gt hz)
  refine hcont.congr (Eventually.of_forall fun s => ?_)
  rw [← Work.FTS.H2.L12dens_eq_FM_K h s, Work.Elliptic.L12dens_eq_three_Fstar_div h s]
  ring

/-- The `L₁₂`-density of the full profile `F_* + h` is integrable on `(0,∞)` for a datum `h` of
the interior class: the density is additive on `(0,∞)` and the two summands are separately
integrable. -/
theorem integrableOn_L12dens_Fstar_add {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {h : ℝ → ℝ → ℝ} (hSO : Work.FTS.EllipticEst.SmoothOpen h)
    (hHk : Work.Spaces.HkMem α 4 h) :
    MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.Fstar α z θ + h z θ))
      (Set.Ioi (0 : ℝ)) := by
  have hA : MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α)) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn hα hα1 0 le_rfl
  have hB : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K h) (Set.Ioi (0 : ℝ)) :=
    integrableOn_L12dens_of_smoothOpen_Hk hSO hHk
  refine (hA.add hB).congr_fun (fun s hs => ?_) measurableSet_Ioi
  exact (Work.FTS.LocData.L12dens_add_of_integrableOn Work.Spaces.K
    (Work.Stability.integrableOn_slice_Fstar α hα s)
    (Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn hSO hHk s hs)).symm

/-- The `L₁₂`-density of the full profile `F_* + h` is continuous at every `z > 0` for a datum
`h` of the interior class: on a neighbourhood of `z` (which lies in `(0,∞)`) the density is the
sum of the two densities just discussed. -/
theorem continuousAt_L12dens_Fstar_add {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {h : ℝ → ℝ → ℝ} (hSO : Work.FTS.EllipticEst.SmoothOpen h)
    (hHk : Work.Spaces.HkMem α 4 h) {z : ℝ} (hz : 0 < z) :
    ContinuousAt
      (Work.FM.L12dens Work.Spaces.K (fun z θ => Work.Construction.Fstar α z θ + h z θ)) z := by
  -- the density of the reference profile `F_*` is the elementary function `α·F_{*,rad}(s)/s`
  have hA : ContinuousAt
      (Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α)) z := by
    have hfun : Work.FM.L12dens Work.Spaces.K (Work.Construction.Fstar α)
        = fun s : ℝ => α * (Work.FM.Fstar s / s) :=
      funext fun s => Work.Construction.L12dens_Fstar hα hα1 s
    rw [hfun]
    have hF : ContinuousAt (fun s : ℝ => Work.FM.Fstar s) z := by
      have h1 : ContinuousAt (fun s : ℝ => (2 : ℝ) * s) z :=
        continuousAt_const.mul continuousAt_id
      have h2 : ContinuousAt (fun s : ℝ => ((1 : ℝ) + s) ^ 2) z :=
        (continuousAt_const.add continuousAt_id).pow 2
      have h3 : ((1 : ℝ) + z) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
      have h4 : ContinuousAt (fun s : ℝ => (2 : ℝ) * s / (1 + s) ^ 2) z := h1.div h2 h3
      have heq : (fun s : ℝ => (2 : ℝ) * s / (1 + s) ^ 2) = Work.FM.Fstar := rfl
      rwa [heq] at h4
    exact (hF.div continuousAt_id (ne_of_gt hz)).const_mul α
  have hB : ContinuousAt (Work.FM.L12dens Work.Spaces.K h) z :=
    continuousAt_L12dens_of_smoothOpen_Hk hSO hHk hz
  refine (hA.add hB).congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds hz] with s hs
  exact (Work.FTS.LocData.L12dens_add_of_integrableOn Work.Spaces.K
    (Work.Stability.integrableOn_slice_Fstar α hα s)
    (Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn hSO hHk s hs)).symm

end Facts


end Work.FTS.MeridianDyn.Bridge
