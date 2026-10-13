/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.FTS.ClassC.Gsing_add_mul_open`

The singular term

  `Gsing α F = -(1/(4α))·L₁₂(F) + Ḡ(α,F)`,
  `Ḡ(α,F)(z) = -(3/(4α))·z^{-5/α}·∫_0^z s^{(5-α)/α}·F_*(F)(s) ds`

of §'The singular term' of Elgindi's paper is **linear in its source** on the open-quadrant
class of the `ClassC` design: for `f, h` smooth on the open quadrant (`SmoothOpen`) that lie
honestly in `ℋ⁴` (`Work.Spaces.HkMem α 4`), and every `c : ℝ`,

  `Gsing α (f + c·h) = Gsing α f + c·Gsing α h`   on `(0,∞)`.

This is the `SmoothOpen` version of the delivered `Work.FTS.EllSol.Gsing_add_mul`, whose
smoothness hypothesis is the *analytic-neighbourhood* class `Work.FTS.LocData.SmoothQuad`
(smoothness on `z > -1`).  Everything the linearity argument actually consumes is available
from `SmoothOpen` alone:

* `F_*` is additive on slices whose product with `sinθcos²θ` is integrable
  (`Work.FTS.EllSol.Fstar_add_mul`), and that slice-integrability is
  `Work.FTS.EllipticEst.Cores.integrableOn_slice_mul_sinCos2` from continuity on the open
  quadrant together with level-`0` honesty;
* the `L₁₂`-density is additive (`Work.FTS.EllSol.L12dens_add_mul`), its angular slices being
  integrable by `Work.FTS.EllSol.L12dens_slice_integrable`;
* `L₁₂` is additive on the open tail (`Work.FTS.EllSol.L12_add_mul`), which needs the density
  to be integrable on `(z,∞)`: for `SmoothOpen` data this is the density form of
  `Work.FTS.EllipticEst.UopHk.integrableOn_Fstar_div_of_smoothOpen_Hk`, re-proved here as
  `integrableOn_L12dens_smoothOpen` (`L12dens = 3·F_*/s` by
  `Work.Elliptic.L12dens_eq_three_Fstar_div`);
* `Ḡ` is additive (`Work.FTS.EllSol.Gbar_add_mul`), which needs the interval integrability of
  `s ↦ s^{(5-α)/α}·F_*(F)(s)` on `(0,z]`; that is the open-quadrant interval-integrability
  lemma `Work.FTS.ClassC.intervalIntegrable_rpow_Fstar_open` (the `SmoothOpen` analogue of
  `Work.FTS.EllSol.intervalIntegrable_rpow_Fstar`).

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.ClassC.intervalIntegrable_rpow_Fstar_open
import Submission.Work.FTS.EllSol.EllAux2
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Open-quadrant facts about the ingredients of `Gsing` -/

/-- **The `L₁₂`-density of `SmoothOpen` `ℋ⁴`-data is integrable on `(0,∞)`.**  This is the
density form of `Work.FTS.EllipticEst.UopHk.integrableOn_Fstar_div_of_smoothOpen_Hk` under
`L12dens = 3·F_*/s` (`Work.Elliptic.L12dens_eq_three_Fstar_div`). -/
theorem integrableOn_L12dens_smoothOpen {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α 4 F) :
    MeasureTheory.IntegrableOn (Work.Elliptic.L12dens F) (Set.Ioi 0) := by
  have h := Work.FTS.EllipticEst.UopHk.integrableOn_Fstar_div_of_smoothOpen_Hk α 4 F hso hmem
  exact MeasureTheory.IntegrableOn.congr_fun (h.const_mul 3)
    (fun r _ => (Work.Elliptic.L12dens_eq_three_Fstar_div F r).symm) measurableSet_Ioi

/-! ## The main theorem -/

/-- **`Gsing` is additive on the open-quadrant class.**  For `α > 0`, `f h` smooth on the open
quadrant with `HkMem α 4`, and `c : ℝ`, the singular term of §'The singular term' is linear:
`Gsing α (f + c·h) z = Gsing α f z + c·Gsing α h z` for every `z > 0`. -/
theorem Gsing_add_mul_open {α : ℝ} (hα : 0 < α) {f h : Work.FTS.Galerkin.Fn} (c : ℝ) {z : ℝ}
    (hz : 0 < z)
    (hsof : Work.FTS.EllipticEst.SmoothOpen f) (hmemf : Work.Spaces.HkMem α 4 f)
    (hsoh : Work.FTS.EllipticEst.SmoothOpen h) (hmemh : Work.Spaces.HkMem α 4 h) :
    Work.Elliptic.Gsing α (fun z θ => f z θ + c * h z θ) z
      = Work.Elliptic.Gsing α f z + c * Work.Elliptic.Gsing α h z := by
  have hmemf0 : Work.Spaces.HkMem α 0 f :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 0) (l := 4) (by norm_num)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hsof) hmemf
  have hmemh0 : Work.Spaces.HkMem α 0 h :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (α := α) (k := 0) (l := 4) (by norm_num)
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall h).mp hsoh) hmemh
  -- additivity of `F_*`
  have hFs : ∀ s, 0 < s → Work.Elliptic.Fstar (fun z θ => f z θ + c * h z θ) s
      = Work.Elliptic.Fstar f s + c * Work.Elliptic.Fstar h s := fun s hs =>
    Work.FTS.EllSol.Fstar_add_mul
      (Work.FTS.EllipticEst.Cores.integrableOn_slice_mul_sinCos2 hsof.continuousOn hmemf0 hs)
      (Work.FTS.EllipticEst.Cores.integrableOn_slice_mul_sinCos2 hsoh.continuousOn hmemh0 hs)
  -- additivity of the `L₁₂`-densities
  have hdens : ∀ s, 0 < s → Work.Elliptic.L12dens (fun z θ => f z θ + c * h z θ) s
      = Work.Elliptic.L12dens f s + c * Work.Elliptic.L12dens h s := fun s hs =>
    Work.FTS.EllSol.L12dens_add_mul
      (Work.FTS.EllSol.L12dens_slice_integrable hsof.continuousOn hmemf hs)
      (Work.FTS.EllSol.L12dens_slice_integrable hsoh.continuousOn hmemh hs)
  -- integrability of the densities on `(z,∞)`
  have hDf : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens f) (Set.Ioi z) :=
    (integrableOn_L12dens_smoothOpen (α := α) hsof hmemf).mono_set (Set.Ioi_subset_Ioi hz.le)
  have hDh : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens h) (Set.Ioi z) :=
    (integrableOn_L12dens_smoothOpen (α := α) hsoh hmemh).mono_set (Set.Ioi_subset_Ioi hz.le)
  -- interval integrability of the `Ḡ`-integrands
  have hIf := intervalIntegrable_rpow_Fstar_open α hα f hsof hmemf hz
  have hIh := intervalIntegrable_rpow_Fstar_open α hα h hsoh hmemh hz
  rw [Work.Elliptic.Gsing, Work.Elliptic.Gsing, Work.Elliptic.Gsing]
  rw [show Work.Elliptic.Gstar α (fun z θ => f z θ + c * h z θ) z
      = -(1 / (4 * α)) * Work.Elliptic.L12 (fun z θ => f z θ + c * h z θ) z from rfl]
  rw [Work.FTS.EllSol.L12_add_mul hz.le hdens hDf hDh,
      Work.FTS.EllSol.Gbar_add_mul hz hFs hIf hIh]
  rw [show Work.Elliptic.Gstar α f z = -(1 / (4 * α)) * Work.Elliptic.L12 f z from rfl,
      show Work.Elliptic.Gstar α h z = -(1 / (4 * α)) * Work.Elliptic.L12 h z from rfl]
  ring

end Work.FTS.ClassC
