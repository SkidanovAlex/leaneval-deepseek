import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.HkMemGradU
import Submission.Work.FTS.EllipticEst.Honest.Step1G.AeClear.AeW2Energy
import Submission.Work.FTS.EllipticEst.Honest.Yc.HonSliceRightTendstoYc
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceMomentIdentity
import Submission.Work.FTS.LocDataExt.LocG5
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6.Majorant6
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.StrongPersist.QangSq6Full
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.T1Q.SlotPtQ
import Submission.Work.H2W.momentChainAe
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Stability.ZcutSmoothCompact
-- ===== merged: Submission.Work.FTS.EllipticEst.Cores.Pieces.AeW2Energy =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.Pieces

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# `AeW2Energy` — the plain-`w²` angular energy of the a.e. class

The estimate `∫_z ∫_θ (∂_θu)² w(z)² ≤ C (|G|²_{ℋ⁰} + α² |D_z u|²_{ℋ⁰})` for a datum
`AeData α u G` of the almost-everywhere class of the level-`0` elliptic estimate of
T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the incompressible
Euler equations on `ℝ³`*, Annals of Math. **194** (2021) (Step 1 of Proposition `prop:H2`).

The proof runs the proved truncated radial energy *identity*
`Work.FTS.EllipticEst.H2W.AeW.aeTruncWHon` for the cut-off family `cut n` and then passes to
the limit `n → ∞`.
-/

/-! ## Elementary radial weight facts on a compact sub-interval of `(0,∞)` -/

/-! ## The domination of the truncation error integrands on the support of the cut-off -/

/-! ## Two elementary slice-integrability transfer lemmas -/

/-! ## The truncated `w²`-weighted energy inequality -/

end Work.FTS.EllipticEst.Cores.Pieces
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Honest.Step1G.AeClear.AeUHkLe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.Pieces

set_option autoImplicit false

/-!
# `AeUHkLe` — the `u`-half of Step 1 of `prop:H2` in the almost-everywhere class

The estimate

`HkSq α 0 u ≤ C · (HkSq α 0 G + α² HkSq α 0 (z ∂_z u))`

for a datum `AeData α u G` of the weak (almost-everywhere) class of the level-`0` elliptic
estimate of T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021) (Step 1 of
Proposition `prop:H2`), for a universal constant `C`.

## Route

Two already-proved estimates are combined.

* the **`σ`-upgrade** `Work.FTS.EllipticEst.Cores.Pieces.ae_hksq_le_of_energy`: the
  `σ`-weighted mass `HkSq α 0 u = ∫_z w z² ∫_θ u² σ` (with `σ = sin(2θ)^{-η}`) is controlled by
  the *unweighted* angular energy `∫_z w z² ∫_θ (∂_θu)²`, at the price of a universal constant —
  provided that the angular energy is honest;
* the **`w²`-weighted angular energy estimate** `Work.FTS.EllipticEst.Cores.Pieces.AeW2Energy`:
  `∫_z ∫_θ (∂_θu)² w z² ≤ C (HkSq α 0 G + α² HkSq α 0 (z∂_zu))`.

The only ingredient not contained in those two statements is the *honesty* of the unweighted
angular energy `z ↦ w z² ∫_θ (∂_θu(z,θ))²`, i.e. that the Bochner integral appearing in
`AeW2Energy` is the honest one (otherwise its left-hand side would be the junk value `0`, and the
two estimates could not be combined).  It is obtained here from the a.e. slice bound
`AngAWeak.ae_sgY_le` (`sgY u z ≤ dBnd α u G z + 6 sgU u z`, i.e. the constrained slice Poincaré
gap `9 ∫_θ u² ≤ ∫_θ (∂_θu)²` combined with the slice self-form of `Lzero` and the `AM–GM` bound
on the source pairing): its majorant is `w²`-integrable because `dBnd` is built from the
`ℋ⁰`-integrands of `G`, `z²∂_zzu`, `z∂_zu` (fields of `AeData`) and `sgU` is `w²`-integrable by
`Work.Spaces.HkMem α 0 u` (the `u`-half of Step 1, already in the tree as
`Dispatch.hkMem_uM`).
-/

/-- **The unweighted angular energy of a datum of the a.e. class is honest**:
`z ↦ w z² · ∫_θ (∂_θu(z,θ))²` is integrable on `Iz = [0,∞)`.

This is the honesty input of `ae_hksq_le_of_energy`.  The a.e. majorant `dBnd + 6 sgU` is
`AngAWeak.ae_sgY_le`; its `w²`-integrability comes from the `ℋ⁰`-memberships of `G`,
`z²∂_zzu`, `z∂_zu` (fields of `AeData`) and of `u`. -/
theorem integrableOn_wSq_sgY {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgY u z)
      Work.Spaces.Iz := by
  have hmu : Work.Spaces.HkMem α 0 u := Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G h
  have hmg : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) :=
    Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h
  have hC := Work.FTS.EllipticEst.H2W.AeProof.ae_continuousOn_slice h
    (Work.FTS.EllipticEst.Dispatch.aeLeftLimitD α u G h)
  -- the dominating function
  have hd : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.dBnd α u G z
        + 6 * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgU u z))
      Work.Spaces.Iz :=
    (Work.FTS.EllipticEst.AngAWeak.integrableOn_wSq_dBnd h hmu hmg).add
      ((Work.FTS.EllipticEst.AngAWeak.integrableOn_wSq_sgU h hmu).1.const_mul 6)
  -- the a.e. pointwise bound
  have hbound : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgY u z
        ≤ (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.dBnd α u G z
          + 6 * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgU u z) := by
    have hIz : (MeasureTheory.volume.restrict Work.Spaces.Iz : MeasureTheory.Measure ℝ)
        = MeasureTheory.volume.restrict (Set.Ioi 0) := by
      rw [Work.Spaces.Iz]
      exact MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
    rw [hIz]
    filter_upwards [Work.FTS.EllipticEst.AngAWeak.ae_sgY_le h hmu hmg hC] with z hz
    have h1 := mul_le_mul_of_nonneg_left hz (sq_nonneg (Work.Spaces.w z))
    linarith [h1]
  -- the a.e. strong measurability of the integrand
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun z => (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgY u z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    Work.FTS.EllipticEst.AngAWeak.aesm_wSq_sgY (by
      have hpth : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth u p.1 p.2)
          Work.FTS.EllipticEst.AngAWeak.Qd :=
        (Work.FTS.EllipticEst.AngAWeak.contDiffOn_uncurry_pth_succ
            Work.FTS.EllipticEst.AngAWeak.isOpen_Qd (n := 0)
            (by simpa only [Work.FTS.EllipticEst.AngAWeak.Qd] using h.smooth 1)).continuousOn_zero
      exact hpth.mul Work.FTS.EllipticEst.AngAWeak.continuousOn_w_Qd)
  refine MeasureTheory.Integrable.mono' hd hmeas ?_
  filter_upwards [hbound] with z hz
  have hnn : 0 ≤ Work.FTS.EllipticEst.AngAWeak.sgY u z := by
    simp only [Work.FTS.EllipticEst.AngAWeak.sgY]
    exact MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hnn)]
  exact hz


end Work.FTS.EllipticEst.Cores.Pieces
end
end
