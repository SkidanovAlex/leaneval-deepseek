import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemUD
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemGradUD
import Submission.Work.FTS.EllipticEst.Dispatch.aeLeftLimitD
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices
import Submission.Work.FTS.EllipticEst.Honest.Step1G.AeClear.AeEnergyWAux
import Submission.Work.FTS.EllipticEst.Cores.Pieces.ae_hksq_le_of_energy
import Submission.Work.FTS.EllipticEst.Honest.Step1G.AeClear.AeW2Energy

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

theorem AeUHkLe : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkSq α 0 u
        ≤ C * (Work.Spaces.HkSq α 0 G
            + α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := ae_hksq_le_of_energy
  obtain ⟨C₂, hC₂pos, hC₂⟩ := AeW2Energy
  refine ⟨C₁ * C₂, mul_pos hC₁pos hC₂pos, fun α u G h => ?_⟩
  have hYmem : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2) Work.Spaces.Iz :=
    integrableOn_wSq_sgY h
  have hup := hC₁ α u G h hYmem
  have hen : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2)
      ≤ C₂ * (Work.Spaces.HkSq α 0 G
          + α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) := by
    have h2 := hC₂ α u G h
    rwa [show (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth u z θ) ^ 2 * (Work.Spaces.w z) ^ 2)
        = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2 from ?_] at h2
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    rw [MeasureTheory.integral_mul_const, mul_comm]
  calc Work.Spaces.HkSq α 0 u
      ≤ C₁ * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2) := hup
    _ ≤ C₁ * (C₂ * (Work.Spaces.HkSq α 0 G
          + α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u))) :=
        mul_le_mul_of_nonneg_left hen (le_of_lt hC₁pos)
    _ = (C₁ * C₂) * (Work.Spaces.HkSq α 0 G
          + α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) := by ring

end Work.FTS.EllipticEst.Cores.Pieces
