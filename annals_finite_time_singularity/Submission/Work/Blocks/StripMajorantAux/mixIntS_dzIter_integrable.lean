import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.EllipticEst.Core.i0Aux.Honest
import Submission.Work.EllipticEst.Core.HkSqLHSv2Meas
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the radial slice functionals `mixIntS (D_z^r V)`

The majorant of the mixed-derivative interpolation estimate contains, for each `r ≤ k`, the
radial slice functional

`mixIntS (D_z^r V) z = w(z)² ∫_θ (D_z ∂_θ (D_z^r V) z θ)² σ_η(θ) dθ`

(`Submission/Work/EllipticEst/Core/Defs.lean`).  This module shows that this function of `z` is
integrable on `Iz = [0,∞)` as soon as `V` is `C^∞` on the open quadrant and the single function
`D_z ∂_θ V` lies in the weighted space `ℋ^k` (`Work.Spaces.HkMem`).

The argument is purely a *slicewise comparison with the `ℋ^k`-integrand*:

* for `z > 0` the derivative block `D_z ∂_θ (D_z^r V)` equals `D_z^r (D_z ∂_θ V)` (Clairaut plus
  the commutation of `∂_θ` with the iterates of `D_z` on the open quadrant);
* the square identity `(D · (w / σ^{η/2}))² = D² w² σ^{-η}` turns the slice integrand into the
  `i = r` summand of `HkIntegrand α k (D_z ∂_θ V)`, which is `≤ HkIntegrand` by
  `Work.Spaces.sq_le_HkIntegrand_z`;
* the generic honesty step `Work.EllipticEst.Core.i0Aux.integrableOn_of_slice_le` converts this
  domination (`HkMem` is exactly integrability of the `θ`-integral of `HkIntegrand`) plus
  a.e. strong measurability (from `Work.EllipticEst.Core.v2_aesm_integral`) into integrability.

Nothing here uses `sorry`; the module rests on `[propext, Classical.choice, Quot.sound]`.
-/
namespace Work.Blocks.StripMajorantAux

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-! ## Nonnegativity of the slice functional -/

/-- `mixIntS u z ≥ 0`: it is the product of the nonnegative weight `w(z)²` with the `θ`-integral
of the nonnegative integrand `(D_z ∂_θ u)² σ_η`. -/
theorem mixIntS_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ Work.EllipticEst.Core.mixIntS u z := by
  rw [Work.EllipticEst.Core.mixIntS]
  refine mul_nonneg (sq_nonneg _) (MeasureTheory.integral_nonneg_of_ae ?_)
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
    (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.EllipticEst.Core.i0Aux.thEta_nonneg_Iθ hθ))

/-! ## The `θ`-slice identity -/

/-- For `z > 0`, the derivative block `D_z ∂_θ (D_z^r V)` equals the `r`-th iterate of the fixed
block `D_z ∂_θ V`: `∂_θ` commutes with `D_z^r` on the open quadrant, and `D_z` commutes with its
own iterates. -/
theorem Dz_pth_DzIter_eq {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ)
    {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ
      = Work.Spaces.DzIter r (Work.Spaces.Dz (Work.Spaces.pth V)) z θ := by
  -- Clairaut on the open quadrant: `∂_θ (D_z^r V) = D_z^r (∂_θ V)`
  have hEq : Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter r V)))
      (Function.uncurry (Work.Spaces.DzIter r (Work.Spaces.pth V)))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall V).mp hV) r
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ1, hθ2⟩
  -- `D_z` of the two functions agrees (its `deriv` sees only a neighbourhood)
  have h1 : Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ
      = Work.Spaces.Dz (Work.Spaces.DzIter r (Work.Spaces.pth V)) z θ := by
    show z * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ
        = z * Work.Spaces.pz (Work.Spaces.DzIter r (Work.Spaces.pth V)) z θ
    rw [Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEq hmem]
  have h2' : Work.Spaces.DzIter (r + 1) (Work.Spaces.pth V)
      = Work.Spaces.DzIter r (Work.Spaces.Dz (Work.Spaces.pth V)) := by
    rw [Work.Spaces.DzIter_add_right r 1]
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
  have h2 : Work.Spaces.Dz (Work.Spaces.DzIter r (Work.Spaces.pth V)) z θ
      = Work.Spaces.DzIter r (Work.Spaces.Dz (Work.Spaces.pth V)) z θ := by
    rw [← congrFun (congrFun (Work.Spaces.DzIter_succ r (Work.Spaces.pth V)) z) θ,
      congrFun (congrFun h2' z) θ]
  rw [h1, h2]

/-- **The slice identity for the radial family.**  For `z > 0`, `mixIntS (D_z^r V) z` is the
`θ`-integral of the weighted square of the *fixed* block `D_z^r (D_z ∂_θ V)`. -/
theorem mixIntS_dzIter_slice_eq {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ)
    {z : ℝ} (hz : 0 < z) :
    Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter r (Work.Spaces.Dz (Work.Spaces.pth V)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  -- step 1: purely algebraic rewriting of the `θ`-integrand (no positivity of `z` needed)
  have h1 : Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [Work.EllipticEst.Core.mixIntS, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    simp only [Work.FTS.EllipticEst.thEta]
    rw [Work.EllipticEst.Core.i0Aux.mul_div_rpow_sq_eq
      (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) (Work.Spaces.w z)
      (Real.sin (2 * θ)) (Work.FTS.EllipticEst.sin_two_nonneg hθ) Work.Spaces.eta_pos.ne']
    ring
  rw [h1]
  -- step 2: identify the derivative block a.e. in `θ` (the endpoints are null)
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl,
    ← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2))]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
  rw [Dz_pth_DzIter_eq hV r hz hθ.1 hθ.2]

/-! ## Domination by the `ℋ^k`-integrand -/

/-- **Slicewise domination.**  For `r ≤ k` and `z > 0`, the slice functional
`mixIntS (D_z^r V) z` is bounded by the `θ`-integral of the `ℋ^k`-integrand of the fixed block
`D_z ∂_θ V`: the former is (a.e.) exactly the `i = r` summand of the latter. -/
theorem mixIntS_dzIter_le_HkIntegrand {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pth V)))
    (hr : r ≤ k) {z : ℝ} (hz : 0 < z) :
    Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z
      ≤ ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (Work.Spaces.Dz (Work.Spaces.pth V)) z θ := by
  rw [mixIntS_dzIter_slice_eq hV r hz]
  exact MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun θ => sq_nonneg _)
    (hmem.1 z (Set.mem_Ici.mpr hz.le))
    (Filter.Eventually.of_forall fun θ =>
      Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.Dz (Work.Spaces.pth V)) z θ r hr)

/-! ## Measurability in `z` -/

/-- The slice functional `mixIntS (D_z^r V)` is a.e. strongly measurable for `volume.restrict Iz`:
it is the weighted angular integral of the `C^∞`-on-the-open-quadrant function
`D_z ∂_θ (D_z^r V)`. -/
theorem aesm_mixIntS_dzIter {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have h := Work.EllipticEst.Core.v2_aesm_integral ((hV.DzIter r).pth.Dz)
    (-(Work.Spaces.eta))
  simpa only [Work.EllipticEst.Core.mixIntS, Work.FTS.EllipticEst.thEta]
    using h.aestronglyMeasurable

/-! ## The value of the `z`-integral -/

/-- The `z`-integral of the radial slice functional is bounded by the *square* of the `ℋ^k`-norm
of the fixed block `D_z ∂_θ V`. -/
theorem integral_mixIntS_dzIter_le_HkSq {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pth V)))
    (hr : r ≤ k) :
    (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
      ≤ Work.Spaces.HkSq α k (Work.Spaces.Dz (Work.Spaces.pth V)) := by
  rw [Work.Spaces.HkSq]
  refine MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => mixIntS_nonneg (Work.Spaces.DzIter r V) z)
    hmem.2 ?_
  filter_upwards [Work.EllipticEst.Core.i0Aux.ae_pos_Iz] with z hz
  exact mixIntS_dzIter_le_HkIntegrand hV hmem hr hz

/-! ## The target -/

theorem mixIntS_dzIter_integrable {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.Dz (Work.Spaces.pth V)))
    (hr : r ≤ k) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
      Work.Spaces.Iz := by
  refine Work.EllipticEst.Core.i0Aux.integrableOn_of_slice_le
    (g := Work.Spaces.Dz (Work.Spaces.pth V))
    (G := fun z : ℝ => Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
    hmem (fun z => mixIntS_nonneg (Work.Spaces.DzIter r V) z)
    (aesm_mixIntS_dzIter hV r) ?_
  filter_upwards [Work.EllipticEst.Core.i0Aux.ae_pos_Iz] with z hz
  exact mixIntS_dzIter_le_HkIntegrand hV hmem hr hz

end

end Work.Blocks.StripMajorantAux
