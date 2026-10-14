import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.ScaleClose6.HkN_sepF_le
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.FluxOpen
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.Base
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.t1SlotTermZ
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T2Sup.GenSlot
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.TransportS.T2Sup.smainBound
import Submission.Work.FTS.TransportS.T3BadAux.slot_prod_le
import Submission.Work.FTS.TransportS.T3SlotAux.Flux
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS_RegExport.RXT.radial_noDecay_le
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.L6Flux.flux_prod_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.L6Flux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## The weighted radial integration by parts with a bounded derivative -/


/-! ## The one-angle flux bound -/


/-! ## The product-measure bound -/


end Work.FTS.StrongPersist.N6Trans.L6Flux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixAux.ExcPairPm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The exceptional configuration of the level-6 `T2` slot

The summand of the Leibniz expansion in which the top pure radial slot `D_z⁵` meets a *mixed*
slot of the other function, in the one configuration (`a = 1`, `b = 5`) where the pointwise
sup at order `5` is not available.  The estimate is the `L²` Cauchy–Schwarz pairing of

* the product `D_z⁵p · D_z^bD_θ^aq · W` (square integrable with bound
  `C(γ-1)⁻¹|p|²_{ℋ⁶}|q|²_{ℋ⁶}`, the proved `T1SixAux.excDz5_mixed_pair_bound`), and
* the remaining level-6 slot `D_z^BD_θ^Ag · W` of `g`.

Since `W² = canonW (gam α)`, the weight comparison `canonW q ≤ W²` (`q ≤ γ`) makes the pairing
applicable to the canonical-weight slot pairing, and `(γ-1)^{-1/2} = √10·α^{-1/2}` gives the
admissible constant.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z canonW_mono)

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-- `canonW q ≤ W_α²` on the angular interval, for `0 < q ≤ γ`. -/
theorem canonW_le_Wt_sq {α q z θ : ℝ} (hq0 : 0 < q) (hq : q ≤ Work.Spaces.gam α)
    (hθ : θ ∈ Work.Spaces.Iθ) : canonW q z θ ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
  rw [← Work.FTS.TransportS.SlotT2.canonW_gam_eq α z θ hθ]
  exact canonW_mono hq0 hq hθ

/-- **The exceptional `L²` pairing.**  Given the square-integrability of
`D_z⁵p · D_z^bD_θ^aq · W_α` with the bound `C/(γ-1)|p|²_{ℋ⁶}|q|²_{ℋ⁶}`, the canonical-weight
pairing of that product against a level-6 slot `D_z^BD_θ^Ag` is bounded by
`√(10C)·α^{-1/2}·|p|_{ℋ⁶}|q|_{ℋ⁶}|g|_{ℋ⁶}`. -/
theorem exc_pair_pm {α q C1 : ℝ} {p qq g : ℝ → ℝ → ℝ} {b a B A : ℕ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hC1 : 0 ≤ C1)
    (hpS : Work.FTS.EllipticEst.SmoothOpen p) (hpm : Work.Spaces.HkMem α 6 p)
    (hqS : Work.FTS.EllipticEst.SmoothOpen qq) (hqm : Work.Spaces.HkMem α 6 qq)
    (hgS : Work.FTS.EllipticEst.SmoothOpen g) (hgm : Work.Spaces.HkMem α 6 g)
    (hA : 1 ≤ A) (hAB : A + B ≤ 6) (hq0 : 0 < q) (hqγ : q ≤ Work.Spaces.gam α)
    (hL2mem : Work.Spaces.L2Mem (fun z θ => Work.Spaces.DzIter 5 p z θ
      * Work.Spaces.mixed b a qq z θ * Work.Spaces.Wt α z θ))
    (hL2sq : Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter 5 p z θ
      * Work.Spaces.mixed b a qq z θ * Work.Spaces.Wt α z θ)
      ≤ C1 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 p * Work.Spaces.HkSq α 6 qq) :
    MeasureTheory.Integrable (fun p' : ℝ × ℝ => canonW q p'.1 p'.2
        * |Work.Spaces.DzIter 5 p p'.1 p'.2| * |Work.Spaces.mixed b a qq p'.1 p'.2|
        * |Work.Spaces.mixed B A g p'.1 p'.2|) pm ∧
      |∫ p', canonW q p'.1 p'.2 * |Work.Spaces.DzIter 5 p p'.1 p'.2|
          * |Work.Spaces.mixed b a qq p'.1 p'.2|
          * |Work.Spaces.mixed B A g p'.1 p'.2| ∂pm|
        ≤ Real.sqrt (10 * C1) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 p
            * Work.Spaces.HkNorm α 6 qq * Work.Spaces.HkNorm α 6 g := by
  have hgampos : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  set A1 : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.DzIter 5 p z θ
      * Work.Spaces.mixed b a qq z θ * Work.Spaces.Wt α z θ with hA1def
  set B1 : ℝ → ℝ → ℝ := fun z θ => Work.Spaces.mixed B A g z θ * Work.Spaces.Wt α z θ
    with hB1def
  have hA1val : ∀ z θ, A1 z θ = Work.Spaces.DzIter 5 p z θ
      * Work.Spaces.mixed b a qq z θ * Work.Spaces.Wt α z θ := fun z θ => by rw [hA1def]
  have hB1val : ∀ z θ, B1 z θ = Work.Spaces.mixed B A g z θ * Work.Spaces.Wt α z θ :=
    fun z θ => by rw [hB1def]
  -- ## a.e. strong measurability
  have hA1cont : ContinuousOn (Function.uncurry A1) Work.FTS.EllipticEst.Q0 := by
    rw [show Function.uncurry A1 = Function.uncurry (fun z θ => Work.Spaces.DzIter 5 p z θ
        * Work.Spaces.mixed b a qq z θ * Work.Spaces.Wt α z θ) from by
      funext p'; exact hA1val p'.1 p'.2]
    exact (((hpS.DzIter 5).continuousOn.mul (hqS.mixed b a).continuousOn).mul
      (Work.FTS.StrongPersist.N6Trans.T1SlotZ.continuousOn_Wt_Q0 α))
  have hB1cont : ContinuousOn (Function.uncurry B1) Work.FTS.EllipticEst.Q0 := by
    rw [show Function.uncurry B1 = Function.uncurry (fun z θ =>
        Work.Spaces.mixed B A g z θ * Work.Spaces.Wt α z θ) from by
      funext p'; exact hB1val p'.1 p'.2]
    exact (hgS.mixed B A).continuousOn.mul
      (Work.FTS.StrongPersist.N6Trans.T1SlotZ.continuousOn_Wt_Q0 α)
  have hA1aesm : AEStronglyMeasurable (fun p' : ℝ × ℝ => A1 p'.1 p'.2) pm :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hA1cont
  have hB1aesm : AEStronglyMeasurable (fun p' : ℝ × ℝ => B1 p'.1 p'.2) pm :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hB1cont
  -- ## the `pm`-integral of `A1²`
  have hA1slice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => (A1 z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hL2mem.1 z hz
  have hA1outer : MeasureTheory.Integrable
      (fun z => ∫ θ, (A1 z θ) ^ 2 ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hL2mem.2
  have hA1pm := Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ) (G := fun z θ => (A1 z θ) ^ 2)
    (fun z θ => sq_nonneg _) (hA1aesm.pow 2) hA1slice hA1outer
  have hA1sqmem : MeasureTheory.Integrable (fun p' : ℝ × ℝ => (A1 p'.1 p'.2) ^ 2) pm :=
    hA1pm.1
  have hA1bound : (∫ p', (A1 p'.1 p'.2) ^ 2 ∂pm)
      ≤ C1 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 p * Work.Spaces.HkSq α 6 qq := by
    rw [hA1pm.2]
    exact hL2sq
  -- ## the `pm`-integral of `B1²`
  have hB1pt : ∀ z θ : ℝ, (B1 z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
    intro z θ
    rw [hB1val z θ]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 6 g z θ A B hA hAB
  have hHkGint :=
    (Work.FTS.StrongPersist.N6Trans.Hon.integrable_HkIntegrand_prod_open hgS hgm)
  have hB1sqmem : MeasureTheory.Integrable (fun p' : ℝ × ℝ => (B1 p'.1 p'.2) ^ 2) pm :=
    MeasureTheory.Integrable.mono' hHkGint.1 (hB1aesm.pow 2)
      (Filter.Eventually.of_forall fun p' => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hB1pt p'.1 p'.2)
  have hB1bound : (∫ p', (B1 p'.1 p'.2) ^ 2 ∂pm) ≤ Work.Spaces.HkSq α 6 g := by
    have h := MeasureTheory.integral_mono hB1sqmem hHkGint.1
      (fun p' : ℝ × ℝ => hB1pt p'.1 p'.2)
    rwa [hHkGint.2] at h
  -- ## the product is integrable
  have hprod : MeasureTheory.Integrable (fun p' : ℝ × ℝ => A1 p'.1 p'.2 * B1 p'.1 p'.2) pm := by
    refine MeasureTheory.Integrable.mono' ((hA1sqmem.add hB1sqmem).const_mul (1 / 2)) ?_ ?_
    · exact hA1aesm.mul hB1aesm
    · filter_upwards with p'
      rw [Real.norm_eq_abs]
      calc |A1 p'.1 p'.2 * B1 p'.1 p'.2|
          ≤ ((A1 p'.1 p'.2) ^ 2 + (B1 p'.1 p'.2) ^ 2) / 2 :=
            Work.FTS.TransportS.T3BadAux.abs_mul_le_half_sq_add _ _
        _ = (1 / 2) * ((A1 p'.1 p'.2) ^ 2 + (B1 p'.1 p'.2) ^ 2) := by ring
  -- ## the Cauchy–Schwarz bound
  have hLpA : MeasureTheory.MemLp (fun p' : ℝ × ℝ => A1 p'.1 p'.2)
      (ENNReal.ofReal 2) pm := by
    rw [show ENNReal.ofReal 2 = (2 : ℝ≥0∞) from ENNReal.ofReal_ofNat 2]
    rw [MeasureTheory.memLp_two_iff_integrable_sq hA1aesm]
    exact hA1sqmem
  have hLpB : MeasureTheory.MemLp (fun p' : ℝ × ℝ => B1 p'.1 p'.2)
      (ENNReal.ofReal 2) pm := by
    rw [show ENNReal.ofReal 2 = (2 : ℝ≥0∞) from ENNReal.ofReal_ofNat 2]
    rw [MeasureTheory.memLp_two_iff_integrable_sq hB1aesm]
    exact hB1sqmem
  have hCS := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := pm) (p := 2) (q := 2)
    (f := fun p' : ℝ × ℝ => A1 p'.1 p'.2) (g := fun p' : ℝ × ℝ => B1 p'.1 p'.2)
    Real.HolderConjugate.two_two hLpA hLpB
  have hCS' : (∫ p', |A1 p'.1 p'.2 * B1 p'.1 p'.2| ∂pm)
      ≤ Real.sqrt (C1 / (Work.Spaces.gam α - 1))
        * (Work.Spaces.HkNorm α 6 p * Work.Spaces.HkNorm α 6 qq)
        * Work.Spaces.HkNorm α 6 g := by
    have h1 : (∫ p', |A1 p'.1 p'.2 * B1 p'.1 p'.2| ∂pm)
        ≤ (∫ p', |A1 p'.1 p'.2| ^ (2 : ℝ) ∂pm) ^ (1 / (2 : ℝ))
          * (∫ p', |B1 p'.1 p'.2| ^ (2 : ℝ) ∂pm) ^ (1 / (2 : ℝ)) := by
      have h1' := hCS
      simpa only [Real.norm_eq_abs, abs_of_nonneg, abs_mul, Real.sqrt_nonneg] using h1'
    have h2 : (∫ p', |A1 p'.1 p'.2| ^ (2 : ℝ) ∂pm)
        = ∫ p', (A1 p'.1 p'.2) ^ 2 ∂pm := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p' => ?_)
      show |A1 p'.1 p'.2| ^ (2 : ℝ) = (A1 p'.1 p'.2) ^ 2
      rw [Real.rpow_two, sq_abs]
    have h3 : (∫ p', |B1 p'.1 p'.2| ^ (2 : ℝ) ∂pm)
        = ∫ p', (B1 p'.1 p'.2) ^ 2 ∂pm := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p' => ?_)
      show |B1 p'.1 p'.2| ^ (2 : ℝ) = (B1 p'.1 p'.2) ^ 2
      rw [Real.rpow_two, sq_abs]
    rw [h2, h3] at h1
    have hnn : 0 ≤ C1 / (Work.Spaces.gam α - 1) := div_nonneg hC1 hgampos.le
    have hupper : (∫ p', (A1 p'.1 p'.2) ^ 2 ∂pm) ^ (1 / (2 : ℝ))
        ≤ Real.sqrt (C1 / (Work.Spaces.gam α - 1))
          * (Work.Spaces.HkNorm α 6 p * Work.Spaces.HkNorm α 6 qq) := by
      rw [← Real.sqrt_eq_rpow]
      have hsq : Work.Spaces.HkSq α 6 p = (Work.Spaces.HkNorm α 6 p) ^ 2 :=
        (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 p)).symm
      have hsq' : Work.Spaces.HkSq α 6 qq = (Work.Spaces.HkNorm α 6 qq) ^ 2 :=
        (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 qq)).symm
      have hprod2 : C1 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 p
          * Work.Spaces.HkSq α 6 qq
          = (C1 / (Work.Spaces.gam α - 1))
            * ((Work.Spaces.HkNorm α 6 p * Work.Spaces.HkNorm α 6 qq) ^ 2) := by
        rw [hsq, hsq']; ring
      calc Real.sqrt (∫ p', (A1 p'.1 p'.2) ^ 2 ∂pm)
          ≤ Real.sqrt (C1 / (Work.Spaces.gam α - 1)
              * Work.Spaces.HkSq α 6 p * Work.Spaces.HkSq α 6 qq) :=
            Real.sqrt_le_sqrt hA1bound
        _ = Real.sqrt (C1 / (Work.Spaces.gam α - 1))
              * (Work.Spaces.HkNorm α 6 p * Work.Spaces.HkNorm α 6 qq) := by
            rw [hprod2, Real.sqrt_mul hnn,
              Real.sqrt_sq (mul_nonneg (Work.Spaces.HkNorm_nonneg α 6 p)
                (Work.Spaces.HkNorm_nonneg α 6 qq))]
    have hlow : (∫ p', (B1 p'.1 p'.2) ^ 2 ∂pm) ^ (1 / (2 : ℝ))
        ≤ Work.Spaces.HkNorm α 6 g := by
      rw [← Real.sqrt_eq_rpow]
      calc Real.sqrt (∫ p', (B1 p'.1 p'.2) ^ 2 ∂pm)
          ≤ Real.sqrt (Work.Spaces.HkSq α 6 g) := Real.sqrt_le_sqrt hB1bound
        _ = Work.Spaces.HkNorm α 6 g := rfl
    calc (∫ p', |A1 p'.1 p'.2 * B1 p'.1 p'.2| ∂pm)
        ≤ (∫ p', (A1 p'.1 p'.2) ^ 2 ∂pm) ^ (1 / (2 : ℝ))
          * (∫ p', (B1 p'.1 p'.2) ^ 2 ∂pm) ^ (1 / (2 : ℝ)) := h1
      _ ≤ (Real.sqrt (C1 / (Work.Spaces.gam α - 1))
            * (Work.Spaces.HkNorm α 6 p * Work.Spaces.HkNorm α 6 qq))
          * Work.Spaces.HkNorm α 6 g := by
          have hBnn : (0 : ℝ) ≤ (∫ p', (B1 p'.1 p'.2) ^ 2 ∂pm) ^ (1 / (2 : ℝ)) :=
            Real.rpow_nonneg (MeasureTheory.integral_nonneg fun p' => sq_nonneg _) _
          have hXnn : (0 : ℝ) ≤ Real.sqrt (C1 / (Work.Spaces.gam α - 1))
              * (Work.Spaces.HkNorm α 6 p * Work.Spaces.HkNorm α 6 qq) :=
            mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Work.Spaces.HkNorm_nonneg α 6 p)
              (Work.Spaces.HkNorm_nonneg α 6 qq))
          exact mul_le_mul hupper hlow hBnn hXnn
  -- ## the weight comparison, integrability and the final arithmetic
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      canonW q z θ * |Work.Spaces.DzIter 5 p z θ| * |Work.Spaces.mixed b a qq z θ|
        * |Work.Spaces.mixed B A g z θ| ≤ |A1 z θ * B1 z θ| := by
    intro z θ hz hθ hθ2
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
    have hw := canonW_le_Wt_sq (z := z) hq0 hqγ hθI
    have hWt0 : 0 ≤ Work.Spaces.Wt α z θ := by
      rw [Work.Spaces.Wt, Work.Spaces.w, Work.Spaces.wTheta]
      exact mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))
        (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI) _)
    rw [hA1val z θ, hB1val z θ, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hWt0]
    have hnn : (0 : ℝ) ≤ |Work.Spaces.DzIter 5 p z θ| * |Work.Spaces.mixed b a qq z θ|
        * |Work.Spaces.mixed B A g z θ| := by positivity
    nlinarith [hw, hnn, sq_nonneg (Work.Spaces.Wt α z θ)]
  have hnorm : ∀ᵐ p' ∂pm,
      ‖canonW q p'.1 p'.2 * |Work.Spaces.DzIter 5 p p'.1 p'.2|
          * |Work.Spaces.mixed b a qq p'.1 p'.2|
          * |Work.Spaces.mixed B A g p'.1 p'.2|‖ ≤ |A1 p'.1 p'.2 * B1 p'.1 p'.2| :=
    Work.FTS.TransportS.ae_of_forall_Qd (P := fun p' : ℝ × ℝ =>
      ‖canonW q p'.1 p'.2 * |Work.Spaces.DzIter 5 p p'.1 p'.2|
          * |Work.Spaces.mixed b a qq p'.1 p'.2|
          * |Work.Spaces.mixed B A g p'.1 p'.2|‖ ≤ |A1 p'.1 p'.2 * B1 p'.1 p'.2|)
      (fun z θ hz hθ hθ2 => by
        have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.le, hθ2.le⟩
        change ‖canonW q z θ * |Work.Spaces.DzIter 5 p z θ| * |Work.Spaces.mixed b a qq z θ|
            * |Work.Spaces.mixed B A g z θ|‖ ≤ |A1 z θ * B1 z θ|
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (canonW_nonneg hθI) (abs_nonneg _))
            (abs_nonneg _)) (abs_nonneg _))]
        exact hpt z θ hz hθ hθ2)
  have htarget : MeasureTheory.Integrable (fun p' : ℝ × ℝ => canonW q p'.1 p'.2
      * |Work.Spaces.DzIter 5 p p'.1 p'.2| * |Work.Spaces.mixed b a qq p'.1 p'.2|
      * |Work.Spaces.mixed B A g p'.1 p'.2|) pm := by
    refine MeasureTheory.Integrable.mono' hprod.abs ?_ hnorm
    refine Work.Spaces.aesm_of_continuousOn_Qd _
      ((((Work.FTS.TransportS.SlotT2.continuousOn_canonW q).mul
        ((hpS.DzIter 5).continuousOn.abs)).mul ((hqS.mixed b a).continuousOn.abs)).mul
        ((hgS.mixed B A).continuousOn.abs))
  refine ⟨htarget, ?_⟩
  have hstep : |∫ p', canonW q p'.1 p'.2 * |Work.Spaces.DzIter 5 p p'.1 p'.2|
        * |Work.Spaces.mixed b a qq p'.1 p'.2|
        * |Work.Spaces.mixed B A g p'.1 p'.2| ∂pm|
      ≤ ∫ p', |A1 p'.1 p'.2 * B1 p'.1 p'.2| ∂pm := by
    refine le_trans (MeasureTheory.abs_integral_le_integral_abs (μ := pm)) ?_
    refine MeasureTheory.integral_mono_ae htarget.abs hprod.abs ?_
    filter_upwards [hnorm] with p' hp'
    rw [Real.norm_eq_abs] at hp'
    exact hp'
  have hsq10 : Real.sqrt (C1 / (Work.Spaces.gam α - 1))
      = Real.sqrt C1 * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)) := by
    have h1 : Real.sqrt (C1 / (Work.Spaces.gam α - 1))
        = Real.sqrt C1 / Real.sqrt (Work.Spaces.gam α - 1) :=
      Real.sqrt_div hC1 (Work.Spaces.gam α - 1)
    rw [h1, div_eq_mul_inv, ← one_div,
      Work.FTS.StrongPersist.N6Trans.SixAux.one_div_sqrt_gam_sub_one hα]
    ring
  rw [hsq10] at hCS'
  refine le_trans (le_trans hstep hCS') ?_
  have hle : Real.sqrt C1 * Real.sqrt 10 = Real.sqrt (10 * C1) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 10)]
    ring
  have hnn : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hA0 : 0 ≤ Work.Spaces.HkNorm α 6 p := Work.Spaces.HkNorm_nonneg α 6 p
  have hB0 : 0 ≤ Work.Spaces.HkNorm α 6 qq := Work.Spaces.HkNorm_nonneg α 6 qq
  have hC0 : 0 ≤ Work.Spaces.HkNorm α 6 g := Work.Spaces.HkNorm_nonneg α 6 g
  have h1 : Real.sqrt C1 * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ))
      ≤ Real.sqrt (10 * C1) * α ^ (-(1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_right (le_of_eq hle) hnn
  calc Real.sqrt C1 * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ))
        * (Work.Spaces.HkNorm α 6 p * Work.Spaces.HkNorm α 6 qq)
        * Work.Spaces.HkNorm α 6 g
      = (Real.sqrt C1 * Real.sqrt 10 * α ^ (-(1 / 2 : ℝ)))
        * ((Work.Spaces.HkNorm α 6 p * Work.Spaces.HkNorm α 6 qq)
          * Work.Spaces.HkNorm α 6 g) := by ring
    _ ≤ (Real.sqrt (10 * C1) * α ^ (-(1 / 2 : ℝ)))
        * ((Work.Spaces.HkNorm α 6 p * Work.Spaces.HkNorm α 6 qq)
          * Work.Spaces.HkNorm α 6 g) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg (mul_nonneg hA0 hB0) hC0)
    _ = Real.sqrt (10 * C1) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 6 p
        * Work.Spaces.HkNorm α 6 qq * Work.Spaces.HkNorm α 6 g := by ring

/-- The exceptional constant for the configuration `(b,a) = (1,1)`. -/
noncomputable def excC11 : ℝ :=
  Classical.choose (Work.FTS.StrongPersist.N6Trans.T1SixAux.excDz5_mixed_pair_bound (b := 1) (a := 1) (by norm_num) (by norm_num))

theorem excC11_pos : 0 < excC11 :=
  (Classical.choose_spec (Work.FTS.StrongPersist.N6Trans.T1SixAux.excDz5_mixed_pair_bound (b := 1) (a := 1) (by norm_num) (by norm_num))).1

theorem excC11_spec {α : ℝ} {p qq : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hpS : Work.FTS.EllipticEst.SmoothOpen p) (hpm : Work.Spaces.HkMem α 6 p)
    (hqS : Work.FTS.EllipticEst.SmoothOpen qq) (hqm : Work.Spaces.HkMem α 6 qq) :
    Work.Spaces.L2Mem (fun z θ => Work.Spaces.DzIter 5 p z θ
        * Work.Spaces.mixed 1 1 qq z θ * Work.Spaces.Wt α z θ) ∧
      Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter 5 p z θ
          * Work.Spaces.mixed 1 1 qq z θ * Work.Spaces.Wt α z θ)
        ≤ excC11 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 p * Work.Spaces.HkSq α 6 qq :=
  (Classical.choose_spec (Work.FTS.StrongPersist.N6Trans.T1SixAux.excDz5_mixed_pair_bound (b := 1) (a := 1) (by norm_num) (by norm_num))).2
    α p qq hα hα1 hpS hpm hqS hqm

/-- The exceptional constant for the configuration `(b,a) = (0,2)`. -/
noncomputable def excC02 : ℝ :=
  Classical.choose (Work.FTS.StrongPersist.N6Trans.T1SixAux.excDz5_mixed_pair_bound (b := 0) (a := 2) (by norm_num) (by norm_num))

theorem excC02_pos : 0 < excC02 :=
  (Classical.choose_spec (Work.FTS.StrongPersist.N6Trans.T1SixAux.excDz5_mixed_pair_bound (b := 0) (a := 2) (by norm_num) (by norm_num))).1

theorem excC02_spec {α : ℝ} {p qq : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hpS : Work.FTS.EllipticEst.SmoothOpen p) (hpm : Work.Spaces.HkMem α 6 p)
    (hqS : Work.FTS.EllipticEst.SmoothOpen qq) (hqm : Work.Spaces.HkMem α 6 qq) :
    Work.Spaces.L2Mem (fun z θ => Work.Spaces.DzIter 5 p z θ
        * Work.Spaces.mixed 0 2 qq z θ * Work.Spaces.Wt α z θ) ∧
      Work.Spaces.L2Sq (fun z θ => Work.Spaces.DzIter 5 p z θ
          * Work.Spaces.mixed 0 2 qq z θ * Work.Spaces.Wt α z θ)
        ≤ excC02 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 p * Work.Spaces.HkSq α 6 qq :=
  (Classical.choose_spec (Work.FTS.StrongPersist.N6Trans.T1SixAux.excDz5_mixed_pair_bound (b := 0) (a := 2) (by norm_num) (by norm_num))).2
    α p qq hα hα1 hpS hpm hqS hqm

end Work.FTS.StrongPersist.N6Trans.SixAux
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.SixAux.fluxSix =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.SixAux

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary helpers -/

/-- The canonical weight is continuous in `z` on `(0,∞)` at a fixed angle. -/
theorem continuousOn_canonW_z (q θ : ℝ) :
    ContinuousOn (fun z : ℝ => Work.FTS.TransportS.SlotT2.canonW q z θ) (Set.Ioi 0) := by
  have hw : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have h : ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) :=
      ((continuous_const.add continuous_id).continuousOn.pow 2).div
        (continuous_id.continuousOn.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
    refine (h.pow 2).congr fun z _ => ?_
    simp only [Work.Spaces.w, Pi.pow_apply]
  have h2 : ContinuousOn
      (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)) (Set.Ioi 0) :=
    hw.mul (continuousOn_const :
      ContinuousOn (fun _ : ℝ => (Real.sin (2 * θ)) ^ (-q)) (Set.Ioi 0))
  refine h2.congr fun z _ => ?_
  rfl

/-- The canonical slot product, written as a product of square roots. -/
theorem abs_canonW_mul_mul_eq {q z θ X Y : ℝ}
    (hρ : 0 ≤ Work.FTS.TransportS.SlotT2.canonW q z θ) :
    |Work.FTS.TransportS.SlotT2.canonW q z θ * X * Y|
      = Real.sqrt (Work.FTS.TransportS.SlotT2.canonW q z θ * X ^ 2)
        * Real.sqrt (Work.FTS.TransportS.SlotT2.canonW q z θ * Y ^ 2) := by
  have hs : Real.sqrt (Work.FTS.TransportS.SlotT2.canonW q z θ)
      * Real.sqrt (Work.FTS.TransportS.SlotT2.canonW q z θ)
      = Work.FTS.TransportS.SlotT2.canonW q z θ := Real.mul_self_sqrt hρ
  rw [abs_mul, abs_mul, abs_of_nonneg hρ, Real.sqrt_mul hρ, Real.sqrt_mul hρ,
    Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
  conv_lhs => rw [← hs]
  ring

/-- `√A √B ≤ (A + B)/2` for nonnegative `A`, `B`. -/
theorem sqrt_mul_sqrt_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Real.sqrt A * Real.sqrt B ≤ (A + B) / 2 := by
  have h := two_mul_le_add_sq (Real.sqrt A) (Real.sqrt B)
  rw [Real.sq_sqrt hA, Real.sq_sqrt hB] at h
  linarith

/-- **The pointwise Cauchy–Schwarz bound for the canonical pairing.** -/
theorem abs_mul_canonW_mul_le {q M X Y hh z θ : ℝ}
    (hρ : 0 ≤ Work.FTS.TransportS.SlotT2.canonW q z θ) (hM : 0 ≤ M) (hb : |hh| ≤ M) :
    |hh * (Work.FTS.TransportS.SlotT2.canonW q z θ * X * Y)|
      ≤ (M / 2) * (Work.FTS.TransportS.SlotT2.canonW q z θ * X ^ 2
          + Work.FTS.TransportS.SlotT2.canonW q z θ * Y ^ 2) := by
  rw [abs_mul, abs_canonW_mul_mul_eq hρ]
  calc |hh| * (Real.sqrt (Work.FTS.TransportS.SlotT2.canonW q z θ * X ^ 2)
        * Real.sqrt (Work.FTS.TransportS.SlotT2.canonW q z θ * Y ^ 2))
      ≤ M * ((Work.FTS.TransportS.SlotT2.canonW q z θ * X ^ 2
          + Work.FTS.TransportS.SlotT2.canonW q z θ * Y ^ 2) / 2) :=
        mul_le_mul hb
          (sqrt_mul_sqrt_le (mul_nonneg hρ (sq_nonneg _)) (mul_nonneg hρ (sq_nonneg _)))
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hM
    _ = (M / 2) * (Work.FTS.TransportS.SlotT2.canonW q z θ * X ^ 2
          + Work.FTS.TransportS.SlotT2.canonW q z θ * Y ^ 2) := by ring

/-! ## The main theorem -/


end

end Work.FTS.StrongPersist.N6Trans.SixAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Asm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.T1SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false


/-- The `θ`-slice of the `canonW q`-weighted square of the slot `mixed b a g` is integrable,
for `q ∈ [0,γ]` (`q ≤ η` when `a = 0`). -/
theorem slotSliceIntegrable (α q : ℝ) {g : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen g) (hmg : Work.Spaces.HkMem α 6 g)
    {a b : ℕ} (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hab : a + b ≤ 6) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn (fun θ : ℝ =>
      canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) Work.Spaces.Iθ := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
  · subst h0
    rw [show (fun θ : ℝ => canonW q 0 θ * (Work.Spaces.mixed b a g 0 θ) ^ 2)
        = fun _ => (0 : ℝ) from by
      funext θ; rw [canonW_zero_z, zero_mul]]
    exact integrableOn_zero
  · refine MeasureTheory.Integrable.mono' (hmg.1 z hz)
      (Work.FTS.TransportS.SlotT2.mslot_slice_aesm (q := q) hG b a hz0) ?_
    filter_upwards [Work.FTS.TransportS.ae_mem_Ioo_Iθ] with θ hθ
    rw [Real.norm_of_nonneg (mul_nonneg (canonW_nonneg ⟨hθ.1.le, hθ.2.le⟩) (sq_nonneg _))]
    exact Work.FTS.StrongPersist.N6Trans.SixAux.canonW_mixed_le6_open α q g a b hqγ hqη hab hθ

/-- The `z`-marginal of the `canonW q`-weighted square of the slot `mixed b a g` is
integrable, and the `z`-outer iterated integral is at most `HkSq α 6 g`. -/
theorem slotEnergyZOuter (α q : ℝ) {g : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen g) (hmg : Work.Spaces.HkMem α 6 g)
    {a b : ℕ} (hq0 : 0 ≤ q) (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hab : a + b ≤ 6) :
    MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) ≤ Work.Spaces.HkSq α 6 g := by
  obtain ⟨hint, _, hbound⟩ :=
    Work.FTS.StrongPersist.N6Trans.SixAux.slotEnergy6 α q g a b hq0 hqγ hqη hab hG hmg
  refine ⟨hint.integral_prod_left, ?_⟩
  rw [MeasureTheory.integral_integral_swap
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (f := fun z θ => canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) hint]
  exact hbound

end Work.FTS.StrongPersist.N6Trans.T1SixAux
end
end
