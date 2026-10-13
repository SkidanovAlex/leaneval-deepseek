import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.Core.i0Aux.Basic
import Submission.Work.EllipticEst.Core.i0Aux.Honest
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.ClassC.NormPieces.prodIntegrableNonneg
import Submission.Work.FTS.EllSol.PkgK5.TraceEngine.SlotEngineBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5.TraceEngine

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! # The three level-`0` slots of `TraceEngine.slotBounds`

The generic product-form transfer (Tonelli) and its three instances: the slot `D_z(D_z^rV)` of
`HkSq α k (D_zV)`, the slot `∂_θ²(D_z^rV)` of `HkSq α k (∂_θ²V)` and the slot `D_z²(D_z^rV)` of
`HkSq α k (D_z²V)`. -/

/-- If the `θ`-slice integrands of the level-`0` radial slot of `F` are honest, then the
product-mode integral of the same integrand is honest and bounded by `B`. -/
theorem slotAux_slotProdCore {B : ℝ} {F : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry (fun z θ : ℝ =>
      (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hslice : ∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ =>
      (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hnn : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      0 ≤ (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
    (hint : IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz)
    (hval : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) ≤ B) :
    IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (F p.1 p.2) ^ 2) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2) ≤ B := by
  obtain ⟨hInt, hval₀⟩ := Work.FTS.ClassC.NormPieces.prodIntegrableNonneg hcont hslice hnn hint
  have hInt' : Integrable (Function.uncurry (fun z θ : ℝ =>
      (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ))
      ((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    rw [slotAux_volume_restrict_dom]; exact hInt
  have heq : ∀ p ∈ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
      (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2
        = Function.uncurry (fun z θ : ℝ =>
            (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) p := by
    rintro ⟨z, θ⟩ hp
    show (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ * (F z θ) ^ 2
      = (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ
    ring
  have hae : (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (F p.1 p.2) ^ 2)
      =ᵐ[(volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)]
      (Function.uncurry (fun z θ : ℝ =>
        (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)) :=
    MeasureTheory.ae_restrict_of_forall_mem slotAux_measurableSet_dom heq
  refine ⟨hInt'.congr hae.symm, ?_⟩
  calc (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2)
      = ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, Function.uncurry (fun z θ : ℝ =>
          (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) p :=
        MeasureTheory.integral_congr_ae hae
    _ = ∫ p, Function.uncurry (fun z θ : ℝ =>
          (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) p
          ∂((volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := rfl
    _ = ∫ p, Function.uncurry (fun z θ : ℝ =>
          (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ) p
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
        rw [slotAux_volume_restrict_dom]
    _ = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ := hval₀
    _ ≤ B := hval

/-- The `D_z`-slot of `D_zV` at radial level `r ≤ k`. -/
theorem slotAux_slotZ_prod {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hd : Work.Spaces.HkMem α k (Work.Spaces.Dz V)) (hr : r ≤ k) :
    IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2
          * (Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
        ≤ Work.Spaces.HkSq α k (Work.Spaces.Dz V) := by
  have hcont : ContinuousOn (Function.uncurry (fun z θ : ℝ =>
      (Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ =>
        (Work.Spaces.DzIter r (Work.Spaces.Dz V) p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      Work.EllipticEst.Core.i0Aux.continuousOn_dzIter_weight (g := Work.Spaces.Dz V) hV.Dz r
    refine h1.congr ?_
    intro p hp
    show (Work.Spaces.Dz (Work.Spaces.DzIter r V) p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2
      = (Work.Spaces.DzIter r (Work.Spaces.Dz V) p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2
    rw [slotAux_Dz_iter_comm_apply r V p.1 p.2]
  have hslice : ∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
    intro z hz
    have h1 := Work.EllipticEst.Core.i0Aux.integrableOn_slice_summand
      (g := Work.Spaces.Dz V) hV.Dz hd hr hz
    refine h1.congr (Filter.Eventually.of_forall fun θ => ?_)
    show (Work.Spaces.DzIter r (Work.Spaces.Dz V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ
      = (Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ
    rw [slotAux_Dz_iter_comm_apply r V z θ]
  have hnn : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      0 ≤ (Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ :=
    fun z θ _ hθ => mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Work.EllipticEst.Core.i0Aux.thEta_nonneg_Iθ hθ)
  have hpt : ∀ z : ℝ, Work.EllipticEst.Core.dIntS (Work.Spaces.DzIter r V) z
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    intro z
    rw [Work.EllipticEst.Core.dIntS, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    ring
  have hint : IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz :=
    (Work.EllipticEst.Core.i0Aux.dIntS_integrableOn (V := V) hV hd hr).congr
      (Filter.Eventually.of_forall fun z => hpt z)
  have hval : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) ≤ Work.Spaces.HkSq α k (Work.Spaces.Dz V) := by
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dz (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.thEta θ)
        = ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.dIntS (Work.Spaces.DzIter r V) z := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          exact (hpt z).symm
      _ ≤ Work.Spaces.HkSq α k (Work.Spaces.Dz V) :=
          Work.EllipticEst.Core.i0Aux.dIntS_integral_le_HkSq (V := V) hd hr
  exact slotAux_slotProdCore hcont hslice hnn hint hval

/-- The `∂_θ²`-slot at radial level `r ≤ k`. -/
theorem slotAux_slotT_prod {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (htt : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V)) (hr : r ≤ k) :
    IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2
          * (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
        ≤ Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V) := by
  have hcont : ContinuousOn (Function.uncurry (fun z θ : ℝ =>
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ =>
        (Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      Work.EllipticEst.Core.i0Aux.continuousOn_dzIter_weight (g := Work.Spaces.pthIter 2 V)
        hV.pth.pth r
    refine h1.congr ?_
    intro p hp
    obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    show (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2
        * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
      = (Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) p.1 p.2) ^ 2
        * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
    rw [Work.EllipticEst.Core.i0Aux.pthIter2_DzIter_comm hV hz hθ1 hθ2 r]
  have hslice : ∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
    intro z hz
    have h1 := Work.EllipticEst.Core.i0Aux.integrableOn_slice_summand
      (g := Work.Spaces.pthIter 2 V) hV.pth.pth htt hr hz
    refine h1.congr ?_
    filter_upwards [slotAux_ae_mem_Ioo_Itheta] with θ hθ
    show (Work.Spaces.DzIter r (Work.Spaces.pthIter 2 V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ
      = (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ
    rw [Work.EllipticEst.Core.i0Aux.pthIter2_DzIter_comm hV hz hθ.1 hθ.2 r]
  have hnn : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      0 ≤ (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ :=
    fun z θ _ hθ => mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Work.EllipticEst.Core.i0Aux.thEta_nonneg_Iθ hθ)
  have hpt : ∀ z : ℝ, Work.EllipticEst.Core.ttIntS (Work.Spaces.DzIter r V) z
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    intro z
    rw [Work.EllipticEst.Core.ttIntS, ← MeasureTheory.integral_const_mul,
      slotAux_pthIter_two_eq (Work.Spaces.DzIter r V)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    ring
  have hint : IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz :=
    (Work.EllipticEst.Core.i0Aux.ttIntS_integrableOn (V := V) hV htt hr).congr
      (Filter.Eventually.of_forall fun z => hpt z)
  have hval : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) ≤ Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V) := by
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pthIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.thEta θ)
        = ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ttIntS (Work.Spaces.DzIter r V) z := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          exact (hpt z).symm
      _ ≤ Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V) :=
          Work.EllipticEst.Core.i0Aux.ttIntS_integral_le_HkSq (V := V) hV htt hr
  exact slotAux_slotProdCore hcont hslice hnn hint hval

/-- The `D_z²`-slot at radial level `r ≤ k`. -/
theorem slotAux_slotD2_prod {k r : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V)
    (hdd : Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V)) (hr : r ≤ k) :
    IntegrableOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
        * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ (∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2
          * (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2)
        ≤ Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V) := by
  have hcont : ContinuousOn (Function.uncurry (fun z θ : ℝ =>
      (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ =>
        (Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      Work.EllipticEst.Core.i0Aux.continuousOn_dzIter_weight (g := Work.Spaces.DzIter 2 V)
        (hV.DzIter 2) r
    refine h1.congr ?_
    intro p hp
    show (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) p.1 p.2) ^ 2
        * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
      = (Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) p.1 p.2) ^ 2
        * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2
    rw [slotAux_DzIter_two_comm_apply r V p.1 p.2]
  have hslice : ∀ z : ℝ, 0 < z → IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
    intro z hz
    have h1 := Work.EllipticEst.Core.i0Aux.integrableOn_slice_summand
      (g := Work.Spaces.DzIter 2 V) (hV.DzIter 2) hdd hr hz
    refine h1.congr (Filter.Eventually.of_forall fun θ => ?_)
    show (Work.Spaces.DzIter r (Work.Spaces.DzIter 2 V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ
      = (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ
    rw [slotAux_DzIter_two_comm_apply r V z θ]
  have hnn : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      0 ≤ (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ :=
    fun z θ _ hθ => mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Work.EllipticEst.Core.i0Aux.thEta_nonneg_Iθ hθ)
  have hpt : ∀ z : ℝ, Work.EllipticEst.Core.ddIntS (Work.Spaces.DzIter r V) z
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
    intro z
    rw [Work.EllipticEst.Core.ddIntS, ← MeasureTheory.integral_const_mul,
      slotAux_DzIter_two_eq (Work.Spaces.DzIter r V)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    ring
  have hint : IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iz :=
    (Work.EllipticEst.Core.i0Aux.ddIntS_integrableOn (V := V) hV hdd hr).congr
      (Filter.Eventually.of_forall fun z => hpt z)
  have hval : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.thEta θ) ≤ Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V) := by
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter 2 (Work.Spaces.DzIter r V) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.thEta θ)
        = ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ddIntS (Work.Spaces.DzIter r V) z := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          exact (hpt z).symm
      _ ≤ Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V) :=
          Work.EllipticEst.Core.i0Aux.ddIntS_integral_le_HkSq (V := V) hdd hr
  exact slotAux_slotProdCore hcont hslice hnn hint hval

end Work.FTS.EllSol.PkgK5.TraceEngine
