import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Apriori.Limit.Defs
import Submission.Work.FTS.Apriori.Limit.SlotCalc
import Submission.Work.FTS.Apriori.Limit.TestQClosure
import Submission.Work.FTS.Apriori.Limit.SupportBox
import Submission.Work.FTS.Apriori.Limit.DerivVanish
import Submission.Work.FTS.Apriori.Limit.integral_pz_eq_zero
import Submission.Work.FTS.Apriori.Limit.integral_pth_eq_zero
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.Limit

set_option autoImplicit false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open Work.FTS.LocData (SmoothQuad)

theorem ae_restrict_Iz_mem_Ioi :
    ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), 0 < z := by
  rw [Work.Spaces.Iz]
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioi

theorem ae_restrict_Iθ_mem_Ioo :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
  rw [Work.Spaces.Iθ]
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := π / 2))]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

theorem ae_mem_Qd : ∀ᵐ p ∂Qμ, p ∈ Qd := by
  have h : ∀ᵐ p ∂Qμ, p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
      (s := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2))
      (measurableSet_Ioi.prod measurableSet_Ioo)).mpr
      (ae_restrict_Iz_mem_Ioi.mono (fun z hz => ae_restrict_Iθ_mem_Ioo.mono
        (fun θ hθ => ⟨hz, hθ⟩)))
  simpa [Qd] using h

/-- Integrability of a smooth function whose *closed* support is contained in that of a test
function. -/
theorem integrable_of_contDiffOn_supp {w v : ℝ → ℝ → ℝ}
    (hw : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry w) Qd) (hv : TestQ v)
    (hsupp : tsupport (Function.uncurry w) ⊆ tsupport (Function.uncurry v)) :
    Integrable (Function.uncurry w) Qμ :=
  integrable_of_continuousOn_of_support hw.continuousOn hv.2.1 hv.2.2
    ((subset_tsupport _).trans hsupp)

theorem tsupport_pz_subset {w : ℝ → ℝ → ℝ} :
    tsupport (Function.uncurry (Work.Spaces.pz w)) ⊆ tsupport (Function.uncurry w) := by
  refine (closure_mono (support_pz_subset_tsupport w)).trans ?_
  rw [IsClosed.closure_eq (isClosed_tsupport _)]

theorem tsupport_adjZ_subset {w : ℝ → ℝ → ℝ} :
    tsupport (Function.uncurry (adjZ w)) ⊆ tsupport (Function.uncurry w) := by
  refine (closure_mono (support_adjZ_subset w)).trans ?_
  rw [IsClosed.closure_eq (isClosed_tsupport _)]

theorem tsupport_pth_subset {w : ℝ → ℝ → ℝ} :
    tsupport (Function.uncurry (Work.Spaces.pth w)) ⊆ tsupport (Function.uncurry w) := by
  refine (closure_mono (support_pth_subset_tsupport w)).trans ?_
  rw [IsClosed.closure_eq (isClosed_tsupport _)]

theorem tsupport_adjTh_subset {w : ℝ → ℝ → ℝ} :
    tsupport (Function.uncurry (adjTh w)) ⊆ tsupport (Function.uncurry w) := by
  refine (closure_mono (support_adjTh_subset w)).trans ?_
  rw [IsClosed.closure_eq (isClosed_tsupport _)]

/-! ## The pointwise product rules -/

theorem pz_mul_three {u v : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u) Qd)
    (hv : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry v) Qd)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.pz (fun z θ => z * u z θ * v z θ) z θ
      = u z θ * v z θ + z * Work.Spaces.pz u z θ * v z θ
        + z * u z θ * Work.Spaces.pz v z θ := by
  have hzu : HasDerivAt (fun z' => u z' θ) (Work.Spaces.pz u z θ) z :=
    ((Work.FTS.LocData.contDiffOn_slice_z hu hθ).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
        (isOpen_Ioi.mem_nhds hz) |>.hasDerivAt
  have hzv : HasDerivAt (fun z' => v z' θ) (Work.Spaces.pz v z θ) z :=
    ((Work.FTS.LocData.contDiffOn_slice_z hv hθ).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
        (isOpen_Ioi.mem_nhds hz) |>.hasDerivAt
  have hid : HasDerivAt (fun z' : ℝ => z') (1 : ℝ) z := hasDerivAt_id z
  have h3 := hid.mul hzu
  have h4 := h3.mul hzv
  have hd : HasDerivAt (fun z' => z' * u z' θ * v z' θ)
      (u z θ * v z θ + z * Work.Spaces.pz u z θ * v z θ
        + z * u z θ * Work.Spaces.pz v z θ) z := by
    convert h4 using 1
    first | (simp only [Pi.mul_apply]; ring) | ring
  rw [Work.Spaces.pz, hd.deriv]

theorem adjZ_apply {v : ℝ → ℝ → ℝ}
    (hv : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry v) Qd)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    adjZ v z θ = -(v z θ + z * Work.Spaces.pz v z θ) := by
  have hzv : HasDerivAt (fun z' => v z' θ) (Work.Spaces.pz v z θ) z :=
    ((Work.FTS.LocData.contDiffOn_slice_z hv hθ).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
        (isOpen_Ioi.mem_nhds hz) |>.hasDerivAt
  have hid : HasDerivAt (fun z' : ℝ => z') (1 : ℝ) z := hasDerivAt_id z
  have h := hid.mul hzv
  have hd : HasDerivAt (fun z' => z' * v z' θ) (v z θ + z * Work.Spaces.pz v z θ) z := by
    convert h using 1
    first | (simp only [Pi.mul_apply]; ring) | ring
  rw [adjZ, hd.deriv]

/-! ## The elementary `z`-integration by parts -/

theorem integral_Dz_mul_adjZ {u v : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u) Qd) (hv : TestQ v) :
    ∫ p, Work.Spaces.Dz u p.1 p.2 * v p.1 p.2 ∂Qμ
      = ∫ p, u p.1 p.2 * adjZ v p.1 p.2 ∂Qμ := by
  set W : ℝ → ℝ → ℝ := fun z θ => z * u z θ * v z θ with hWdef
  have hWsm : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry W) Qd := by
    have h1 : Function.uncurry W
        = fun p : ℝ × ℝ => p.1 * Function.uncurry u p * Function.uncurry v p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h1]
    exact (contDiffOn_fst.mul hu).mul hv.1
  have hWsupp : tsupport (Function.uncurry W) ⊆ tsupport (Function.uncurry v) := by
    have h1 : Function.uncurry W
        = fun p : ℝ × ℝ => p.1 * Function.uncurry u p * Function.uncurry v p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h1]
    exact tsupport_mul_subset_right
      (f := fun p : ℝ × ℝ => p.1 * Function.uncurry u p) (g := Function.uncurry v)
  have hWcomp : HasCompactSupport (Function.uncurry W) :=
    IsCompact.of_isClosed_subset hv.2.1 (isClosed_tsupport _) hWsupp
  have hWsub : tsupport (Function.uncurry W) ⊆ Qd := fun p hp => hv.2.2 (hWsupp hp)
  have hftc : ∫ p, Work.Spaces.pz W p.1 p.2 ∂Qμ = 0 :=
    integral_pz_eq_zero hWsm hWcomp hWsub
  have hpzW : Integrable (fun p : ℝ × ℝ => Work.Spaces.pz W p.1 p.2) Qμ :=
    integrable_of_contDiffOn_supp (w := Work.Spaces.pz W) (v := v)
      (Work.FTS.LocData.contDiffOn_pz isOpen_Qd hWsm) hv
      ((tsupport_pz_subset (w := W)).trans hWsupp)
  have huv : Integrable (fun p : ℝ × ℝ => u p.1 p.2 * v p.1 p.2) Qμ := by
    refine integrable_of_contDiffOn_supp (w := fun z θ => u z θ * v z θ) (v := v) ?_ hv ?_
    · have h1 : Function.uncurry (fun z θ => u z θ * v z θ)
          = Function.uncurry u * Function.uncurry v := by
        funext p; rcases p with ⟨z, θ⟩; rfl
      rw [h1]; exact hu.mul hv.1
    · exact tsupport_mul_subset_right (f := Function.uncurry u) (g := Function.uncurry v)
  have hzu : Integrable (fun p : ℝ × ℝ => p.1 * u p.1 p.2 * Work.Spaces.pz v p.1 p.2) Qμ := by
    refine integrable_of_contDiffOn_supp
      (w := fun z θ => z * u z θ * Work.Spaces.pz v z θ) (v := v) ?_ hv ?_
    · have h1 : Function.uncurry (fun z θ => z * u z θ * Work.Spaces.pz v z θ)
          = fun p : ℝ × ℝ => p.1 * Function.uncurry u p
              * Function.uncurry (Work.Spaces.pz v) p := by
        funext p; rcases p with ⟨z, θ⟩; rfl
      rw [h1]
      exact (contDiffOn_fst.mul hu).mul (Work.FTS.LocData.contDiffOn_pz isOpen_Qd hv.1)
    · have h1 : Function.uncurry (fun z θ => z * u z θ * Work.Spaces.pz v z θ)
          = fun p : ℝ × ℝ => p.1 * Function.uncurry u p
              * Function.uncurry (Work.Spaces.pz v) p := by
        funext p; rcases p with ⟨z, θ⟩; rfl
      rw [h1]
      exact (tsupport_mul_subset_right
        (f := fun p : ℝ × ℝ => p.1 * Function.uncurry u p)
        (g := Function.uncurry (Work.Spaces.pz v))).trans
        (tsupport_pz_subset (w := v))
  have huadj : Integrable (fun p : ℝ × ℝ => u p.1 p.2 * adjZ v p.1 p.2) Qμ := by
    refine integrable_of_contDiffOn_supp (w := fun z θ => u z θ * adjZ v z θ) (v := v) ?_ hv ?_
    · have h1 : Function.uncurry (fun z θ => u z θ * adjZ v z θ)
          = Function.uncurry u * Function.uncurry (adjZ v) := by
        funext p; rcases p with ⟨z, θ⟩; rfl
      rw [h1]; exact hu.mul (TestQ_adjZ hv).1
    · exact (tsupport_mul_subset_right (f := Function.uncurry u) (g := Function.uncurry (adjZ v))).trans
        (tsupport_adjZ_subset (w := v))
  have hkey : ∀ᵐ p ∂Qμ, Work.Spaces.Dz u p.1 p.2 * v p.1 p.2
      = u p.1 p.2 * adjZ v p.1 p.2 + Work.Spaces.pz W p.1 p.2 := by
    filter_upwards [ae_mem_Qd] with p hp
    have h1 := pz_mul_three hu hv.1 hp.1 hp.2
    have h2 := adjZ_apply hv.1 hp.1 hp.2
    rw [hWdef, h1, h2, Work.Spaces.Dz]
    ring
  rw [MeasureTheory.integral_congr_ae hkey]
  rw [show (∫ p : ℝ × ℝ, u p.1 p.2 * adjZ v p.1 p.2
        + Work.Spaces.pz W p.1 p.2 ∂Qμ)
      = (∫ p, u p.1 p.2 * adjZ v p.1 p.2 ∂Qμ)
        + ∫ p, Work.Spaces.pz W p.1 p.2 ∂Qμ
    from MeasureTheory.integral_add huadj hpzW]
  rw [hftc, add_zero]


/-! ## The `θ`-product rules -/

theorem pth_mul_three {u v : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u) Qd)
    (hv : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry v) Qd)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.pth (fun z θ => Real.sin (2 * θ) * (u z θ * v z θ)) z θ
      = 2 * Real.cos (2 * θ) * (u z θ * v z θ)
        + Real.sin (2 * θ) * (Work.Spaces.pth u z θ * v z θ
          + u z θ * Work.Spaces.pth v z θ) := by
  have hzu : HasDerivAt (fun θ' => u z θ') (Work.Spaces.pth u z θ) θ :=
    ((Work.FTS.LocData.contDiffOn_slice_θ hu (by rw [Set.mem_Ioi]; exact hz)).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
        (isOpen_Ioo.mem_nhds hθ) |>.hasDerivAt
  have hzv : HasDerivAt (fun θ' => v z θ') (Work.Spaces.pth v z θ) θ :=
    ((Work.FTS.LocData.contDiffOn_slice_θ hv (by rw [Set.mem_Ioi]; exact hz)).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
        (isOpen_Ioo.mem_nhds hθ) |>.hasDerivAt
  have hsin : HasDerivAt (fun θ' => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ := by
    have h2 : HasDerivAt (fun y : ℝ => 2 * y) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul 2
    exact (Real.hasDerivAt_sin (2 * θ)).comp θ h2
  have h := hsin.mul (hzu.mul hzv)
  have hd : HasDerivAt (fun θ' => Real.sin (2 * θ') * (u z θ' * v z θ'))
      (2 * Real.cos (2 * θ) * (u z θ * v z θ)
        + Real.sin (2 * θ) * (Work.Spaces.pth u z θ * v z θ
          + u z θ * Work.Spaces.pth v z θ)) θ := by
    convert h using 1
    first | (simp only [Pi.mul_apply]; ring) | ring
  rw [Work.Spaces.pth, hd.deriv]

theorem adjTh_apply {v : ℝ → ℝ → ℝ}
    (hv : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry v) Qd)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    adjTh v z θ = -(2 * Real.cos (2 * θ) * v z θ
      + Real.sin (2 * θ) * Work.Spaces.pth v z θ) := by
  have hzv : HasDerivAt (fun θ' => v z θ') (Work.Spaces.pth v z θ) θ :=
    ((Work.FTS.LocData.contDiffOn_slice_θ hv (by rw [Set.mem_Ioi]; exact hz)).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
        (isOpen_Ioo.mem_nhds hθ) |>.hasDerivAt
  have hsin : HasDerivAt (fun θ' => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ := by
    have h2 : HasDerivAt (fun y : ℝ => 2 * y) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul 2
    exact (Real.hasDerivAt_sin (2 * θ)).comp θ h2
  have h := hsin.mul hzv
  have hd : HasDerivAt (fun θ' => Real.sin (2 * θ') * v z θ')
      (2 * Real.cos (2 * θ) * v z θ + Real.sin (2 * θ) * Work.Spaces.pth v z θ) θ := by
    convert h using 1
    first | (simp only [Pi.mul_apply]; ring) | ring
  rw [adjTh, hd.deriv]

/-! ## The elementary `θ`-integration by parts -/

theorem integral_Dth_mul_adjTh {u v : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u) Qd) (hv : TestQ v) :
    ∫ p, Work.Spaces.Dth u p.1 p.2 * v p.1 p.2 ∂Qμ
      = ∫ p, u p.1 p.2 * adjTh v p.1 p.2 ∂Qμ := by
  set W : ℝ → ℝ → ℝ := fun z θ => Real.sin (2 * θ) * (u z θ * v z θ) with hWdef
  have hWsm : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry W) Qd := by
    have h1 : Function.uncurry W
        = fun p : ℝ × ℝ => Real.sin (2 * p.2) * (Function.uncurry u p * Function.uncurry v p) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h1]
    exact ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn).mul
      (hu.mul hv.1)
  have hWsupp : tsupport (Function.uncurry W) ⊆ tsupport (Function.uncurry v) := by
    have h1 : Function.uncurry W
        = fun p : ℝ × ℝ => Real.sin (2 * p.2) * (Function.uncurry u p * Function.uncurry v p) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h1]
    refine (tsupport_mul_subset_right (f := fun p : ℝ × ℝ => Real.sin (2 * p.2))
      (g := fun p : ℝ × ℝ => Function.uncurry u p * Function.uncurry v p)).trans ?_
    exact tsupport_mul_subset_right (f := Function.uncurry u) (g := Function.uncurry v)
  have hWcomp : HasCompactSupport (Function.uncurry W) :=
    IsCompact.of_isClosed_subset hv.2.1 (isClosed_tsupport _) hWsupp
  have hWsub : tsupport (Function.uncurry W) ⊆ Qd := fun p hp => hv.2.2 (hWsupp hp)
  have hftc : ∫ p, Work.Spaces.pth W p.1 p.2 ∂Qμ = 0 :=
    integral_pth_eq_zero hWsm hWcomp hWsub
  have hpthW : Integrable (fun p : ℝ × ℝ => Work.Spaces.pth W p.1 p.2) Qμ :=
    integrable_of_contDiffOn_supp (w := Work.Spaces.pth W) (v := v)
      (Work.FTS.LocData.contDiffOn_pth isOpen_Qd hWsm) hv
      ((tsupport_pth_subset (w := W)).trans hWsupp)
  have huv : Integrable (fun p : ℝ × ℝ => Real.sin (2 * p.2) * u p.1 p.2 * Work.Spaces.pth v p.1 p.2) Qμ := by
    refine integrable_of_contDiffOn_supp
      (w := fun z θ => Real.sin (2 * θ) * u z θ * Work.Spaces.pth v z θ) (v := v) ?_ hv ?_
    · have h1 : Function.uncurry (fun z θ => Real.sin (2 * θ) * u z θ * Work.Spaces.pth v z θ)
          = fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry u p
              * Function.uncurry (Work.Spaces.pth v) p := by
        funext p; rcases p with ⟨z, θ⟩; rfl
      rw [h1]
      exact (((Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn).mul hu).mul
        (Work.FTS.LocData.contDiffOn_pth isOpen_Qd hv.1)
    · have h1 : Function.uncurry (fun z θ => Real.sin (2 * θ) * u z θ * Work.Spaces.pth v z θ)
          = fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry u p
              * Function.uncurry (Work.Spaces.pth v) p := by
        funext p; rcases p with ⟨z, θ⟩; rfl
      rw [h1]
      exact (tsupport_mul_subset_right
        (f := fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry u p)
        (g := Function.uncurry (Work.Spaces.pth v))).trans
        ((tsupport_pth_subset (w := v)))
  have huadj : Integrable (fun p : ℝ × ℝ => u p.1 p.2 * adjTh v p.1 p.2) Qμ := by
    refine integrable_of_contDiffOn_supp (w := fun z θ => u z θ * adjTh v z θ) (v := v) ?_ hv ?_
    · have h1 : Function.uncurry (fun z θ => u z θ * adjTh v z θ)
          = Function.uncurry u * Function.uncurry (adjTh v) := by
        funext p; rcases p with ⟨z, θ⟩; rfl
      rw [h1]; exact hu.mul (TestQ_adjTh hv).1
    · exact (tsupport_mul_subset_right (f := Function.uncurry u)
        (g := Function.uncurry (adjTh v))).trans (tsupport_adjTh_subset (w := v))
  have hkey : ∀ᵐ p ∂Qμ, Work.Spaces.Dth u p.1 p.2 * v p.1 p.2
      = u p.1 p.2 * adjTh v p.1 p.2 + Work.Spaces.pth W p.1 p.2 := by
    filter_upwards [ae_mem_Qd] with p hp
    have h1 := pth_mul_three hu hv.1 hp.1 hp.2
    have h2 := adjTh_apply hv.1 hp.1 hp.2
    rw [hWdef, h1, h2, Work.Spaces.Dth]
    ring
  rw [MeasureTheory.integral_congr_ae hkey]
  rw [show (∫ p : ℝ × ℝ, u p.1 p.2 * adjTh v p.1 p.2
        + Work.Spaces.pth W p.1 p.2 ∂Qμ)
      = (∫ p, u p.1 p.2 * adjTh v p.1 p.2 ∂Qμ)
        + ∫ p, Work.Spaces.pth W p.1 p.2 ∂Qμ
    from MeasureTheory.integral_add huadj hpthW]
  rw [hftc, add_zero]

/-! ## Iterating the elementary integrations by parts -/

theorem integral_DzIter_mul_adjDzIter_aux {u : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u) Qd) (j : ℕ) :
    ∀ {v : ℝ → ℝ → ℝ}, TestQ v →
      ∫ p, Work.Spaces.DzIter j u p.1 p.2 * v p.1 p.2 ∂Qμ
        = ∫ p, u p.1 p.2 * adjDzIter j v p.1 p.2 ∂Qμ := by
  induction j with
  | zero => intro v hv; rfl
  | succ j ih =>
      intro v hv
      rw [Work.Spaces.DzIter_succ]
      rw [integral_Dz_mul_adjZ (u := Work.Spaces.DzIter j u) (v := v)
        (Work.FTS.LocData.contDiffOn_DzIter isOpen_Qd hu j) hv]
      rw [ih (TestQ_adjZ hv)]
      rfl

theorem integral_DzIter_mul_adjDzIter {u v : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u) Qd) (hv : TestQ v)
    (j : ℕ) :
    ∫ p, Work.Spaces.DzIter j u p.1 p.2 * v p.1 p.2 ∂Qμ
      = ∫ p, u p.1 p.2 * adjDzIter j v p.1 p.2 ∂Qμ :=
  integral_DzIter_mul_adjDzIter_aux hu j hv

theorem integral_DthIter_mul_adjDthIter_aux {u : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u) Qd) (i : ℕ) :
    ∀ {v : ℝ → ℝ → ℝ}, TestQ v →
      ∫ p, Work.Spaces.DthIter i u p.1 p.2 * v p.1 p.2 ∂Qμ
        = ∫ p, u p.1 p.2 * adjDthIter i v p.1 p.2 ∂Qμ := by
  induction i with
  | zero => intro v hv; rfl
  | succ i ih =>
      intro v hv
      rw [Work.Spaces.DthIter_succ]
      rw [integral_Dth_mul_adjTh (u := Work.Spaces.DthIter i u) (v := v)
        (Work.FTS.LocData.contDiffOn_DthIter isOpen_Qd hu i) hv]
      rw [ih (TestQ_adjTh hv)]
      rfl

theorem integral_DthIter_mul_adjDthIter {u v : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry u) Qd) (hv : TestQ v)
    (i : ℕ) :
    ∫ p, Work.Spaces.DthIter i u p.1 p.2 * v p.1 p.2 ∂Qμ
      = ∫ p, u p.1 p.2 * adjDthIter i v p.1 p.2 ∂Qμ :=
  integral_DthIter_mul_adjDthIter_aux hu i hv

/-! ## The adjointness of `mixed j i` -/

theorem integral_mixed_mul_adjMixed {g ψ : ℝ → ℝ → ℝ}
    (hg : Work.FTS.LocData.SmoothQuad g) (hψ : Work.FTS.Apriori.Limit.TestQ ψ) (j i : ℕ) :
    MeasureTheory.integral Work.FTS.Apriori.Limit.Qμ
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i g p.1 p.2 * ψ p.1 p.2)
      = MeasureTheory.integral Work.FTS.Apriori.Limit.Qμ
        (fun p : ℝ × ℝ => g p.1 p.2 * Work.FTS.Apriori.Limit.adjMixed (j, i) ψ p.1 p.2) := by
  have hg' : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Qd :=
    hg.mono Qd_subset_quadU
  have h1 := integral_DzIter_mul_adjDzIter
    (u := Work.Spaces.DthIter i g) (v := ψ)
    (Work.FTS.LocData.contDiffOn_DthIter isOpen_Qd hg' i) hψ j
  have h2 := integral_DthIter_mul_adjDthIter (u := g) (v := adjDzIter j ψ) hg'
    (TestQ_adjDzIter j hψ) i
  exact h1.trans h2

end Work.FTS.Apriori.Limit
