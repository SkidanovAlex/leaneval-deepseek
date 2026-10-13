import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB
import Submission.Work.FTS.EllipticEst.Cores.Pieces.AeW2Energy
import Submission.Work.FTS.EllipticEst.Cores.Pieces.AeW2SliceBundle
import Submission.Work.FTS.EllipticEst.Cores.Pieces.AeUHkLe
import Submission.Work.Spaces.integrable_prod_of_iterated

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeCutEnergyV2`

The truncated level-`0` energy inequality of Step 1 of `prop:H2` of
T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021), in the
almost-everywhere class `Work.FTS.EllipticEst.H2W.Ae.AeData`.

The real-valued content is the *proved* inequality
`Work.FTS.EllipticEst.Cores.Pieces.cut_ineq` (stated in the slice notation `sgU`, `sgY`, `sgP`
of `Work.FTS.EllipticEst.AngAWeak`); its two extra hypotheses are both available for `AeData`
data: the six a.e. slice-integrability conditions (`Cores.Pieces.AeW2SliceBundle`) and the
honesty of the `w²`-weighted angular energy (`Cores.Pieces.integrableOn_wSq_sgY`).  What is
added here is the transfer between the `∫⁻`-form of the statement and the Bochner form of
`cut_ineq`, and the final assembly in `ℝ≥0∞`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.EllipticEst.H2W.AeProof

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Transfer lemmas between the Bochner integral and the lintegral -/

/-- `ofReal` of the Bochner integral of a function is dominated by the lintegral of its
`ofReal`-lift. -/
private theorem ofReal_integral_le_lintegral {s : Set ℝ} {f : ℝ → ℝ} :
    ENNReal.ofReal (∫ x in s, f x) ≤ ∫⁻ x in s, ENNReal.ofReal (f x) := by
  by_cases hg : MeasureTheory.IntegrableOn f s
  · have hg' : MeasureTheory.IntegrableOn (fun x => max (f x) 0) s := hg.pos_part
    have h1 : (∫ x in s, f x) ≤ ∫ x in s, max (f x) 0 :=
      MeasureTheory.integral_mono hg hg' (fun x => le_max_left _ _)
    have h2 : ENNReal.ofReal (∫ x in s, max (f x) 0)
        = ∫⁻ x in s, ENNReal.ofReal (max (f x) 0) :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg'
        (Filter.Eventually.of_forall fun x => le_max_right _ _)
    calc ENNReal.ofReal (∫ x in s, f x) ≤ ENNReal.ofReal (∫ x in s, max (f x) 0) :=
          ENNReal.ofReal_le_ofReal h1
      _ = ∫⁻ x in s, ENNReal.ofReal (max (f x) 0) := h2
      _ = ∫⁻ x in s, ENNReal.ofReal (f x) := by
          refine lintegral_congr (fun x => ?_)
          rcases lt_or_ge 0 (f x) with h | h
          · rw [max_eq_left (le_of_lt h)]
          · rw [max_eq_right h, ENNReal.ofReal_eq_zero.mpr h, ENNReal.ofReal_zero]
  · rw [MeasureTheory.integral_undef hg]; simp

/-- The weighted slice integral in `∫⁻`-form dominates `ofReal` of its Bochner form. -/
private theorem ofReal_integral_le_lintegral_weight (W : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hW : ∀ z, 0 ≤ W z) :
    ENNReal.ofReal (∫ z in Work.Spaces.Iz, W z * (∫ θ in Work.Spaces.Iθ, f z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (W z)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (f z θ)) := by
  calc ENNReal.ofReal (∫ z in Work.Spaces.Iz, W z * (∫ θ in Work.Spaces.Iθ, f z θ))
      = ENNReal.ofReal (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, W z * f z θ) := by
        congr 1
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
        rw [MeasureTheory.integral_const_mul]
    _ ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, W z * f z θ) :=
        ofReal_integral_le_lintegral
    _ ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (W z * f z θ) :=
        MeasureTheory.lintegral_mono (fun z => ofReal_integral_le_lintegral)
    _ = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (W z) * ENNReal.ofReal (f z θ) := by
        refine lintegral_congr (fun z => lintegral_congr (fun θ => ?_))
        rw [ENNReal.ofReal_mul (hW z)]
    _ = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (W z)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (f z θ)) := by
        refine lintegral_congr (fun z => ?_)
        rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- **The exact form of the previous transfer lemma**, when the joint function is integrable:
the weighted slice lintegral is `ofReal` of the Bochner form. -/
private theorem lintegral_weight_eq_ofReal (W : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hW : ∀ z, 0 ≤ W z) (hf : ∀ z θ, 0 ≤ f z θ)
    (haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => W p.1 * f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hint : MeasureTheory.Integrable (fun p : ℝ × ℝ => W p.1 * f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (W z)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (f z θ)))
      = ENNReal.ofReal (∫ z in Work.Spaces.Iz, W z * (∫ θ in Work.Spaces.Iθ, f z θ)) := by
  have hmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (W p.1 * f p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := haesm.aemeasurable.ennreal_ofReal
  have e1 : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (W z)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (f z θ)))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (W z * f z θ) := by
    refine lintegral_congr (fun z => ?_)
    rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (W z)) _ ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun θ => ?_)
    rw [ENNReal.ofReal_mul (hW z)]
  have e2 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (W z * f z θ))
      = ∫⁻ p, ENNReal.ofReal (W p.1 * f p.1 p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.lintegral_prod (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun p : ℝ × ℝ => ENNReal.ofReal (W p.1 * f p.1 p.2)) hmeas]
  have e3 : (∫⁻ p, ENNReal.ofReal (W p.1 * f p.1 p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ENNReal.ofReal (∫ p, W p.1 * f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun p => mul_nonneg (hW p.1) (hf p.1 p.2)))).symm
  have e4 : (∫ p, W p.1 * f p.1 p.2
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ z in Work.Spaces.Iz, W z * (∫ θ in Work.Spaces.Iθ, f z θ) := by
    rw [MeasureTheory.integral_prod (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun p : ℝ × ℝ => W p.1 * f p.1 p.2) hint]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    show (∫ y in Work.Spaces.Iθ, W z * f z y) = W z * ∫ θ in Work.Spaces.Iθ, f z θ
    rw [MeasureTheory.integral_const_mul]
  rw [e1, e2, e3, e4]

/-! ## Slice data of an `AeData` datum -/

/-- The restricted measures on `Iz` and on `(0,∞)` agree. -/
private theorem restrict_Iz_eq_Ioi_V2 :
    (MeasureTheory.volume.restrict Work.Spaces.Iz : MeasureTheory.Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
  rw [Work.Spaces.Iz]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm

/-- The angular slice `θ ↦ (∂_θu z θ)²` is integrable for a.e. `z`, for `AeData` data. -/
private theorem ae_slice_pth_sq (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pth u z θ) ^ 2) Work.Spaces.Iθ := by
  filter_upwards [Work.FTS.EllipticEst.Honest.ae_pos_of_mem_Iz] with z hz
  -- the slice is `C¹` on the open interval
  have hslice : ContDiffOn ℝ 1 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have hp : ContDiffOn ℝ 1 (fun θ : ℝ => ((z, θ) : ℝ × ℝ)) (Set.Ioo 0 (Real.pi / 2)) := by
      fun_prop
    have h2 := (h.smooth 1).comp hp (fun θ hθ => ⟨hz, hθ⟩)
    simpa [Function.comp_def, Function.uncurry] using h2
  have hcont : ContinuousOn (fun θ => Work.Spaces.pth u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have hd := hslice.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
    simpa only [Work.Spaces.pth] using hd
  have hIoo : MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2))
      = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) :=
    (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
        (b := Real.pi / 2))).symm
  obtain ⟨C, -, hC⟩ :=
    Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB h.smooth h.memAng2 hz
  refine MeasureTheory.IntegrableOn.of_bound isCompact_Icc.measure_lt_top ?_ (C ^ 2) ?_
  · rw [hIoo]
    exact (hcont.pow 2).aestronglyMeasurable measurableSet_Ioo
  · rw [hIoo]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hb : |Work.Spaces.pth u z θ| ≤ C := (hC θ hθ).2
    have hb' : |Work.Spaces.pth u z θ| ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [sq_abs] at hb'
    exact hb'

/-- The angular slice `θ ↦ (∂_zu z θ)²` is integrable for a.e. `z`, for `AeData` data
(divided out of the `(z ∂_zu)²`-condition). -/
private theorem ae_slice_pz_sq (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pz u z θ) ^ 2) Work.Spaces.Iθ := by
  have hb := Work.FTS.EllipticEst.Cores.Pieces.AeW2SliceBundle α u G h
  rw [← restrict_Iz_eq_Ioi_V2] at hb
  filter_upwards [hb, Work.FTS.EllipticEst.Honest.ae_pos_of_mem_Iz] with z hz hzpos
  obtain ⟨-, -, -, -, hB2, -⟩ := hz
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => ((z : ℝ) ^ 2)⁻¹ * ((z * Work.Spaces.pz u z θ) ^ 2)) Work.Spaces.Iθ :=
    MeasureTheory.Integrable.const_mul hB2 _
  refine h1.congr_fun (fun θ _ => ?_) measurableSet_Icc
  have hz0 : z ≠ 0 := ne_of_gt hzpos
  change ((z : ℝ) ^ 2)⁻¹ * (z * Work.Spaces.pz u z θ) ^ 2 = Work.Spaces.pz u z θ ^ 2
  rw [mul_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hz0), one_mul]

/-! ## Bridges from the Bochner form of `cut_ineq` to the `∫⁻`-form of the statement -/

/-- Joint strong measurability of a level-`0` weighted product, from continuity on the open
quadrant. -/
private theorem aesm_quadrant_weight (W : ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hWc : ContinuousOn (fun p : ℝ × ℝ => W p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hfc : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => W p.1 * f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ (hWc.mul hfc)

/-- Bridge for the radial term: `∫⁻_z ofReal (φw²z²)·(∫⁻_θ ofReal ((∂_zu)²))` is `ofReal` of
the Bochner integral `∫_z φw²z² (∫_θ (∂_zu)²)`. -/
private theorem bridge_A (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (φ : ℝ → ℝ)
    (hφsm : ContDiff ℝ 2 φ) (hφnn : ∀ z : ℝ, 0 ≤ φ z) (hφ1 : ∀ z : ℝ, φ z ≤ 1) :
    (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2)))
      = ENNReal.ofReal (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * z ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz u z θ) ^ 2)) := by
  have hWnn : ∀ z : ℝ, 0 ≤ φ z * (Work.Spaces.w z) ^ 2 * z ^ 2 := fun z =>
    mul_nonneg (mul_nonneg (hφnn z) (sq_nonneg _)) (sq_nonneg _)
  have hmg : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
    Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G h
  have hWzsqP : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * z ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgP u z)
      Work.Spaces.Iz :=
    (Work.FTS.EllipticEst.Cores.Pieces.integrableOn_wSq_zsq_sgP (α := α) hmg
      (Work.FTS.EllipticEst.AngAWeak.aesm_wSq_zsq_sgP h)).1
  have hφmeas : Measurable φ := hφsm.continuous.measurable
  have houter0 : MeasureTheory.IntegrableOn
      (fun z => φ z * ((Work.Spaces.w z) ^ 2 * z ^ 2
        * Work.FTS.EllipticEst.AngAWeak.sgP u z)) Work.Spaces.Iz :=
    Work.FTS.EllipticEst.Cores.Pieces.integrableOn_mul_of_bounded hφnn hφ1 hφmeas hWzsqP
  have houter : MeasureTheory.IntegrableOn
      (fun z => φ z * (Work.Spaces.w z) ^ 2 * z ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz u z θ) ^ 2)) Work.Spaces.Iz :=
    houter0.congr_fun (fun z _ => by
      simp only [Work.FTS.EllipticEst.AngAWeak.sgP]; ring) measurableSet_Ici
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => φ z * (Work.Spaces.w z) ^ 2 * z ^ 2
        * (Work.Spaces.pz u z θ) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [ae_slice_pz_sq α u G h] with z hz
    exact MeasureTheory.Integrable.const_mul hz _
  have hcont_pz : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h1 := Work.FTS.EllipticEst.Blocks.contDiffOn_uncurry_pz_succ
      (G := u) (U := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) (isOpen_Ioi.prod isOpen_Ioo)
      (n := 0) (by simpa using h.smooth 1)
    exact h1.continuousOn_zero
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (φ p.1 * (Work.Spaces.w p.1) ^ 2 * p.1 ^ 2)
        * (Work.Spaces.pz u p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have hφc : ContinuousOn (fun p : ℝ × ℝ => φ p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      hφsm.continuous.comp continuous_fst |>.continuousOn
    have hwc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      simpa only [Work.FTS.EllipticEst.AngAWeak.Qd] using
        Work.FTS.EllipticEst.AngAWeak.continuousOn_w_Qd
    exact ((hφc.mul (hwc.pow 2)).mul (continuous_fst.pow 2).continuousOn).mul
      (hcont_pz.pow 2)
  have hjoint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => φ p.1 * (Work.Spaces.w p.1) ^ 2 * p.1 ^ 2
        * (Work.Spaces.pz u p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine (Work.Spaces.integrable_prod_of_iterated
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (G := fun z θ => φ z * (Work.Spaces.w z) ^ 2 * z ^ 2
        * (Work.Spaces.pz u z θ) ^ 2)
      (fun z θ => mul_nonneg (hWnn z) (sq_nonneg _)) haesm hslice ?_).1
    refine houter.integrable.congr ?_
    filter_upwards with z
    rw [MeasureTheory.integral_const_mul]
  exact lintegral_weight_eq_ofReal _ _
    (fun z => hWnn z) (fun z θ => sq_nonneg _) haesm hjoint

/-- Bridge for the angular term. -/
private theorem bridge_B (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (φ : ℝ → ℝ)
    (hφsm : ContDiff ℝ 2 φ) (hφnn : ∀ z : ℝ, 0 ≤ φ z) (hφ1 : ∀ z : ℝ, φ z ≤ 1) :
    (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)))
      = ENNReal.ofReal (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2)) := by
  have hWnn : ∀ z : ℝ, 0 ≤ φ z * (Work.Spaces.w z) ^ 2 := fun z =>
    mul_nonneg (hφnn z) (sq_nonneg _)
  have hwsqY : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgY u z)
      Work.Spaces.Iz := Work.FTS.EllipticEst.Cores.Pieces.integrableOn_wSq_sgY h
  have hφmeas : Measurable φ := hφsm.continuous.measurable
  have houter : MeasureTheory.IntegrableOn
      (fun z => φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2)) Work.Spaces.Iz :=
    (Work.FTS.EllipticEst.Cores.Pieces.integrableOn_mul_of_bounded hφnn hφ1 hφmeas hwsqY).congr_fun
      (fun z _ => by simp only [Work.FTS.EllipticEst.AngAWeak.sgY]; ring) measurableSet_Ici
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => φ z * (Work.Spaces.w z) ^ 2
        * (Work.Spaces.pth u z θ) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [ae_slice_pth_sq α u G h] with z hz
    exact MeasureTheory.Integrable.const_mul hz _
  have hcont_pth : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have h1 := Work.FTS.EllipticEst.AngAWeak.contDiffOn_uncurry_pth_succ
      (G := u) (U := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) (isOpen_Ioi.prod isOpen_Ioo)
      (n := 0) (by simpa using h.smooth 1)
    exact h1.continuousOn_zero
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (φ p.1 * (Work.Spaces.w p.1) ^ 2)
        * (Work.Spaces.pth u p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have hφc : ContinuousOn (fun p : ℝ × ℝ => φ p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      hφsm.continuous.comp continuous_fst |>.continuousOn
    have hwc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      simpa only [Work.FTS.EllipticEst.AngAWeak.Qd] using
        Work.FTS.EllipticEst.AngAWeak.continuousOn_w_Qd
    exact (hφc.mul (hwc.pow 2)).mul (hcont_pth.pow 2)
  have hjoint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => φ p.1 * (Work.Spaces.w p.1) ^ 2
        * (Work.Spaces.pth u p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine (Work.Spaces.integrable_prod_of_iterated
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (G := fun z θ => φ z * (Work.Spaces.w z) ^ 2
        * (Work.Spaces.pth u z θ) ^ 2)
      (fun z θ => mul_nonneg (hWnn z) (sq_nonneg _)) haesm hslice ?_).1
    refine houter.integrable.congr ?_
    filter_upwards with z
    rw [MeasureTheory.integral_const_mul]
  exact lintegral_weight_eq_ofReal _ _
    (fun z => hWnn z) (fun z θ => sq_nonneg _) haesm hjoint

/-- Bridge for the mass term. -/
private theorem bridge_M (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) (φ : ℝ → ℝ)
    (hφsm : ContDiff ℝ 2 φ) (hφnn : ∀ z : ℝ, 0 ≤ φ z)
    (hM : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))) ≠ ⊤) :
    (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
      = ENNReal.ofReal (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)) := by
  have hWnn : ∀ z : ℝ, 0 ≤ φ z * (Work.Spaces.w z) ^ 2 := fun z =>
    mul_nonneg (hφnn z) (sq_nonneg _)
  have hcont_u : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (h.smooth 0).continuousOn
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (φ p.1 * (Work.Spaces.w p.1) ^ 2) * (u p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have hφc : ContinuousOn (fun p : ℝ × ℝ => φ p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      hφsm.continuous.comp continuous_fst |>.continuousOn
    have hwc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      simpa only [Work.FTS.EllipticEst.AngAWeak.Qd] using
        Work.FTS.EllipticEst.AngAWeak.continuousOn_w_Qd
    exact (hφc.mul (hwc.pow 2)).mul (hcont_u.pow 2)
  have hlin : (∫⁻ p, ENNReal.ofReal (φ p.1 * (Work.Spaces.w p.1) ^ 2 * (u p.1 p.2) ^ 2)
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) ≠ ⊤ := by
    have e1 : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
        = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2 * (u z θ) ^ 2) := by
      refine lintegral_congr (fun z => ?_)
      rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)) _
        ENNReal.ofReal_ne_top]
      refine lintegral_congr (fun θ => ?_)
      rw [ENNReal.ofReal_mul (hWnn z)]
    rw [e1] at hM
    rwa [← MeasureTheory.lintegral_prod (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun p : ℝ × ℝ =>
        ENNReal.ofReal (φ p.1 * (Work.Spaces.w p.1) ^ 2 * (u p.1 p.2) ^ 2))
      haesm.aemeasurable.ennreal_ofReal] at hM
  have hjoint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => φ p.1 * (Work.Spaces.w p.1) ^ 2 * (u p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable haesm
      (Filter.Eventually.of_forall fun p => mul_nonneg (hWnn p.1) (sq_nonneg _))).mp hlin
  exact lintegral_weight_eq_ofReal _ _
    (fun z => hWnn z) (fun z θ => sq_nonneg _) haesm hjoint

/-- Bridge for the source term: `ofReal` of the Bochner integral is dominated by the lintegral. -/
private theorem bridge_F (φ : ℝ → ℝ) (u G : ℝ → ℝ → ℝ) (hφnn : ∀ z : ℝ, 0 ≤ φ z) :
    ENNReal.ofReal (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) :=
  ofReal_integral_le_lintegral_weight _ _
    (fun z => mul_nonneg (hφnn z) (sq_nonneg _))

/-! ## The target -/

theorem AeCutEnergyV2 (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hC : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2)))
    (hL0 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hLπ : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (φ : ℝ → ℝ) (hφsm : ContDiff ℝ 2 φ) (hcpt : HasCompactSupport φ)
    (hφ0 : ∀ z : ℝ, z ≤ 0 → φ z = 0) (hφnn : ∀ z : ℝ, 0 ≤ φ z) (hφ1 : ∀ z : ℝ, φ z ≤ 1)
    (hφδ : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, z ≤ δ → φ z = 0)
    (hM : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))) ≠ ⊤) :
    ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2)))
      + (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)))
    ≤ ENNReal.ofReal (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)))
        * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
      + ENNReal.ofReal (1 / 2)
        * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      + ENNReal.ofReal ((α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
            (2 * |deriv φ z| * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
              + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
              * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))
          + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
              |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
                * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))) := by
  -- ## the two extra hypotheses of `cut_ineq`
  have hslice := Work.FTS.EllipticEst.Cores.Pieces.AeW2SliceBundle α u G h
  have hIntY := Work.FTS.EllipticEst.Cores.Pieces.integrableOn_wSq_sgY h
  -- ## the real-valued inequality
  have hcut := Work.FTS.EllipticEst.Cores.Pieces.cut_ineq α u G h φ hφsm hcpt hφδ hφnn hφ1
    hslice hIntY
  simp only [Work.FTS.EllipticEst.AngAWeak.sgP, Work.FTS.EllipticEst.AngAWeak.sgY,
    Work.FTS.EllipticEst.AngAWeak.sgU] at hcut
  -- ## the bridges to the `∫⁻`-form
  have hA := bridge_A α u G h φ hφsm hφnn hφ1
  have hB := bridge_B α u G h φ hφsm hφnn hφ1
  have hMb := bridge_M α u G h φ hφsm hφnn hM
  have hFb := bridge_F φ u G hφnn
  -- ## nonnegativity of the pieces
  have hAnn : (0 : ℝ) ≤ ∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * z ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz u z θ) ^ 2) :=
    setIntegral_nonneg measurableSet_Ici (fun z _ => mul_nonneg
      (mul_nonneg (mul_nonneg (hφnn z) (sq_nonneg _)) (sq_nonneg _))
      (MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)))
  have hBnn : (0 : ℝ) ≤ ∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2) :=
    setIntegral_nonneg measurableSet_Ici (fun z _ => mul_nonneg
      (mul_nonneg (hφnn z) (sq_nonneg _))
      (MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)))
  have hMnn : (0 : ℝ) ≤ ∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2) :=
    setIntegral_nonneg measurableSet_Ici (fun z _ => mul_nonneg
      (mul_nonneg (hφnn z) (sq_nonneg _))
      (MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)))
  have hFnn : (0 : ℝ) ≤ ∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
    setIntegral_nonneg measurableSet_Ici (fun z _ => mul_nonneg
      (mul_nonneg (hφnn z) (sq_nonneg _))
      (MeasureTheory.integral_nonneg_of_ae (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        refine mul_nonneg (sq_nonneg _) ?_
        rw [Work.FTS.EllipticEst.sEta]
        exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
          ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _)))
  have hK0 : (0 : ℝ) ≤ 13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)) := by
    have h1 : (0 : ℝ) ≤ 3 * α ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ (3 / 2) * α * (5 + α) :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt h.1)) (by linarith [h.1])
    linarith
  have hEnn : (0 : ℝ) ≤ (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
        (2 * |deriv φ z| * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
          * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))
      + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
          |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)) := by
    have h1 : (0 : ℝ) ≤ ∫ z in Work.Spaces.Iz,
        (2 * |deriv φ z| * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
          + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
          * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2) :=
      setIntegral_nonneg measurableSet_Ici (fun z _ => mul_nonneg (by positivity)
        (MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)))
    have h2 : (0 : ℝ) ≤ ∫ z in Work.Spaces.Iz, |deriv φ z| * (z * (Work.Spaces.w z) ^ 2)
        * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2) :=
      setIntegral_nonneg measurableSet_Ici (fun z hz => mul_nonneg
        (mul_nonneg (abs_nonneg _) (mul_nonneg hz (sq_nonneg _)))
        (MeasureTheory.integral_nonneg (fun θ => sq_nonneg _)))
    have h3 : (0 : ℝ) ≤ α ^ 2 / 2 := by positivity
    have h4 : (0 : ℝ) ≤ α * (5 + α) / 2 :=
      mul_nonneg (mul_nonneg (le_of_lt h.1) (by linarith [h.1])) (by norm_num)
    nlinarith [mul_nonneg h3 h1, mul_nonneg h4 h2]
  -- ## assembly
  have h1F : (0 : ℝ) ≤ ((1 / 2) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))) := by linarith [hFnn]
  have hKM : (0 : ℝ) ≤ (((13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)))) := mul_nonneg hK0 hMnn
  have hPK : (0 : ℝ) ≤ ((((13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))) + ((1 / 2) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))))) := by linarith [hKM, h1F]
  have hstep1 : ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2 * z ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2)))
      + (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)))
      = ENNReal.ofReal (α ^ 2 * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz u z θ) ^ 2)) + (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2))) := by
    rw [hA, hB, ← ENNReal.ofReal_mul (sq_nonneg α)]
    exact (ENNReal.ofReal_add (mul_nonneg (sq_nonneg α) hAnn) hBnn).symm
  have hstep2 : ENNReal.ofReal (α ^ 2 * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * z ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz u z θ) ^ 2)) + (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2))) ≤ ENNReal.ofReal ((((13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))) + ((1 / 2) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))) + ((α ^ 2 / 2) * (∫ z in Work.Spaces.Iz, (2 * |deriv φ z| * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z| + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)) + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz, |deriv φ z| * (z * (Work.Spaces.w z) ^ 2) * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)))) := by
    refine ENNReal.ofReal_le_ofReal ?_
    convert hcut using 1 <;> ring
  have hstep3 : ENNReal.ofReal ((((13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))) + ((1 / 2) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))) + ((α ^ 2 / 2) * (∫ z in Work.Spaces.Iz, (2 * |deriv φ z| * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z| + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)) + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz, |deriv φ z| * (z * (Work.Spaces.w z) ^ 2) * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)))) ≤ ENNReal.ofReal ((((13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))) + ((1 / 2) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))))) + ENNReal.ofReal ((α ^ 2 / 2) * (∫ z in Work.Spaces.Iz, (2 * |deriv φ z| * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z| + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)) + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz, |deriv φ z| * (z * (Work.Spaces.w z) ^ 2) * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))) :=
    le_of_eq (ENNReal.ofReal_add (p := (((13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))) + ((1 / 2) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))))) (q := ((α ^ 2 / 2) * (∫ z in Work.Spaces.Iz, (2 * |deriv φ z| * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z| + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)) + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz, |deriv φ z| * (z * (Work.Spaces.w z) ^ 2) * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)))) hPK hEnn)
  have hstep4 : ENNReal.ofReal ((((13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))) + ((1 / 2) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))))) + ENNReal.ofReal ((α ^ 2 / 2) * (∫ z in Work.Spaces.Iz, (2 * |deriv φ z| * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z| + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)) + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz, |deriv φ z| * (z * (Work.Spaces.w z) ^ 2) * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)))
      ≤ (ENNReal.ofReal ((13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))) + ENNReal.ofReal ((1 / 2) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))) + ENNReal.ofReal ((α ^ 2 / 2) * (∫ z in Work.Spaces.Iz, (2 * |deriv φ z| * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z| + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)) + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz, |deriv φ z| * (z * (Work.Spaces.w z) ^ 2) * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))) :=
    add_le_add (le_of_eq (ENNReal.ofReal_add (p := ((13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)))) (q := ((1 / 2) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))) hKM h1F)) le_rfl
  have hstep5 : (ENNReal.ofReal ((13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))) + ENNReal.ofReal ((1 / 2) * (∫ z in Work.Spaces.Iz, φ z * (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))) + ENNReal.ofReal ((α ^ 2 / 2) * (∫ z in Work.Spaces.Iz, (2 * |deriv φ z| * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z| + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)) + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz, |deriv φ z| * (z * (Work.Spaces.w z) ^ 2) * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)))
      ≤ (ENNReal.ofReal (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α))) * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
                  * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
          + ENNReal.ofReal (1 / 2)
              * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (φ z * (Work.Spaces.w z) ^ 2)
                  * (∫⁻ θ in Work.Spaces.Iθ,
                      ENNReal.ofReal ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))))
          + ENNReal.ofReal ((α ^ 2 / 2) * (∫ z in Work.Spaces.Iz, (2 * |deriv φ z| * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z| + |deriv (deriv φ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)) + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz, |deriv φ z| * (z * (Work.Spaces.w z) ^ 2) * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2))) := by
    refine add_le_add (add_le_add ?_ ?_) le_rfl
    · rw [ENNReal.ofReal_mul hK0, hMb]
    · rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact mul_le_mul le_rfl hFb bot_le bot_le
  exact le_trans (le_of_eq hstep1) (le_trans hstep2 (le_trans hstep3 (le_trans hstep4 hstep5)))

end Work.FTS.EllipticEst.H2W.AeProof
