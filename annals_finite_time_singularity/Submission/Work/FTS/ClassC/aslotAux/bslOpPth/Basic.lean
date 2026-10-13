import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.ClassC.aslotAux.ofReal_HkSq_eq_lintegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.aslotAux.BslOpPth

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary measure-theoretic helpers -/

/-- The half-line `Iz = [0,∞)` and `(0,∞)` agree almost everywhere. -/
theorem lintegral_Iz_congr (f : ℝ → ℝ≥0∞) :
    (∫⁻ z in Work.Spaces.Iz, f z) = ∫⁻ z in Set.Ioi 0, f z := by
  rw [Work.Spaces.Iz]
  exact congrArg (fun μ : Measure ℝ => ∫⁻ z, f z ∂μ)
    (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))).symm

/-- The angular interval `Iθ = [0,π/2]` and the open interval agree almost everywhere. -/
theorem lintegral_Iθ_congr (f : ℝ → ℝ≥0∞) :
    (∫⁻ θ in Work.Spaces.Iθ, f θ) = ∫⁻ θ in Set.Ioo 0 (Real.pi / 2), f θ := by
  rw [Work.Spaces.Iθ]
  exact congrArg (fun μ : Measure ℝ => ∫⁻ θ, f θ ∂μ)
    (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ))
        (b := Real.pi / 2))).symm

/-- The product of the restricted measures is the restricted planar measure. -/
theorem prod_restrict_eq_restrict :
    (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)
      = (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
  have hIz : (volume.restrict Work.Spaces.Iz : Measure ℝ) = volume.restrict (Set.Ioi 0) := by
    rw [Work.Spaces.Iz]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))).symm
  rw [hIz, MeasureTheory.Measure.volume_eq_prod]
  exact MeasureTheory.Measure.prod_restrict (μ := volume) (ν := volume)
    (Set.Ioi (0 : ℝ)) Work.Spaces.Iθ

/-- The two restricted rectangular measures agree. -/
theorem restrict_rect_eq :
    (volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
  have hIz : (volume.restrict Work.Spaces.Iz : Measure ℝ) = volume.restrict (Set.Ioi 0) := by
    rw [Work.Spaces.Iz]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))).symm
  have hL : (volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict (μ := volume) (ν := volume)
      Work.Spaces.Iz Work.Spaces.Iθ).symm
  have hR : (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)
      = (volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict (μ := volume) (ν := volume)
      (Set.Ioi (0 : ℝ)) Work.Spaces.Iθ).symm
  rw [hL, hR, hIz]

/-- The restricted planar measure on `(0,∞) × Iθ` is the one on the open quadrant. -/
theorem restrict_prod_eq_restrict_Q0 :
    (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)
      = volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have h1 : (volume.restrict Work.Spaces.Iθ : Measure ℝ)
      = volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ))
        (b := Real.pi / 2))).symm
  have hL : (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)
      = (volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict (μ := volume) (ν := volume) (Set.Ioi (0 : ℝ))
      Work.Spaces.Iθ).symm
  have hR : (volume : Measure (ℝ × ℝ)).restrict (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
      = (volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict (μ := volume) (ν := volume) (Set.Ioi (0 : ℝ))
      (Set.Ioo (0 : ℝ) (Real.pi / 2))).symm
  rw [hL, hR, h1]

/-- A function continuous on the open quadrant is a.e. strongly measurable for the restricted
planar measure on `(0,∞) × Iθ`. -/
theorem aesm_restrict_Ioi_Iθ {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEStronglyMeasurable g (volume.restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)) := by
  rw [← prod_restrict_eq_restrict]
  exact Work.Spaces.aesm_of_continuousOn_Qd g hg

/-- A.e. measurability of the `ofReal`-integrand for the restricted planar measure. -/
theorem aemeasurable_ofReal_restrict_prod {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (g p))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hIz : (volume.restrict Work.Spaces.Iz : Measure ℝ) = volume.restrict (Set.Ioi 0) := by
    rw [Work.Spaces.Iz]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ)))).symm
  rw [← hIz]
  exact (Work.Spaces.aesm_of_continuousOn_Qd g hg).aemeasurable.ennreal_ofReal

/-- The squared radial weight is continuous on the open quadrant. -/
theorem continuousOn_w_sq_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rw [show (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 from rfl]
    refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
      (continuousOn_fst.pow 2) (fun p hp => ?_)
    exact pow_ne_zero 2 (ne_of_gt hp.1)
  exact h1.pow 2

/-- The angular weight `sin(2θ)^{2-γ}` is continuous on the open quadrant. -/
theorem continuousOn_sigma_Q0 (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hsinpos : ∀ p ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)),
      0 < Real.sin (2 * p.2) := by
    intro p hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  have hsin : Continuous (fun p : ℝ × ℝ => Real.sin (2 * p.2)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_snd)
  exact hsin.continuousOn.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

/-- Cauchy–Schwarz for three terms. -/
theorem sq_sum_three_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

/-- Splitting a `lintegral` against a sum of four terms (only the first three need to be
a.e.-measurable). -/
theorem lintegral_le_sum4 {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f f1 f2 f3 f4 : X → ℝ≥0∞} {A B C D : ℝ≥0∞}
    (h1m : AEMeasurable f1 μ) (h2m : AEMeasurable f2 μ) (h3m : AEMeasurable f3 μ)
    (hle : f ≤ᵐ[μ] fun x => f1 x + (f2 x + (f3 x + f4 x)))
    (h1 : ∫⁻ x, f1 x ∂μ ≤ A) (h2 : ∫⁻ x, f2 x ∂μ ≤ B)
    (h3 : ∫⁻ x, f3 x ∂μ ≤ C) (h4 : ∫⁻ x, f4 x ∂μ ≤ D) :
    ∫⁻ x, f x ∂μ ≤ A + (B + (C + D)) := by
  refine le_trans (MeasureTheory.lintegral_mono_ae hle) ?_
  rw [MeasureTheory.lintegral_add_left' h1m, MeasureTheory.lintegral_add_left' h2m,
    MeasureTheory.lintegral_add_left' h3m]
  exact add_le_add h1 (add_le_add h2 (add_le_add h3 h4))

/-- Splitting a `lintegral` against a sum of three terms. -/
theorem lintegral_le_sum3 {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f f1 f2 f3 : X → ℝ≥0∞} {A B C : ℝ≥0∞}
    (h1m : AEMeasurable f1 μ) (h2m : AEMeasurable f2 μ)
    (hle : f ≤ᵐ[μ] fun x => f1 x + (f2 x + f3 x))
    (h1 : ∫⁻ x, f1 x ∂μ ≤ A) (h2 : ∫⁻ x, f2 x ∂μ ≤ B) (h3 : ∫⁻ x, f3 x ∂μ ≤ C) :
    ∫⁻ x, f x ∂μ ≤ A + (B + C) := by
  refine le_trans (MeasureTheory.lintegral_mono_ae hle) ?_
  rw [MeasureTheory.lintegral_add_left' h1m, MeasureTheory.lintegral_add_left' h2m]
  exact add_le_add h1 (add_le_add h2 h3)

/-! ## The iterated-to-product transfer, and the level-`0` slots -/

/-- Measurability of a `σ`-weighted slot integrand, from smoothness of the uncurried factor
on the open quadrant. -/
theorem aesm_slot_of {α : ℝ} {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (g p ^ 2 * (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)))
      (volume.restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)) := by
  have hA : AEStronglyMeasurable (fun p : ℝ × ℝ => g p ^ 2 * (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (((Work.Spaces.aesm_of_continuousOn_Qd g hg).pow 2).mul
      (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2)
        continuousOn_w_sq_Q0)).mul
      (Work.Spaces.aesm_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α))
        (continuousOn_sigma_Q0 α))
  have hA' : AEStronglyMeasurable (fun p : ℝ × ℝ => g p ^ 2 * (Work.Spaces.w p.1) ^ 2
      * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α))
      (volume.restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)) := by
    rw [← prod_restrict_eq_restrict]
    exact hA
  exact hA'.aemeasurable.ennreal_ofReal

/-- **The transfer**: an iterated `∫⁻_z ∫⁻_θ`-bound for a `σ`-weighted slot gives the
corresponding product-measure bound. -/
theorem piece_slot {α : ℝ} {h : ℝ → ℝ → ℝ} {K : ℝ}
    (hmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal ((h p.1 p.2) ^ 2
      * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)))
      (volume.restrict (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)))
    (hinner : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((h z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) ≤ ENNReal.ofReal K) :
    (∫⁻ p in Set.Ioi 0 ×ˢ Work.Spaces.Iθ,
        ENNReal.ofReal ((h p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α))) ≤ ENNReal.ofReal K := by
  have hmeas' : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal ((h p.1 p.2) ^ 2
      * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [prod_restrict_eq_restrict]
    exact hmeas
  have hM : (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) : Measure (ℝ × ℝ))
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict (μ := volume) (ν := volume)
      Work.Spaces.Iz Work.Spaces.Iθ).symm
  calc (∫⁻ p in Set.Ioi 0 ×ˢ Work.Spaces.Iθ, ENNReal.ofReal ((h p.1 p.2) ^ 2
        * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)))
      = ∫⁻ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ, ENNReal.ofReal ((h p.1 p.2) ^ 2
          * (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)) := by
        rw [← restrict_rect_eq]
    _ = ∫⁻ p, ENNReal.ofReal ((h p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α))
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
        rw [hM]
    _ = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((h z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) :=
        MeasureTheory.lintegral_prod _ hmeas'
    _ = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((h z θ) ^ 2
          * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
        rw [lintegral_Iz_congr (f := fun z => ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((h z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))]
    _ ≤ ENNReal.ofReal K := hinner

/-- The level-`0` `η`-weighted slot of a function `h` with `HkMem α 0 h`. -/
theorem lintegral_Ioi0_Iθ_le_HkSq_zero {α : ℝ} {h : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 0 h) :
    (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((h z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
      ≤ ENNReal.ofReal (Work.Spaces.HkSq α 0 h) := by
  rw [← ofReal_HkSq_eq_lintegral hmem]
  rw [lintegral_Iz_congr (f := fun z => ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 h z θ))]
  refine MeasureTheory.lintegral_mono (fun z => MeasureTheory.lintegral_mono_ae ?_)
  filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc)] with θ hθ
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]
  exact ENNReal.ofReal_le_ofReal (le_of_eq
    (Work.FTS.EllipticEst.Honest.sq_profile_eq h z θ
      (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ)).symm)

/-- The level-`k` mixed slot of a function `g` with `HkMem α k g`. -/
theorem lintegral_Ioi0_Iθ_le_mixed_slot {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k g) (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ k) :
    (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2))
      ≤ ENNReal.ofReal (Work.Spaces.HkSq α k g) := by
  rw [← ofReal_HkSq_eq_lintegral hmem]
  rw [lintegral_Iz_congr (f := fun z => ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k g z θ))]
  refine MeasureTheory.lintegral_mono (fun z => MeasureTheory.lintegral_mono (fun θ => ?_))
  exact ENNReal.ofReal_le_ofReal (Work.Spaces.sq_le_HkIntegrand_mixed α k g z θ i j hi hij)

/-- The `σ = sin(2θ)^{2-γ}`-weighted slot of a function `h` with `HkMem α 0 h`. -/
theorem piece_zero {α : ℝ} {h : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hmem : Work.Spaces.HkMem α 0 h) :
    (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((h z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))
      ≤ ENNReal.ofReal (Work.Spaces.HkSq α 0 h) := by
  refine le_trans ?_ (lintegral_Ioi0_Iθ_le_HkSq_zero hmem)
  refine MeasureTheory.lintegral_mono (fun z => MeasureTheory.lintegral_mono_ae ?_)
  filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc)] with θ hθ
  refine ENNReal.ofReal_le_ofReal ?_
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have h0 : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ
  rcases eq_or_lt_of_le h0 with hz | hz
  · rw [← hz]
    have h1 : (0 : ℝ) ^ (2 - Work.Spaces.gam α) = 0 :=
      Real.zero_rpow (by rw [Work.Spaces.gam]; linarith [hα4])
    have h2 : (0 : ℝ) ^ (-(Work.Spaces.eta)) = 0 :=
      Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
    rw [h1, h2]
  · exact Real.rpow_le_rpow_of_exponent_ge hz (Real.sin_le_one _) (by
      rw [Work.Spaces.eta, Work.Spaces.gam]; linarith [hα4])

end Work.FTS.ClassC.aslotAux.BslOpPth
