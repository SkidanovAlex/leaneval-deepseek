import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.ClassC.VopGen.truncFacts
import Submission.Work.FTS.ClassC.aslotAux.bslOpPth.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.ClassC.VopGen.truncHonest`

The measure-theoretic engine of the truncation half `VopGen.TruncStmt`: for a nonnegative
light-weighted slot `(h)²(w)²σ` which is jointly continuous on the open quadrant and dominated
pointwise by an `HkIntegrand`-majorant, one gets its slicewise, outer and product integrability
together with the Fubini identity.
-/
noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.VopGen

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Work.Spaces (HkSq HkMem HkIntegrand HkIntegrand_nonneg w Iz Iθ)

local notation "Q0" => Work.FTS.EllipticEst.Q0

/-- The restricted measure on `Iθ` is the one on the open interval. -/
theorem restrict_Iθ_eq_Ioo :
    (volume.restrict Iθ : Measure ℝ) = volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
  rw [Work.Spaces.Iθ]
  exact (MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2))).symm

/-- The product of the restricted measures is the restricted measure on `Iz ×ˢ Iθ`. -/
theorem prod_restrict_eq_rect :
    (volume.restrict Iz).prod (volume.restrict Iθ)
      = (volume : Measure (ℝ × ℝ)).restrict (Iz ×ˢ Iθ) := by
  rw [MeasureTheory.Measure.volume_eq_prod]
  exact MeasureTheory.Measure.prod_restrict (μ := volume) (ν := volume) Iz Iθ

/-- **The closed-rectangle form of a slot domination.**  A domination proved on the open quadrant
extends to the closed rectangle, because both weights vanish on the boundary. -/
theorem closed_dom {α : ℝ} {k : ℕ} {h M : ℝ → ℝ → ℝ} (hα1 : α ≤ 1)
    (hle : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (h z θ) ^ 2 * (w z) ^ 2 * sgm α θ ≤ HkIntegrand α k M z θ) :
    ∀ z ∈ Iz, ∀ θ ∈ Iθ, (h z θ) ^ 2 * (w z) ^ 2 * sgm α θ ≤ HkIntegrand α k M z θ := by
  have hexp : 2 - Work.Spaces.gam α ≠ 0 := by
    rw [Work.Spaces.gam]; intro hc; linarith
  intro z hz θ hθ
  have hz' : 0 ≤ z := Set.mem_Ici.mp hz
  have hθ' : 0 ≤ θ := (Set.mem_Icc.mp hθ).1
  have hθ2 : θ ≤ Real.pi / 2 := (Set.mem_Icc.mp hθ).2
  rcases lt_or_ge 0 z with hz0 | hz0
  · rcases lt_or_ge 0 θ with hθ0 | hθ0
    · rcases lt_or_ge θ (Real.pi / 2) with hlt | hlt
      · exact hle z θ hz0 hθ0 hlt
      · have hθeq : θ = Real.pi / 2 := le_antisymm hθ2 hlt
        have hzero : sgm α θ = 0 := by
          simp only [sgm, hθeq, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
          exact Real.zero_rpow hexp
        have : (h z θ) ^ 2 * (w z) ^ 2 * sgm α θ = 0 := by rw [hzero, mul_zero]
        rw [this]; exact HkIntegrand_nonneg α k M z θ
    · have hθeq : θ = 0 := le_antisymm hθ0 hθ'
      have hzero : sgm α θ = 0 := by
        simp only [sgm, hθeq, mul_zero, Real.sin_zero]
        exact Real.zero_rpow hexp
      have : (h z θ) ^ 2 * (w z) ^ 2 * sgm α θ = 0 := by rw [hzero, mul_zero]
      rw [this]; exact HkIntegrand_nonneg α k M z θ
  · have hzeq : z = 0 := le_antisymm hz0 hz'
    have hw : w z = 0 := by rw [hzeq, Work.Spaces.w]; norm_num
    have : (h z θ) ^ 2 * (w z) ^ 2 * sgm α θ = 0 := by rw [hw]; ring
    rw [this]; exact HkIntegrand_nonneg α k M z θ

/-- **The engine.**  A nonnegative slot `(h)²·(w)²·σ`, jointly continuous on the open quadrant and
dominated by the `HkIntegrand`-majorant of an honest function, is honest: slicewise a.e., in `z`,
on the product, and its iterated integral is the product integral. -/
theorem slotFacts {α : ℝ} {k : ℕ} {h M : ℝ → ℝ → ℝ} (hα1 : α ≤ 1) (hM : HkMem α k M)
    (hhcont : ContinuousOn (Function.uncurry h) Q0)
    (hle : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (h z θ) ^ 2 * (w z) ^ 2 * sgm α θ ≤ HkIntegrand α k M z θ) :
    (∀ᵐ z ∂(volume.restrict Iz),
        IntegrableOn (fun θ => (h z θ) ^ 2 * (w z) ^ 2 * sgm α θ) Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Iθ, (h z θ) ^ 2 * (w z) ^ 2 * sgm α θ) Iz ∧
      IntegrableOn (fun p : ℝ × ℝ => (h p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2)
        (Iz ×ˢ Iθ) ∧
      (∫ p in Iz ×ˢ Iθ, (h p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2
        = ∫ z in Iz, ∫ θ in Iθ, (h z θ) ^ 2 * (w z) ^ 2 * sgm α θ) := by
  have hleC : ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      (h z θ) ^ 2 * (w z) ^ 2 * sgm α θ ≤ HkIntegrand α k M z θ :=
    closed_dom hα1 hle
  -- joint a.e.-strong-measurability
  have hgcont : ContinuousOn (Function.uncurry (fun z θ => (h z θ) ^ 2 * (w z) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) Q0 := by
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · exact hhcont.pow 2
    · exact Work.FTS.ClassC.aslotAux.BslOpPth.continuousOn_w_sq_Q0
    · exact Work.FTS.ClassC.aslotAux.BslOpPth.continuousOn_sigma_Q0 α
  have haesm : AEStronglyMeasurable (Function.uncurry (fun z θ => (h z θ) ^ 2 * (w z) ^ 2
      * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)))
      ((volume.restrict Iz).prod (volume.restrict Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hgcont
  -- slicewise honesty, a.e. in `z`
  have hslice : ∀ᵐ z ∂(volume.restrict Iz),
      IntegrableOn (fun θ => (h z θ) ^ 2 * (w z) ^ 2 * sgm α θ) Iθ := by
    filter_upwards [Work.FTS.EllipticEst.Prop.ae_restrict_Iz_pos] with z hz
    have hzI : z ∈ Iz := Set.mem_Ici.mpr hz.le
    have hMz : IntegrableOn (fun θ => HkIntegrand α k M z θ) Iθ := hM.1 z hzI
    have hcont : ContinuousOn (fun θ => (h z θ) ^ 2 * (w z) ^ 2 * sgm α θ)
        (Set.Ioo 0 (Real.pi / 2)) := by
      have h2 : ContinuousOn (fun θ : ℝ => ((z, θ) : ℝ × ℝ)) (Set.Ioo 0 (Real.pi / 2)) := by
        fun_prop
      have h3 : ContinuousOn (fun θ : ℝ => (h z θ) ^ 2 * (w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) (Set.Ioo 0 (Real.pi / 2)) :=
        hgcont.comp h2 (fun θ hθ => ⟨hz, hθ⟩)
      simpa only [sgm] using h3
    have hIoo : IntegrableOn (fun θ => (h z θ) ^ 2 * (w z) ^ 2 * sgm α θ)
        (Set.Ioo 0 (Real.pi / 2)) := by
      refine Integrable.mono' (hMz.mono_set Ioo_subset_Icc_self)
        (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hθI : θ ∈ Iθ := ⟨hθ.1.le, hθ.2.le⟩
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (by rw [sgm]; exact sigma_nonneg hθI))]
      exact hleC z hzI θ hθI
    rw [MeasureTheory.IntegrableOn, restrict_Iθ_eq_Ioo]
    exact hIoo
  -- the iterated lintegral bound
  have hinner : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ,
      ENNReal.ofReal ((h z θ) ^ 2 * (w z) ^ 2 * sgm α θ)) ≤ ENNReal.ofReal (HkSq α k M) := by
    rw [← Work.FTS.ClassC.aslotAux.BslOpPth.lintegral_Iz_congr
      (f := fun z => ∫⁻ θ in Iθ, ENNReal.ofReal ((h z θ) ^ 2 * (w z) ^ 2 * sgm α θ))]
    rw [← Work.FTS.ClassC.aslotAux.ofReal_HkSq_eq_lintegral hM]
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact ENNReal.ofReal_le_ofReal (hleC z hz θ hθ)
  -- the product lintegral bound
  have hpiece : (∫⁻ p in Set.Ioi 0 ×ˢ Iθ,
      ENNReal.ofReal ((h p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2))
      ≤ ENNReal.ofReal (HkSq α k M) := by
    have hmeas : AEMeasurable
        (fun p : ℝ × ℝ => ENNReal.ofReal ((h p.1 p.2) ^ 2 * (w p.1) ^ 2
          * (Real.sin (2 * p.2)) ^ (2 - Work.Spaces.gam α)))
        (volume.restrict (Set.Ioi 0 ×ˢ Iθ)) := by
      have h0 := Work.FTS.ClassC.aslotAux.BslOpPth.aesm_slot_of (α := α)
        (g := Function.uncurry h) hhcont
      exact h0
    have hinner' : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Iθ,
        ENNReal.ofReal ((h z θ) ^ 2 * (w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) ≤ ENNReal.ofReal (HkSq α k M) := by
      simpa only [sgm] using hinner
    have h := Work.FTS.ClassC.aslotAux.BslOpPth.piece_slot (α := α) (h := h)
      (K := HkSq α k M) hmeas hinner'
    simpa only [sgm] using h
  -- the a.e. nonnegativity on the product
  have hnn_prod : 0 ≤ᵐ[((volume.restrict Iz).prod (volume.restrict Iθ))]
      (fun p : ℝ × ℝ => (h p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2) := by
    rw [prod_restrict_eq_rect]
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_Ici.prod measurableSet_Icc)] with p hp
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (by rw [sgm]; exact sigma_nonneg hp.2)
  have hfin : MeasureTheory.HasFiniteIntegral
      (fun p : ℝ × ℝ => (h p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) := by
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (f := fun p : ℝ × ℝ => (h p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2) hnn_prod]
    rw [prod_restrict_eq_rect, Work.FTS.ClassC.aslotAux.BslOpPth.restrict_rect_eq]
    exact lt_of_le_of_lt hpiece ENNReal.ofReal_lt_top
  have hIntegrable : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (h p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) := ⟨haesm, hfin⟩
  refine ⟨hslice, ?_, ?_, ?_⟩
  · have h1 := hIntegrable.integral_prod_left
    simpa only [MeasureTheory.IntegrableOn] using h1
  · have h1 : MeasureTheory.Integrable
        (fun p : ℝ × ℝ => (h p.1 p.2) ^ 2 * (w p.1) ^ 2 * sgm α p.2)
        ((volume : Measure (ℝ × ℝ)).restrict (Iz ×ˢ Iθ)) := by
      rw [← prod_restrict_eq_rect]
      exact hIntegrable
    simpa only [MeasureTheory.IntegrableOn] using h1
  · have h1 := MeasureTheory.integral_integral
      (μ := volume.restrict Iz) (ν := volume.restrict Iθ)
      (f := fun z θ => (h z θ) ^ 2 * (w z) ^ 2 * sgm α θ) hIntegrable
    rw [prod_restrict_eq_rect] at h1
    exact h1.symm

end Work.FTS.ClassC.VopGen
