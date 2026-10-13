import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.sliceBarSq2
import Submission.Work.FTS.EllipticEst.Honest.honestBarLim
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.cs_integral
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Elementary facts about the angular weight `σ = sEta` -/

theorem hsd_measurable_sEta : Measurable (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ) := by
  unfold Work.FTS.EllipticEst.sEta
  exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow_const _

theorem hsd_integrableOn_sEta :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
    (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta])).1
  simpa only [Work.FTS.EllipticEst.sEta] using h

theorem hsd_pth_eq_deriv (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Spaces.pth Ψ z = deriv (fun θ => Ψ z θ) := rfl

theorem hsd_sEta_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ := by
  unfold Work.FTS.EllipticEst.sEta
  refine Real.rpow_nonneg ?_ _
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
    (by linarith [hθ.2, Real.pi_pos])

theorem hsd_sEta_pi_div_two : Work.FTS.EllipticEst.sEta (Real.pi / 2) = 0 := by
  unfold Work.FTS.EllipticEst.sEta
  rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  exact Real.zero_rpow (by norm_num [Work.Spaces.eta])

/-! ## Boundedness of the slice and of its derivative -/

theorem hsd_slice_bdd {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Ψ z θ| ≤ M ∧ |deriv (fun θ' => Ψ z θ') θ| ≤ M := by
  have hsm : ContDiffOn ℝ 2 (fun θ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hon_slice_contDiffOn h hz 2
  have hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := hon_slice_deriv2_integrableOn_Iθ h hz
  exact slice_bdd_of_sq_mul_sEta hsm hint

theorem hsd_aemeasurable_slice {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ} (hz : 0 < z)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ Real.pi / 2) :
    AEMeasurable (fun θ : ℝ => Ψ z θ) (volume.restrict (Set.Icc a b)) := by
  have hcont : ContinuousOn (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hon_slice_contDiffOn h hz 0).continuousOn
  have hsub : Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun θ hθ =>
    ⟨lt_of_le_of_lt ha hθ.1, lt_of_lt_of_le hθ.2 hb⟩
  have h1 : AEMeasurable (fun θ : ℝ => Ψ z θ) (volume.restrict (Set.Ioo a b)) :=
    ((hcont.mono hsub).aestronglyMeasurable measurableSet_Ioo).aemeasurable
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := a) (b := b)).symm]
  exact h1

theorem hsd_integrableOn_sq_Ioo_of_bdd {u : ℝ → ℝ} (hu : Measurable u) {M : ℝ}
    (hM : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |u θ| ≤ M)
    {a : ℝ} (ha : 0 ≤ a) :
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) (Set.Ioo a (Real.pi / 2)) := by
  have hvol : volume (Set.Ioo a (Real.pi / 2)) < ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  refine MeasureTheory.IntegrableOn.of_bound (s := Set.Ioo a (Real.pi / 2)) hvol
    (hu.aestronglyMeasurable.pow 2) (M ^ 2) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hθ0 : 0 < θ := lt_of_le_of_lt ha hθ.1
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (u θ)) (hM θ ⟨hθ0, hθ.2⟩) 2

theorem hsd_intervalIntegrable_deriv {u : ℝ → ℝ} (hu : Measurable u) {M : ℝ}
    (hM : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |u θ| ≤ M)
    {a : ℝ} (ha : 0 ≤ a) (ha2 : a < Real.pi / 2) :
    IntervalIntegrable u volume a (Real.pi / 2) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha2.le]
  have hvol : volume (Set.Ioc a (Real.pi / 2)) < ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have hne : ∀ᵐ θ ∂(volume.restrict (Set.Ioc a (Real.pi / 2))), θ ≠ Real.pi / 2 :=
    MeasureTheory.ae_restrict_of_ae (by
      rw [MeasureTheory.ae_iff]; simpa using MeasureTheory.measure_singleton (Real.pi / 2))
  refine MeasureTheory.IntegrableOn.of_bound (s := Set.Ioc a (Real.pi / 2)) hvol
    hu.aestronglyMeasurable M ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with θ hθ hne'
  rw [Real.norm_eq_abs]
  exact hM θ ⟨lt_of_le_of_lt ha hθ.1, lt_of_le_of_ne hθ.2 hne'⟩

/-! ## The `θ`-split of `Iθ` -/

theorem hsd_lintegral_split (G : ℝ → ENNReal) :
    (∫⁻ θ in Work.Spaces.Iθ, G θ)
      ≤ (∫⁻ θ in Set.Icc (0 : ℝ) (Real.pi / 4), G θ)
        + (∫⁻ θ in Set.Ioc (Real.pi / 4) (Real.pi / 2), G θ) := by
  have hAB : Set.Icc (0 : ℝ) (Real.pi / 4) ∪ Set.Ioc (Real.pi / 4) (Real.pi / 2)
      = Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]
    ext θ
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, by linarith [h2, Real.pi_pos]⟩
      · exact ⟨le_trans (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 4) (le_of_lt h1), h2⟩
    · rintro ⟨h1, h2⟩
      by_cases h : θ ≤ Real.pi / 4
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨lt_of_not_ge h, h2⟩
  have hd : Disjoint (Set.Icc (0 : ℝ) (Real.pi / 4)) (Set.Ioc (Real.pi / 4) (Real.pi / 2)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx'.1 (not_lt_of_ge hx.2)
  have hmain : (∫⁻ θ in Work.Spaces.Iθ, G θ)
      = (∫⁻ θ in Set.Icc (0 : ℝ) (Real.pi / 4), G θ)
        + ∫⁻ θ in Set.Ioc (Real.pi / 4) (Real.pi / 2), G θ := by
    rw [← hAB, MeasureTheory.lintegral_union measurableSet_Ioc hd]
  exact le_of_eq hmain

/-! ## The left half `[0, π/4]` -/

theorem hsd_one_div_cos_sq_le_two {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 4)) :
    1 / (Real.cos θ) ^ 2 ≤ 2 := by
  have hc : (1 / 2 : ℝ) ≤ (Real.cos θ) ^ 2 := by
    have h2 : Real.cos (Real.pi / 4) ≤ Real.cos θ :=
      Real.cos_le_cos_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]) hθ.2
    have h3 : (Real.cos (Real.pi / 4)) ^ 2 = 1 / 2 := by
      rw [Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    calc (1 / 2 : ℝ) = (Real.cos (Real.pi / 4)) ^ 2 := h3.symm
      _ ≤ (Real.cos θ) ^ 2 := by
          refine pow_le_pow_left₀ ?_ h2 2
          exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],
            by linarith [Real.pi_pos]⟩
  have hpos : 0 < (Real.cos θ) ^ 2 := lt_of_lt_of_le (by norm_num) hc
  rw [div_le_iff₀ hpos]
  linarith

theorem hsd_left_half (h : ℝ → ℝ) :
    (∫⁻ θ in Set.Icc (0 : ℝ) (Real.pi / 4), ENNReal.ofReal
        (Work.FTS.EllipticEst.sEta θ * (h θ / Real.cos θ) ^ 2))
      ≤ 2 * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        (Work.FTS.EllipticEst.sEta θ * (h θ) ^ 2)) := by
  have hpt : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 4),
      ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (h θ / Real.cos θ) ^ 2)
        ≤ (2 : ENNReal) * ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (h θ) ^ 2) := by
    intro θ hθ
    have hc := hsd_one_div_cos_sq_le_two hθ
    have hs : 0 ≤ Work.FTS.EllipticEst.sEta θ := hsd_sEta_nonneg (by
      rw [Work.Spaces.Iθ]; exact ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩)
    have hcinv : ((Real.cos θ) ^ 2)⁻¹ ≤ 2 := by
      rw [← one_div]; exact hc
    have hle : Work.FTS.EllipticEst.sEta θ * (h θ / Real.cos θ) ^ 2
        ≤ Work.FTS.EllipticEst.sEta θ * (h θ) ^ 2 * 2 := by
      rw [div_pow]
      calc Work.FTS.EllipticEst.sEta θ * ((h θ) ^ 2 * ((Real.cos θ) ^ 2)⁻¹)
          = (Work.FTS.EllipticEst.sEta θ * (h θ) ^ 2) * ((Real.cos θ) ^ 2)⁻¹ := by ring
        _ ≤ (Work.FTS.EllipticEst.sEta θ * (h θ) ^ 2) * 2 :=
            mul_le_mul_of_nonneg_left hcinv (mul_nonneg hs (sq_nonneg _))
    refine le_trans (ENNReal.ofReal_le_ofReal hle) ?_
    rw [mul_comm (Work.FTS.EllipticEst.sEta θ * (h θ) ^ 2) 2,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  calc (∫⁻ θ in Set.Icc (0 : ℝ) (Real.pi / 4), ENNReal.ofReal
        (Work.FTS.EllipticEst.sEta θ * (h θ / Real.cos θ) ^ 2))
      ≤ ∫⁻ θ in Set.Icc (0 : ℝ) (Real.pi / 4),
          (2 : ENNReal) * ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (h θ) ^ 2) :=
        MeasureTheory.lintegral_mono_ae
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpt)
    _ = (2 : ENNReal) * (∫⁻ θ in Set.Icc (0 : ℝ) (Real.pi / 4),
          ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (h θ) ^ 2)) :=
        MeasureTheory.lintegral_const_mul' 2 _ (by norm_num)
    _ ≤ (2 : ENNReal) * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (h θ) ^ 2)) :=
        mul_le_mul_right (MeasureTheory.lintegral_mono_set (by
          intro θ hθ
          rw [Set.mem_Icc] at hθ
          rw [Work.Spaces.Iθ, Set.mem_Icc]
          exact ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩)) 2

/-! ## The right half `[π/4, π/2]` -/

/-- **Pointwise Cauchy–Schwarz step of the weighted Hardy inequality.** -/
theorem hsd_pointwise_cs {u u' : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hu' : Measurable u')
    (hder : ∀ x ∈ Set.Ioo a b, HasDerivAt u (u' x) x)
    (hint : IntervalIntegrable u' volume a b)
    (hleft : Tendsto u (nhdsWithin a (Set.Ioi a)) (nhds (u a)))
    (hright : Tendsto u (nhdsWithin b (Set.Iio b)) (nhds 0)) (hub : u b = 0)
    (hsq : MeasureTheory.IntegrableOn (fun x : ℝ => (u' x) ^ 2) (Set.Ioo a b)) :
    ENNReal.ofReal ((u a) ^ 2)
      ≤ ENNReal.ofReal (b - a)
        * (∫⁻ t in Set.Ioo a b, ENNReal.ofReal ((u' t) ^ 2)) := by
  have hFTC : (∫ x in a..b, u' x) = 0 - u a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hab hder hint hleft hright
  have h1 : u a = -(∫ x in a..b, u' x) := by linarith
  have hmem1 : MemLp u' 2 (volume.restrict (Set.Ioo a b)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hu'.aestronglyMeasurable).2 hsq
  have hvol : volume (Set.Ioo a b) < ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo a b)) := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]; exact hvol⟩
  have hmem2 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Set.Ioo a b)) :=
    MeasureTheory.memLp_const 1
  have hcs := Work.Spaces.cs_integral hmem1 hmem2
  have e1 : (∫ x in Set.Ioo a b, u' x) = ∫ x in a..b, u' x := by
    rw [intervalIntegral.integral_of_le hab.le]
    exact (MeasureTheory.integral_Ioc_eq_integral_Ioo).symm
  have e3 : (∫ x in Set.Ioo a b, (1 : ℝ) ^ 2) = b - a := by
    rw [one_pow, MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def,
      Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ b - a), smul_eq_mul, mul_one]
  have hsq_bound : (u a) ^ 2 ≤ (b - a) * (∫ x in Set.Ioo a b, (u' x) ^ 2) := by
    calc (u a) ^ 2 = (∫ x in Set.Ioo a b, u' x) ^ 2 := by rw [h1, ← e1]; ring
      _ = (∫ x in Set.Ioo a b, u' x * 1) ^ 2 := by simp only [mul_one]
      _ ≤ (∫ x in Set.Ioo a b, (u' x) ^ 2) * (∫ x in Set.Ioo a b, (1 : ℝ) ^ 2) := hcs
      _ = (b - a) * (∫ x in Set.Ioo a b, (u' x) ^ 2) := by rw [e3]; ring
  have hconv : ENNReal.ofReal (∫ x in Set.Ioo a b, (u' x) ^ 2)
      = ∫⁻ t in Set.Ioo a b, ENNReal.ofReal ((u' t) ^ 2) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hsq (by
      filter_upwards with x
      exact sq_nonneg _)
  refine le_trans (ENNReal.ofReal_le_ofReal hsq_bound) ?_
  rw [ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ b - a), hconv]

/-- **The pointwise bound on the weight** on `[π/4, π/2]`: with `δ = π/2-θ`,
`σ θ · δ / cos²θ ≤ (π/4)^η (π/2)² δ^{-(1+η)}`. -/
theorem hsd_weight_pt {θ : ℝ} (h4 : Real.pi / 4 ≤ θ) (hθ2 : θ < Real.pi / 2) :
    Work.FTS.EllipticEst.sEta θ * (Real.pi / 2 - θ) / (Real.cos θ) ^ 2
      ≤ (Real.pi / 4) ^ Work.Spaces.eta * (Real.pi / 2) ^ 2
        * (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta)) := by
  have hδ : 0 < Real.pi / 2 - θ := by linarith
  have hη0 : (0 : ℝ) < Work.Spaces.eta := by
    rw [show Work.Spaces.eta = 99 / 100 from rfl]; norm_num
  have hcos : Real.cos θ = Real.sin (Real.pi / 2 - θ) := by
    conv_lhs => rw [show θ = Real.pi / 2 - (Real.pi / 2 - θ) by ring]
    rw [Real.cos_pi_div_two_sub]
  have hsin : Real.sin (2 * θ) = Real.sin (2 * (Real.pi / 2 - θ)) := by
    rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
  have hσ : Work.FTS.EllipticEst.sEta θ
      ≤ (Real.pi / 4) ^ Work.Spaces.eta * (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)) := by
    unfold Work.FTS.EllipticEst.sEta
    rw [hsin]
    have hj : (4 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.sin (2 * (Real.pi / 2 - θ)) := by
      have h := Real.mul_le_sin (x := 2 * (Real.pi / 2 - θ)) (by linarith) (by linarith)
      rwa [show 2 / Real.pi * (2 * (Real.pi / 2 - θ)) = (4 / Real.pi) * (Real.pi / 2 - θ)
        by ring] at h
    have h1 := Real.rpow_le_rpow_of_nonpos (by positivity) hj (by linarith : -(Work.Spaces.eta) ≤ 0)
    refine h1.trans (le_of_eq ?_)
    rw [Real.mul_rpow (div_nonneg (by norm_num) (le_of_lt Real.pi_pos)) (le_of_lt hδ)]
    have hπ : (4 / Real.pi) ^ (-(Work.Spaces.eta)) = (Real.pi / 4) ^ Work.Spaces.eta := by
      rw [Real.rpow_neg_eq_inv_rpow, inv_div]
    rw [hπ]
  have hdiv : (Real.pi / 2 - θ) / (Real.cos θ) ^ 2 ≤ (Real.pi / 2) ^ 2 / (Real.pi / 2 - θ) := by
    rw [hcos]
    have hsinδ : 0 < Real.sin (Real.pi / 2 - θ) :=
      Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [hθ2])
    have hj : (2 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.sin (Real.pi / 2 - θ) :=
      Real.mul_le_sin (le_of_lt hδ) (by linarith)
    have hsq : ((2 / Real.pi) * (Real.pi / 2 - θ)) ^ 2 ≤ (Real.sin (Real.pi / 2 - θ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hj 2
    have hc : (Real.pi / 2) * (2 / Real.pi) = 1 := by field_simp
    have hc2 : (Real.pi / 2) ^ 2 * (2 / Real.pi) ^ 2 = 1 := by
      rw [← mul_pow, hc, one_pow]
    have hgoal : (Real.pi / 2 - θ) ^ 2
        ≤ (Real.pi / 2) ^ 2 * (Real.sin (Real.pi / 2 - θ)) ^ 2 := by
      have hstep := mul_le_mul_of_nonneg_left hsq (sq_nonneg (Real.pi / 2))
      rw [mul_pow, ← mul_assoc, hc2, one_mul] at hstep
      exact hstep
    rw [div_le_iff₀ (pow_pos hsinδ 2)]
    rw [show (Real.pi / 2) ^ 2 / (Real.pi / 2 - θ) * (Real.sin (Real.pi / 2 - θ)) ^ 2
        = (Real.pi / 2) ^ 2 * (Real.sin (Real.pi / 2 - θ)) ^ 2 / (Real.pi / 2 - θ) by ring]
    rw [le_div_iff₀ hδ]
    calc (Real.pi / 2 - θ) * (Real.pi / 2 - θ) = (Real.pi / 2 - θ) ^ 2 := by ring
      _ ≤ (Real.pi / 2) ^ 2 * (Real.sin (Real.pi / 2 - θ)) ^ 2 := hgoal
  calc Work.FTS.EllipticEst.sEta θ * (Real.pi / 2 - θ) / (Real.cos θ) ^ 2
      = Work.FTS.EllipticEst.sEta θ * ((Real.pi / 2 - θ) / (Real.cos θ) ^ 2) := by ring
    _ ≤ ((Real.pi / 4) ^ Work.Spaces.eta * (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)))
          * ((Real.pi / 2) ^ 2 / (Real.pi / 2 - θ)) :=
        mul_le_mul hσ hdiv (div_nonneg (by linarith) (sq_nonneg _))
          (mul_nonneg (Real.rpow_nonneg (by linarith [Real.pi_pos]) _)
            (Real.rpow_nonneg (le_of_lt hδ) _))
    _ = (Real.pi / 4) ^ Work.Spaces.eta * (Real.pi / 2) ^ 2
          * (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta)) := by
        have hpow : (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)) / (Real.pi / 2 - θ)
            = (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta)) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hδ]
          congr 1
          ring
        rw [show ((Real.pi / 4) ^ Work.Spaces.eta * (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)))
              * ((Real.pi / 2) ^ 2 / (Real.pi / 2 - θ))
            = (Real.pi / 4) ^ Work.Spaces.eta * (Real.pi / 2) ^ 2
              * ((Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)) / (Real.pi / 2 - θ)) by ring]
        rw [hpow]

/-- **The elementary weight bound on the triangular region.** -/
theorem hsd_weight_bound {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) (Real.pi / 2)) :
    (∫⁻ θ in Set.Ioo (Real.pi / 4) t, ENNReal.ofReal
        (Work.FTS.EllipticEst.sEta θ * (Real.pi / 2 - θ) / (Real.cos θ) ^ 2))
      ≤ ENNReal.ofReal 8 * ENNReal.ofReal (Work.FTS.EllipticEst.sEta t) := by
  have hη0 : (0 : ℝ) < Work.Spaces.eta := by
    rw [show Work.Spaces.eta = 99 / 100 from rfl]; norm_num
  have hη1 : Work.Spaces.eta ≤ 1 := by
    rw [show Work.Spaces.eta = 99 / 100 from rfl]; norm_num
  by_cases ht4 : Real.pi / 4 < t
  · have ht2 : t < Real.pi / 2 := ht.2
    set K : ℝ := (Real.pi / 4) ^ Work.Spaces.eta * (Real.pi / 2) ^ 2 with hK
    have hK0 : 0 ≤ K := by
      rw [hK]
      exact mul_nonneg (Real.rpow_nonneg (by linarith [Real.pi_pos]) _) (sq_nonneg _)
    have hδt : 0 < Real.pi / 2 - t := by linarith
    -- continuity and integrability of the integrand on `[π/4, t]`
    have hcont : ContinuousOn
        (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ * (Real.pi / 2 - θ) / (Real.cos θ) ^ 2)
        (Set.Icc (Real.pi / 4) t) := by
      have hs : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ)
          (Set.Icc (Real.pi / 4) t) := by
        show ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          (Set.Icc (Real.pi / 4) t)
        have hsin2 : Continuous (fun x : ℝ => Real.sin (2 * x)) := by fun_prop
        exact hsin2.continuousOn.rpow_const (fun x hx => Or.inl (ne_of_gt
          (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1, Real.pi_pos]) (by linarith [hx.2]))))
      have h2 : ContinuousOn (fun θ : ℝ => Real.pi / 2 - θ) (Set.Icc (Real.pi / 4) t) :=
        (continuous_const.sub continuous_id).continuousOn
      have h3 : ContinuousOn (fun θ : ℝ => (Real.cos θ) ^ 2) (Set.Icc (Real.pi / 4) t) :=
        (Real.continuous_cos.pow 2).continuousOn
      exact (hs.mul h2).div h3 (fun x hx => pow_ne_zero 2 (ne_of_gt
        (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2]⟩)))
    have hint : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ * (Real.pi / 2 - θ) / (Real.cos θ) ^ 2)
        (Set.Ioo (Real.pi / 4) t) :=
      (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (Real.pi / 4) t)]
        (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ * (Real.pi / 2 - θ) / (Real.cos θ) ^ 2) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hs : 0 ≤ Work.FTS.EllipticEst.sEta θ := by
        unfold Work.FTS.EllipticEst.sEta
        exact Real.rpow_nonneg
          (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1, Real.pi_pos])
            (by linarith [hθ.2])) _
      exact div_nonneg (mul_nonneg hs (by linarith [hθ.2])) (sq_nonneg _)
    have hof : (∫⁻ θ in Set.Ioo (Real.pi / 4) t, ENNReal.ofReal
          (Work.FTS.EllipticEst.sEta θ * (Real.pi / 2 - θ) / (Real.cos θ) ^ 2))
        = ENNReal.ofReal (∫ θ in Set.Ioo (Real.pi / 4) t,
          Work.FTS.EllipticEst.sEta θ * (Real.pi / 2 - θ) / (Real.cos θ) ^ 2) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    rw [hof]
    have hset : (∫ θ in Set.Ioo (Real.pi / 4) t,
          Work.FTS.EllipticEst.sEta θ * (Real.pi / 2 - θ) / (Real.cos θ) ^ 2)
        = ∫ θ in (Real.pi / 4)..t,
          Work.FTS.EllipticEst.sEta θ * (Real.pi / 2 - θ) / (Real.cos θ) ^ 2 := by
      rw [MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioo_ae_eq_Ioc (a := Real.pi / 4) (b := t)),
        ← intervalIntegral.integral_of_le ht4.le]
    rw [hset]
    have hInt1 : IntervalIntegrable
        (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ * (Real.pi / 2 - θ) / (Real.cos θ) ^ 2)
        volume (Real.pi / 4) t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht4.le).mpr
        ((hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self)
    have hcontM : ContinuousOn (fun θ : ℝ => K * (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta)))
        (Set.Icc (Real.pi / 4) t) :=
      continuousOn_const.mul (((continuous_const.sub continuous_id).continuousOn).rpow_const
        (fun x hx => Or.inl (by linarith [hx.1, hx.2, ht2, Real.pi_pos] :
          Real.pi / 2 - x ≠ 0)))
    have hInt2 : IntervalIntegrable
        (fun θ : ℝ => K * (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta)))
        volume (Real.pi / 4) t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht4.le).mpr
        ((hcontM.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self)
    have hpt : ∀ θ ∈ Set.Icc (Real.pi / 4) t,
        Work.FTS.EllipticEst.sEta θ * (Real.pi / 2 - θ) / (Real.cos θ) ^ 2
          ≤ K * (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta)) := fun θ hθ =>
      hsd_weight_pt hθ.1 (by linarith [hθ.2, ht2])
    have hmono := intervalIntegral.integral_mono_on ht4.le hInt1 hInt2 hpt
    -- the fundamental theorem of calculus for the majorant
    have hderiv : ∀ x ∈ Set.uIcc (Real.pi / 4) t,
        HasDerivAt (fun θ : ℝ => (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)) / Work.Spaces.eta)
          ((Real.pi / 2 - x) ^ (-(1 + Work.Spaces.eta))) x := by
      intro x hx
      rw [Set.uIcc_of_le ht4.le] at hx
      have hx0 : 0 < Real.pi / 2 - x := by linarith [hx.1, hx.2, ht2]
      have hd : HasDerivAt (fun θ : ℝ => Real.pi / 2 - θ) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub (Real.pi / 2)
      have h1 : HasDerivAt (fun θ : ℝ => (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)))
          ((-1) * (-(Work.Spaces.eta)) * (Real.pi / 2 - x) ^ (-(Work.Spaces.eta) - 1)) x :=
        hd.rpow_const (p := -(Work.Spaces.eta)) (Or.inl (ne_of_gt hx0))
      refine (h1.div_const Work.Spaces.eta).congr_deriv ?_
      rw [show (-(1 : ℝ)) * (-(Work.Spaces.eta)) * (Real.pi / 2 - x) ^ (-(Work.Spaces.eta) - 1)
            / Work.Spaces.eta = (Real.pi / 2 - x) ^ (-(Work.Spaces.eta) - 1) by field_simp]
      congr 1
      ring
    have hInt3 : IntervalIntegrable
        (fun θ : ℝ => (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta)))
        volume (Real.pi / 4) t := by
      have hpos : ∀ x ∈ Set.uIcc (Real.pi / 4) t, Real.pi / 2 - x ≠ 0 := by
        intro x hx
        rw [Set.uIcc_of_le ht4.le] at hx
        exact ne_of_gt (by linarith [hx.1, hx.2, ht2, Real.pi_pos])
      exact (((continuous_const.sub continuous_id).continuousOn).rpow_const
        (fun x hx => Or.inl (hpos x hx))).intervalIntegrable
    have hFTC : (∫ θ in (Real.pi / 4)..t, (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta)))
        = (Real.pi / 2 - t) ^ (-(Work.Spaces.eta)) / Work.Spaces.eta
          - (Real.pi / 4) ^ (-(Work.Spaces.eta)) / Work.Spaces.eta := by
      simpa only [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring] using
        intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt3
    have hval : (∫ θ in (Real.pi / 4)..t, K * (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta)))
        ≤ K * ((Real.pi / 2 - t) ^ (-(Work.Spaces.eta)) / Work.Spaces.eta) := by
      rw [intervalIntegral.integral_const_mul, hFTC]
      have hB : 0 ≤ (Real.pi / 4) ^ (-(Work.Spaces.eta)) / Work.Spaces.eta :=
        div_nonneg (Real.rpow_nonneg (by linarith [Real.pi_pos]) _) (le_of_lt hη0)
      have hrew : K * ((Real.pi / 2 - t) ^ (-(Work.Spaces.eta)) / Work.Spaces.eta
            - (Real.pi / 4) ^ (-(Work.Spaces.eta)) / Work.Spaces.eta)
          = K * ((Real.pi / 2 - t) ^ (-(Work.Spaces.eta)) / Work.Spaces.eta)
            - K * ((Real.pi / 4) ^ (-(Work.Spaces.eta)) / Work.Spaces.eta) := by ring
      rw [hrew]
      linarith [mul_nonneg hK0 hB]
    -- numerical bounds
    have hKη : K / Work.Spaces.eta ≤ 4 := by
      have h1 : (Real.pi / 4) ^ Work.Spaces.eta ≤ (Real.pi / 2) ^ Work.Spaces.eta :=
        Real.rpow_le_rpow (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (le_of_lt hη0)
      have h2 : (Real.pi / 2) ^ Work.Spaces.eta ≤ Real.pi / 2 := by
        have h := Real.rpow_le_rpow_of_exponent_le
          (by linarith [Real.pi_gt_d4] : (1 : ℝ) ≤ Real.pi / 2) hη1
        rwa [Real.rpow_one] at h
      have h3 : (Real.pi / 2) ^ 3 / Work.Spaces.eta ≤ 4 := by
        rw [div_le_iff₀ hη0, show Work.Spaces.eta = 99 / 100 from rfl]
        nlinarith [Real.pi_lt_d2, Real.pi_pos]
      have h4 : (Real.pi / 4) ^ Work.Spaces.eta * (Real.pi / 2) ^ 2 ≤ (Real.pi / 2) ^ 3 := by
        calc (Real.pi / 4) ^ Work.Spaces.eta * (Real.pi / 2) ^ 2
            ≤ (Real.pi / 2) ^ Work.Spaces.eta * (Real.pi / 2) ^ 2 :=
              mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
          _ ≤ (Real.pi / 2) * (Real.pi / 2) ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
          _ = (Real.pi / 2) ^ 3 := by ring
      calc (Real.pi / 4) ^ Work.Spaces.eta * (Real.pi / 2) ^ 2 / Work.Spaces.eta
          ≤ (Real.pi / 2) ^ 3 / Work.Spaces.eta := div_le_div_of_nonneg_right h4 (le_of_lt hη0)
        _ ≤ 4 := h3
    have hσt : (2 * (Real.pi / 2 - t)) ^ (-(Work.Spaces.eta))
        ≤ Work.FTS.EllipticEst.sEta t := by
      have hsin : Real.sin (2 * t) = Real.sin (2 * (Real.pi / 2 - t)) := by
        rw [show 2 * (Real.pi / 2 - t) = Real.pi - 2 * t by ring, Real.sin_pi_sub]
      unfold Work.FTS.EllipticEst.sEta
      rw [hsin]
      refine Real.rpow_le_rpow_of_nonpos ?_ ?_ (by linarith : -(Work.Spaces.eta) ≤ 0)
      · exact Real.sin_pos_of_pos_of_lt_pi (by linarith)
          (by linarith [ht2, hδt])
      · exact Real.sin_le (by linarith [hδt])
    have hδ_le : (Real.pi / 2 - t) ^ (-(Work.Spaces.eta))
        ≤ 2 * Work.FTS.EllipticEst.sEta t := by
      have h1 : (2 : ℝ) ^ (-(Work.Spaces.eta)) * (Real.pi / 2 - t) ^ (-(Work.Spaces.eta))
          = (2 * (Real.pi / 2 - t)) ^ (-(Work.Spaces.eta)) :=
        (Real.mul_rpow (by norm_num) (le_of_lt hδt)).symm
      have h2 : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(Work.Spaces.eta)) := by
        have h : (2 : ℝ) ^ (-(1 : ℝ)) ≤ (2 : ℝ) ^ (-(Work.Spaces.eta)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
            (by linarith : -(1 : ℝ) ≤ -(Work.Spaces.eta))
        have h' : (2 : ℝ)⁻¹ ≤ (2 : ℝ) ^ (-(Work.Spaces.eta)) := by
          rwa [Real.rpow_neg_one] at h
        norm_num at h'
        exact h'
      have h3 : (Real.pi / 2 - t) ^ (-(Work.Spaces.eta))
          ≤ 2 * ((2 : ℝ) ^ (-(Work.Spaces.eta)) * (Real.pi / 2 - t) ^ (-(Work.Spaces.eta))) := by
        have h2' : (1 : ℝ) ≤ 2 * (2 : ℝ) ^ (-(Work.Spaces.eta)) := by linarith
        calc (Real.pi / 2 - t) ^ (-(Work.Spaces.eta))
            = 1 * (Real.pi / 2 - t) ^ (-(Work.Spaces.eta)) := by ring
          _ ≤ (2 * (2 : ℝ) ^ (-(Work.Spaces.eta))) * (Real.pi / 2 - t) ^ (-(Work.Spaces.eta)) :=
              mul_le_mul_of_nonneg_right h2' (Real.rpow_nonneg (le_of_lt hδt) _)
          _ = 2 * ((2 : ℝ) ^ (-(Work.Spaces.eta))
                * (Real.pi / 2 - t) ^ (-(Work.Spaces.eta))) := by ring
      calc (Real.pi / 2 - t) ^ (-(Work.Spaces.eta))
          ≤ 2 * ((2 : ℝ) ^ (-(Work.Spaces.eta)) * (Real.pi / 2 - t) ^ (-(Work.Spaces.eta))) := h3
        _ = 2 * (2 * (Real.pi / 2 - t)) ^ (-(Work.Spaces.eta)) := by rw [h1]
        _ ≤ 2 * Work.FTS.EllipticEst.sEta t := mul_le_mul_of_nonneg_left hσt (by norm_num)
    have hfinal : (∫ θ in (Real.pi / 4)..t,
          Work.FTS.EllipticEst.sEta θ * (Real.pi / 2 - θ) / (Real.cos θ) ^ 2)
        ≤ 8 * Work.FTS.EllipticEst.sEta t := by
      refine le_trans hmono (le_trans hval ?_)
      have h2 : K * ((Real.pi / 2 - t) ^ (-(Work.Spaces.eta)) / Work.Spaces.eta)
          = (K / Work.Spaces.eta) * (Real.pi / 2 - t) ^ (-(Work.Spaces.eta)) := by ring
      rw [h2]
      calc (K / Work.Spaces.eta) * (Real.pi / 2 - t) ^ (-(Work.Spaces.eta))
          ≤ 4 * (Real.pi / 2 - t) ^ (-(Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right hKη (Real.rpow_nonneg (le_of_lt hδt) _)
        _ ≤ 4 * (2 * Work.FTS.EllipticEst.sEta t) :=
            mul_le_mul_of_nonneg_left hδ_le (by norm_num)
        _ = 8 * Work.FTS.EllipticEst.sEta t := by ring
    refine le_trans (ENNReal.ofReal_le_ofReal hfinal) ?_
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
  · have hset : Set.Ioo (Real.pi / 4) t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact absurd (lt_trans hx.1 hx.2) ht4
    rw [hset, MeasureTheory.setLIntegral_empty]
    positivity

theorem hsd_right_half {u u' : ℝ → ℝ} (hu' : Measurable u') {M : ℝ}
    (hM : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |u θ| ≤ M ∧ |u' θ| ≤ M)
    (hder : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt u (u' x) x)
    (hr : Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hub : u (Real.pi / 2) = 0) :
    (∫⁻ θ in Set.Ioc (Real.pi / 4) (Real.pi / 2), ENNReal.ofReal
        (Work.FTS.EllipticEst.sEta θ * (u θ / Real.cos θ) ^ 2))
      ≤ ENNReal.ofReal 8 * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        (Work.FTS.EllipticEst.sEta θ * (u' θ) ^ 2)) := by
  set S : Set ℝ := Set.Ioc (Real.pi / 4) (Real.pi / 2) with hS
  set T : Set ℝ := Set.Ico (0 : ℝ) (Real.pi / 2) with hT
  set F : ℝ → ENNReal := fun t => ENNReal.ofReal ((u' t) ^ 2) with hF
  set A : ℝ → ENNReal := fun θ => ENNReal.ofReal
    (Work.FTS.EllipticEst.sEta θ * (Real.pi / 2 - θ) / (Real.cos θ) ^ 2) with hA
  have hSmeas : MeasurableSet S := by rw [hS]; exact measurableSet_Ioc
  have hTmeas : MeasurableSet T := by rw [hT]; exact measurableSet_Ico
  have hFmeas : Measurable F := by
    rw [hF]
    exact ENNReal.measurable_ofReal.comp (Measurable.pow_const hu' (2 : ℕ))
  -- elementary facts about members of `S`
  have hθIθ : ∀ θ ∈ S, θ ∈ Work.Spaces.Iθ := by
    intro θ hθ
    rw [hS] at hθ
    rw [Work.Spaces.Iθ]
    exact ⟨le_of_lt (lt_trans (by linarith [Real.pi_pos]) hθ.1), hθ.2⟩
  have hsq : ∀ θ ∈ S, MeasureTheory.IntegrableOn (fun t : ℝ => (u' t) ^ 2)
      (Set.Ioo θ (Real.pi / 2)) := by
    intro θ hθ
    rw [hS] at hθ
    exact hsd_integrableOn_sq_Ioo_of_bdd hu' (fun t ht => (hM t ht).2)
      (le_of_lt (lt_trans (by linarith [Real.pi_pos]) hθ.1))
  have hintI : ∀ θ ∈ S, θ < Real.pi / 2 → IntervalIntegrable u' volume θ (Real.pi / 2) := by
    intro θ hθ hlt
    rw [hS] at hθ
    exact hsd_intervalIntegrable_deriv hu' (fun t ht => (hM t ht).2)
      (le_of_lt (lt_trans (by linarith [Real.pi_pos]) hθ.1)) hlt
  have hIooT : ∀ {θ : ℝ}, Real.pi / 4 < θ → Set.Ioo θ (Real.pi / 2) ⊆ T := by
    intro θ hθ t ht
    rw [hT]
    exact ⟨le_of_lt (lt_trans (lt_trans (by linarith [Real.pi_pos]) hθ) ht.1), ht.2⟩
  -- Step 1: split off the weight `σ/cos²`
  have step1 : (∫⁻ θ in S, ENNReal.ofReal
        (Work.FTS.EllipticEst.sEta θ * (u θ / Real.cos θ) ^ 2))
      = ∫⁻ θ in S, ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ / (Real.cos θ) ^ 2)
          * ENNReal.ofReal ((u θ) ^ 2) := by
    refine MeasureTheory.lintegral_congr_ae
      (MeasureTheory.ae_restrict_of_forall_mem hSmeas (fun θ hθ => ?_))
    show ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (u θ / Real.cos θ) ^ 2)
      = ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ / (Real.cos θ) ^ 2)
        * ENNReal.ofReal ((u θ) ^ 2)
    rw [← ENNReal.ofReal_mul (div_nonneg (hsd_sEta_nonneg (hθIθ θ hθ)) (sq_nonneg _))]
    congr 1
    rw [div_pow]
    ring
  -- Step 2: the pointwise Cauchy--Schwarz bound
  have step2 : (∫⁻ θ in S, ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ / (Real.cos θ) ^ 2)
          * ENNReal.ofReal ((u θ) ^ 2))
      ≤ ∫⁻ θ in S, ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ / (Real.cos θ) ^ 2)
          * (ENNReal.ofReal (Real.pi / 2 - θ)
            * ∫⁻ t in Set.Ioo θ (Real.pi / 2), F t) := by
    refine MeasureTheory.lintegral_mono_ae
      (MeasureTheory.ae_restrict_of_forall_mem hSmeas (fun θ hθ => ?_))
    rw [hS] at hθ
    show ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ / (Real.cos θ) ^ 2)
          * ENNReal.ofReal ((u θ) ^ 2)
        ≤ ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ / (Real.cos θ) ^ 2)
          * (ENNReal.ofReal (Real.pi / 2 - θ)
            * ∫⁻ t in Set.Ioo θ (Real.pi / 2), F t)
    rcases eq_or_lt_of_le hθ.2 with heq | hlt
    · subst heq
      have h0 : ENNReal.ofReal (Work.FTS.EllipticEst.sEta (Real.pi / 2)
          / (Real.cos (Real.pi / 2)) ^ 2) = 0 := by
        rw [hsd_sEta_pi_div_two, zero_div, ENNReal.ofReal_zero]
      rw [h0, zero_mul, zero_mul]
    · have hleft : Tendsto u (nhdsWithin θ (Set.Ioi θ)) (nhds (u θ)) :=
        ((hder θ ⟨lt_trans (by linarith [Real.pi_pos]) hθ.1, hlt⟩).continuousAt).tendsto.mono_left
          nhdsWithin_le_nhds
      have hcs := hsd_pointwise_cs hlt hu'
        (fun x hx => hder x ⟨lt_trans (lt_trans (by linarith [Real.pi_pos]) hθ.1) hx.1, hx.2⟩)
        (hintI θ hθ hlt) hleft hr hub (hsq θ hθ)
      exact mul_le_mul_right hcs _
  -- Step 3: put the two `θ`-factors together and rewrite the inner integral over `T`
  have step3 : (∫⁻ θ in S, ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ / (Real.cos θ) ^ 2)
          * (ENNReal.ofReal (Real.pi / 2 - θ)
            * ∫⁻ t in Set.Ioo θ (Real.pi / 2), F t))
      = ∫⁻ θ in S, A θ * (∫⁻ t in T, (Set.Ioo θ (Real.pi / 2)).indicator F t) := by
    refine MeasureTheory.lintegral_congr_ae
      (MeasureTheory.ae_restrict_of_forall_mem hSmeas (fun θ hθ => ?_))
    show ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ / (Real.cos θ) ^ 2)
          * (ENNReal.ofReal (Real.pi / 2 - θ) * ∫⁻ t in Set.Ioo θ (Real.pi / 2), F t)
        = A θ * (∫⁻ t in T, (Set.Ioo θ (Real.pi / 2)).indicator F t)
    have hcoef : ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ / (Real.cos θ) ^ 2)
          * ENNReal.ofReal (Real.pi / 2 - θ) = A θ := by
      rw [hA, ← ENNReal.ofReal_mul (div_nonneg (hsd_sEta_nonneg (hθIθ θ hθ)) (sq_nonneg _))]
      congr 1
      ring
    have hinner : (∫⁻ t in Set.Ioo θ (Real.pi / 2), F t)
        = ∫⁻ t in T, (Set.Ioo θ (Real.pi / 2)).indicator F t := by
      rw [← MeasureTheory.lintegral_indicator measurableSet_Ioo,
        ← MeasureTheory.lintegral_indicator hTmeas]
      refine MeasureTheory.lintegral_congr fun t => ?_
      rw [Set.indicator_apply]
      by_cases ht : t ∈ Set.Ioo θ (Real.pi / 2)
      · rw [if_pos ht, Set.indicator_of_mem (hIooT hθ.1 ht), Set.indicator_of_mem ht]
      · rw [if_neg ht]
        by_cases htT : t ∈ T
        · rw [Set.indicator_of_mem htT, Set.indicator_of_notMem ht]
        · rw [Set.indicator_of_notMem htT]
    rw [← mul_assoc, hcoef, hinner]
  -- Step 4: pull the `θ`-coefficient inside and swap
  have step4a : (∫⁻ θ in S, A θ * (∫⁻ t in T, (Set.Ioo θ (Real.pi / 2)).indicator F t))
      = ∫⁻ θ in S, ∫⁻ t in T, A θ * (Set.Ioo θ (Real.pi / 2)).indicator F t := by
    refine MeasureTheory.lintegral_congr fun θ => ?_
    exact (MeasureTheory.lintegral_const_mul' (A θ) _ ENNReal.ofReal_ne_top).symm
  have hmeas : AEMeasurable (Function.uncurry (fun θ t : ℝ =>
      A θ * (Set.Ioo θ (Real.pi / 2)).indicator F t))
      ((volume.restrict S).prod (volume.restrict T)) := by
    have hAmeas : Measurable A := by
      rw [hA]
      refine ENNReal.measurable_ofReal.comp ?_
      exact (hsd_measurable_sEta.mul (measurable_const.sub measurable_id)).div
        (Measurable.pow_const Real.measurable_cos (2 : ℕ))
    have h1 : AEMeasurable (fun p : ℝ × ℝ => A p.1)
        ((volume.restrict S).prod (volume.restrict T)) :=
      hAmeas.aemeasurable.comp_fst
    have h2 : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Set.Ioo p.1 (Real.pi / 2)} := by
      have hlt1 : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
        measurableSet_lt measurable_fst measurable_snd
      have hlt2 : MeasurableSet {p : ℝ × ℝ | p.2 < Real.pi / 2} :=
        measurableSet_lt measurable_snd measurable_const
      have he : {p : ℝ × ℝ | p.2 ∈ Set.Ioo p.1 (Real.pi / 2)}
          = {p : ℝ × ℝ | p.1 < p.2} ∩ {p : ℝ × ℝ | p.2 < Real.pi / 2} := by
        ext p
        simp only [Set.mem_ofPred_eq, Set.mem_Ioo, Set.mem_inter_iff, and_comm]
      rw [he]
      exact hlt1.inter hlt2
    have h3 : AEMeasurable (fun p : ℝ × ℝ => F p.2)
        ((volume.restrict S).prod (volume.restrict T)) :=
      hFmeas.aemeasurable.comp_snd
    exact h1.mul (h3.indicator h2)
  have step4b : (∫⁻ θ in S, ∫⁻ t in T, A θ * (Set.Ioo θ (Real.pi / 2)).indicator F t)
      = ∫⁻ t in T, ∫⁻ θ in S, A θ * (Set.Ioo θ (Real.pi / 2)).indicator F t :=
    MeasureTheory.lintegral_lintegral_swap hmeas
  -- Step 5: bound the inner integral for each `t`
  have step5 : ∀ t ∈ T, (∫⁻ θ in S, A θ * (Set.Ioo θ (Real.pi / 2)).indicator F t)
      ≤ F t * (ENNReal.ofReal 8 * ENNReal.ofReal (Work.FTS.EllipticEst.sEta t)) := by
    intro t ht
    have ht2 : t < Real.pi / 2 := ht.2
    have e1 : (∫⁻ θ in S, A θ * (Set.Ioo θ (Real.pi / 2)).indicator F t)
        = ∫⁻ θ in S, A θ * (Set.Iio t).indicator (fun _ => F t) θ := by
      refine MeasureTheory.lintegral_congr fun θ => ?_
      congr 1
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases h : θ < t
      · rw [if_pos ⟨h, ht2⟩, if_pos (Set.mem_Iio.mpr h)]
      · rw [if_neg (fun hc => h hc.1), if_neg (fun hc => h (Set.mem_Iio.mp hc))]
    have e2 : (∫⁻ θ in S, A θ * (Set.Iio t).indicator (fun _ => F t) θ)
        = (∫⁻ θ in S ∩ Set.Iio t, A θ) * F t := by
      rw [← MeasureTheory.lintegral_indicator hSmeas]
      rw [show S.indicator (fun θ => A θ * (Set.Iio t).indicator (fun _ => F t) θ)
          = (S ∩ Set.Iio t).indicator (fun θ => A θ * F t) from by
        funext θ
        by_cases h1 : θ ∈ S
        · by_cases h2 : θ ∈ Set.Iio t
          · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
              Set.indicator_of_mem (show θ ∈ S ∩ Set.Iio t from ⟨h1, h2⟩)]
          · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, Set.indicator_of_notMem
              (fun hc => h2 hc.2), mul_zero]
        · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (fun hc => h1 hc.1)]]
      rw [MeasureTheory.lintegral_indicator (hSmeas.inter measurableSet_Iio),
        MeasureTheory.lintegral_mul_const' (F t) _ ENNReal.ofReal_ne_top]
    have hset : S ∩ Set.Iio t = Set.Ioo (Real.pi / 4) t := by
      rw [hS]
      ext θ
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioo, Set.mem_Ioc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, by linarith [h3, ht2]⟩, h3⟩
    rw [e1, e2, hset]
    by_cases ht4 : Real.pi / 4 < t
    · refine le_trans (mul_le_mul_left (hsd_weight_bound ht) (F t)) (le_of_eq ?_)
      ring
    · have hempty : Set.Ioo (Real.pi / 4) t = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact absurd (lt_trans hx.1 hx.2) ht4
      rw [hempty, MeasureTheory.setLIntegral_empty, zero_mul]
      positivity
  -- Step 6: assemble
  have step6 : (∫⁻ t in T, ∫⁻ θ in S, A θ * (Set.Ioo θ (Real.pi / 2)).indicator F t)
      ≤ ENNReal.ofReal 8 * (∫⁻ t in Work.Spaces.Iθ, ENNReal.ofReal
          (Work.FTS.EllipticEst.sEta t * (u' t) ^ 2)) := by
    have h1 : (∫⁻ t in T, ∫⁻ θ in S, A θ * (Set.Ioo θ (Real.pi / 2)).indicator F t)
        ≤ ∫⁻ t in T, F t * (ENNReal.ofReal 8 * ENNReal.ofReal (Work.FTS.EllipticEst.sEta t)) :=
      MeasureTheory.lintegral_mono_ae
        (MeasureTheory.ae_restrict_of_forall_mem hTmeas step5)
    refine le_trans h1 ?_
    rw [show (fun t : ℝ => F t
          * (ENNReal.ofReal 8 * ENNReal.ofReal (Work.FTS.EllipticEst.sEta t)))
        = fun t : ℝ => ENNReal.ofReal 8
          * (F t * ENNReal.ofReal (Work.FTS.EllipticEst.sEta t)) from by
      funext t; ring,
      MeasureTheory.lintegral_const_mul' (ENNReal.ofReal 8) _ ENNReal.ofReal_ne_top]
    refine mul_le_mul_right ?_ (ENNReal.ofReal 8)
    refine le_trans (le_of_eq ?_) (MeasureTheory.lintegral_mono_set (s := T)
      (t := Work.Spaces.Iθ) ?_)
    · refine MeasureTheory.lintegral_congr fun t => ?_
      show F t * ENNReal.ofReal (Work.FTS.EllipticEst.sEta t)
        = ENNReal.ofReal (Work.FTS.EllipticEst.sEta t * (u' t) ^ 2)
      rw [hF, ← ENNReal.ofReal_mul (sq_nonneg (u' t))]
      ring
    · intro t ht
      rw [hT] at ht
      rw [Work.Spaces.Iθ]
      exact ⟨ht.1, le_of_lt ht.2⟩
  refine le_trans (le_of_eq step1) ?_
  refine le_trans step2 ?_
  refine le_trans (le_of_eq step3) ?_
  refine le_trans (le_of_eq step4a) ?_
  refine le_trans (le_of_eq step4b) ?_
  exact step6

theorem honSliceDivCosLintegral {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.Honest.Hon α F Ψ) {z : ℝ} (hz : 0 < z) :
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        (Work.FTS.EllipticEst.sEta θ * (Ψ z θ / Real.cos θ) ^ 2))
      ≤ 100 * ((∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
            (Work.FTS.EllipticEst.sEta θ * (Ψ z θ) ^ 2))
        + (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
            (Work.FTS.EllipticEst.sEta θ * (Work.Spaces.pth Ψ z θ) ^ 2))) := by
  obtain ⟨M, hM0, hM⟩ := hsd_slice_bdd h hz
  have hbdd : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Ψ z θ| ≤ M ∧ |Work.Spaces.pth Ψ z θ| ≤ M := fun θ hθ => hM θ hθ
  have hder : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ => Ψ z θ) (Work.Spaces.pth Ψ z x) x := by
    intro x hx
    have h1 : ContDiffOn ℝ 1 (fun θ => Ψ z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hon_slice_contDiffOn h hz 1
    exact ((h1.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have hr : Tendsto (fun θ => Ψ z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    HonSliceRightTendsto α F Ψ h z hz
  have hub : (fun θ => Ψ z θ) (Real.pi / 2) = 0 := h.dπ z
  have hu' : Measurable (Work.Spaces.pth Ψ z) := by
    rw [hsd_pth_eq_deriv]
    exact measurable_deriv _
  set P : ENNReal := ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
    (Work.FTS.EllipticEst.sEta θ * (Ψ z θ) ^ 2) with hP
  set Q : ENNReal := ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
    (Work.FTS.EllipticEst.sEta θ * (Work.Spaces.pth Ψ z θ) ^ 2) with hQ
  have hsplit := hsd_lintegral_split
    (fun θ => ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (Ψ z θ / Real.cos θ) ^ 2))
  have hleft := hsd_left_half (fun θ => Ψ z θ)
  have hright := hsd_right_half hu' hbdd hder hr hub
  have hleft' : (∫⁻ θ in Set.Icc (0 : ℝ) (Real.pi / 4), ENNReal.ofReal
        (Work.FTS.EllipticEst.sEta θ * (Ψ z θ / Real.cos θ) ^ 2)) ≤ 2 * P := hleft
  have hright' : (∫⁻ θ in Set.Ioc (Real.pi / 4) (Real.pi / 2), ENNReal.ofReal
        (Work.FTS.EllipticEst.sEta θ * (Ψ z θ / Real.cos θ) ^ 2))
      ≤ ENNReal.ofReal 8 * Q := hright
  have h1 : (2 : ENNReal) * P ≤ 100 * P :=
    mul_le_mul_left (by norm_num : (2 : ENNReal) ≤ 100) P
  have h2 : ENNReal.ofReal 8 * Q ≤ 100 * Q :=
    mul_le_mul_left (by norm_num : ENNReal.ofReal 8 ≤ (100 : ENNReal)) Q
  calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal
        (Work.FTS.EllipticEst.sEta θ * (Ψ z θ / Real.cos θ) ^ 2))
      ≤ (∫⁻ θ in Set.Icc (0 : ℝ) (Real.pi / 4), ENNReal.ofReal
            (Work.FTS.EllipticEst.sEta θ * (Ψ z θ / Real.cos θ) ^ 2))
          + (∫⁻ θ in Set.Ioc (Real.pi / 4) (Real.pi / 2), ENNReal.ofReal
            (Work.FTS.EllipticEst.sEta θ * (Ψ z θ / Real.cos θ) ^ 2)) := hsplit
    _ ≤ 2 * P + ENNReal.ofReal 8 * Q := add_le_add hleft' hright'
    _ ≤ 100 * P + 100 * Q := add_le_add h1 h2
    _ = 100 * (P + Q) := by rw [mul_add]

end

end Work.FTS.EllipticEst.Honest
