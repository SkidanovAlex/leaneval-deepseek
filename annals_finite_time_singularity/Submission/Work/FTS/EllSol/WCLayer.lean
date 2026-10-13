/-
# `Work.FTS.EllSol.WCLayer` — the layer integrals of `σ = sin(2θ)^{-η}` and the two-layer bound

This module contains the analytic input of `Work.FTS.EllSol.wildCorrector`:

* Jordan's inequality `sin(2θ) ≥ 4θ/π` on `(0, π/4]` in the form
  `sin(2θ)^{-η} ≤ (π/4)^η θ^{-η}` (`thEta_le_rpow`);
* the layer integrals `∫_0^a σ ≤ (π/4)^η a^{1-η}/(1-η)` and
  `∫_{a/2}^a σ ≤ (π/4)^η a^{1-η}/(1-η)` (`integral_thEta_zero_a`, `integral_thEta_half_a`),
  together with their reflections `∫_{π/2-a}^{π/2} σ`, `∫_{π/2-a}^{π/2-a/2} σ` obtained by the
  substitution `θ ↦ π/2 - θ`, under which `σ` is invariant;
* the general "two-layer" bound `integral_two_layer_le`: if `F` vanishes off
  `Icc c₁ d₁ ∪ Icc c₂ d₂` and `|F| ≤ K` then `∫_{Iθ} σ F² ≤ K² L₁ + K² L₂` whenever `Lᵢ`
  bounds `∫_{cᵢ}^{dᵢ} σ`;
* the domination criterion `integrableOn_thEta_mul_sq` for the integrability of `σ F²`.

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol

local notation "σ" => Work.FTS.EllipticEst.thEta
local notation "η" => Work.Spaces.eta

set_option autoImplicit false

lemma eta_lt_one : η < 1 := by norm_num [Work.Spaces.eta]

lemma eta_nonneg : 0 ≤ η := Work.Spaces.eta_nonneg

lemma one_sub_eta_pos : 0 < 1 - η := by norm_num [Work.Spaces.eta]

lemma one_sub_eta_ne : (1 : ℝ) - η ≠ 0 := ne_of_gt one_sub_eta_pos

lemma measurable_thEta : Measurable σ := by
  show Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
  exact Measurable.pow_const (Real.measurable_sin.comp (measurable_const.mul measurable_id)) _

/-- Jordan's inequality in the form needed here: on `(0, π/4]`,
`sin(2θ)^{-η} ≤ (π/4)^η θ^{-η}`. -/
lemma thEta_le_rpow {θ : ℝ} (h0 : 0 < θ) (h4 : θ ≤ Real.pi / 4) :
    σ θ ≤ (Real.pi / 4) ^ η * θ ^ (-η) := by
  have h2θ0 : 0 ≤ 2 * θ := by linarith
  have h2θ1 : 2 * θ ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hj := Real.mul_le_sin h2θ0 h2θ1
  have hle : 4 * θ / Real.pi ≤ Real.sin (2 * θ) := by
    have e : (2 : ℝ) / Real.pi * (2 * θ) = 4 * θ / Real.pi := by ring
    rwa [e] at hj
  have hpos : 0 < 4 * θ / Real.pi := by positivity
  have h1 := Real.rpow_le_rpow_of_nonpos hpos hle (neg_nonpos.mpr eta_nonneg)
  have h2 : 4 * θ / Real.pi = (Real.pi / 4)⁻¹ * θ := by rw [inv_div]; ring
  rw [h2, Real.mul_rpow (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ Real.pi / 4)) h0.le,
    Real.inv_rpow (by positivity : (0 : ℝ) ≤ Real.pi / 4),
    ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ Real.pi / 4), neg_neg] at h1
  exact h1

lemma integral_thEta_zero_a {a : ℝ} (ha : 0 < a) (ha4 : a ≤ Real.pi / 4) :
    (∫ θ in (0 : ℝ)..a, σ θ) ≤ (Real.pi / 4) ^ η * a ^ (1 - η) / (1 - η) := by
  have h0a : (0 : ℝ) ≤ a := ha.le
  have hint1 : IntervalIntegrable σ volume 0 a := by
    rw [intervalIntegrable_iff]
    refine (Work.FTS.EllipticEst.integrableOn_thEta.1).mono_set ?_
    intro θ hθ
    rw [Set.uIoc_of_le ha.le] at hθ
    exact ⟨le_of_lt hθ.1, by linarith [hθ.2, ha4, Real.pi_pos]⟩
  have hint2 : IntervalIntegrable (fun θ : ℝ => (Real.pi / 4) ^ η * θ ^ (-η)) volume 0 a :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith [eta_lt_one] : -1 < -η)).const_mul _
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) a, σ θ ≤ (Real.pi / 4) ^ η * θ ^ (-η) :=
    fun θ hθ => thEta_le_rpow hθ.1 (by linarith [hθ.2, ha4])
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo h0a hint1 hint2 hpt
  have hval : (∫ θ in (0 : ℝ)..a, (Real.pi / 4) ^ η * θ ^ (-η))
      = (Real.pi / 4) ^ η * (a ^ (1 - η) / (1 - η)) := by
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith [eta_lt_one] : -1 < -η))]
    rw [show -η + 1 = 1 - η by ring, Real.zero_rpow (x := 1 - η) one_sub_eta_ne]
    ring
  calc (∫ θ in (0 : ℝ)..a, σ θ)
      ≤ ∫ θ in (0 : ℝ)..a, (Real.pi / 4) ^ η * θ ^ (-η) := hmono
    _ = (Real.pi / 4) ^ η * (a ^ (1 - η) / (1 - η)) := hval
    _ = (Real.pi / 4) ^ η * a ^ (1 - η) / (1 - η) := by ring

lemma integral_thEta_half_a {a : ℝ} (ha : 0 < a) (ha4 : a ≤ Real.pi / 4) :
    (∫ θ in a / 2..a, σ θ) ≤ (Real.pi / 4) ^ η * a ^ (1 - η) / (1 - η) := by
  have hh : a / 2 ≤ a := by linarith
  have hint1 : IntervalIntegrable σ volume (a / 2) a := by
    rw [intervalIntegrable_iff]
    refine (Work.FTS.EllipticEst.integrableOn_thEta.1).mono_set ?_
    intro θ hθ
    rw [Set.uIoc_of_le hh] at hθ
    exact ⟨by linarith [hθ.1, ha], by linarith [hθ.2, ha4, Real.pi_pos]⟩
  have hint2 : IntervalIntegrable (fun θ : ℝ => (Real.pi / 4) ^ η * θ ^ (-η)) volume (a / 2) a :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith [eta_lt_one] : -1 < -η)).const_mul _
  have hpt : ∀ θ ∈ Set.Ioo (a / 2) a, σ θ ≤ (Real.pi / 4) ^ η * θ ^ (-η) :=
    fun θ hθ => thEta_le_rpow (by linarith [hθ.1, ha]) (by linarith [hθ.2, ha4])
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hh hint1 hint2 hpt
  have hval : (∫ θ in a / 2..a, (Real.pi / 4) ^ η * θ ^ (-η))
      = (Real.pi / 4) ^ η * ((a ^ (1 - η) - (a / 2) ^ (1 - η)) / (1 - η)) := by
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith [eta_lt_one] : -1 < -η))]
    rw [show -η + 1 = 1 - η by ring]
  have hK : 0 < (Real.pi / 4) ^ η := Real.rpow_pos_of_pos (by positivity) _
  have h2 : (0 : ℝ) ≤ (a / 2) ^ (1 - η) := Real.rpow_nonneg (by positivity) _
  have h3 : 0 < 1 - η := one_sub_eta_pos
  calc (∫ θ in a / 2..a, σ θ)
      ≤ ∫ θ in a / 2..a, (Real.pi / 4) ^ η * θ ^ (-η) := hmono
    _ = (Real.pi / 4) ^ η * ((a ^ (1 - η) - (a / 2) ^ (1 - η)) / (1 - η)) := hval
    _ = (Real.pi / 4) ^ η * ((a ^ (1 - η) - (a / 2) ^ (1 - η)) * (1 - η)⁻¹) := by ring
    _ ≤ (Real.pi / 4) ^ η * a ^ (1 - η) * (1 - η)⁻¹ := by
        calc (Real.pi / 4) ^ η * ((a ^ (1 - η) - (a / 2) ^ (1 - η)) * (1 - η)⁻¹)
            = ((Real.pi / 4) ^ η * (a ^ (1 - η) - (a / 2) ^ (1 - η))) * (1 - η)⁻¹ := by ring
          _ ≤ ((Real.pi / 4) ^ η * a ^ (1 - η)) * (1 - η)⁻¹ :=
              mul_le_mul_of_nonneg_right (by nlinarith [hK, h2]) (inv_nonneg.mpr h3.le)
          _ = (Real.pi / 4) ^ η * a ^ (1 - η) * (1 - η)⁻¹ := by ring
    _ = (Real.pi / 4) ^ η * a ^ (1 - η) / (1 - η) := by ring

/-- `σ` is invariant under the reflection `θ ↦ π/2 - θ`. -/
lemma integrand_sub_pi_div_two (x : ℝ) : σ (Real.pi / 2 - x) = σ x := by
  simp only [Work.FTS.EllipticEst.thEta]
  rw [show 2 * (Real.pi / 2 - x) = Real.pi - 2 * x by ring, Real.sin_pi_sub]

lemma integral_thEta_right_layer {a : ℝ} (ha : 0 < a) (ha4 : a ≤ Real.pi / 4) :
    (∫ θ in (Real.pi / 2 - a)..(Real.pi / 2), σ θ)
      ≤ (Real.pi / 4) ^ η * a ^ (1 - η) / (1 - η) := by
  have h := intervalIntegral.integral_comp_sub_left (a := Real.pi / 2 - a) (b := Real.pi / 2)
    (fun θ : ℝ => σ θ) (Real.pi / 2)
  rw [show Real.pi / 2 - (Real.pi / 2 - a) = a by ring,
    show Real.pi / 2 - Real.pi / 2 = (0 : ℝ) by ring] at h
  rw [show (fun x : ℝ => σ (Real.pi / 2 - x)) = σ from funext integrand_sub_pi_div_two] at h
  rw [h]
  exact integral_thEta_zero_a ha ha4

lemma integral_thEta_right_layer2 {a : ℝ} (ha : 0 < a) (ha4 : a ≤ Real.pi / 4) :
    (∫ θ in (Real.pi / 2 - a)..(Real.pi / 2 - a / 2), σ θ)
      ≤ (Real.pi / 4) ^ η * a ^ (1 - η) / (1 - η) := by
  have h := intervalIntegral.integral_comp_sub_left (a := Real.pi / 2 - a)
    (b := Real.pi / 2 - a / 2) (fun θ : ℝ => σ θ) (Real.pi / 2)
  rw [show Real.pi / 2 - (Real.pi / 2 - a / 2) = a / 2 by ring,
    show Real.pi / 2 - (Real.pi / 2 - a) = a by ring] at h
  rw [show (fun x : ℝ => σ (Real.pi / 2 - x)) = σ from funext integrand_sub_pi_div_two] at h
  rw [h]
  exact integral_thEta_half_a ha ha4

/-! ## The generic two-layer bound -/

lemma integrable_indicator_thEta {S : Set ℝ} (hS : MeasurableSet S) :
    Integrable (fun θ : ℝ => Set.indicator S (fun _ => (1 : ℝ)) θ * σ θ)
      (volume.restrict Work.Spaces.Iθ) := by
  refine Integrable.mono' (Work.FTS.EllipticEst.integrableOn_thEta.1) ?_ ?_
  · exact ((measurable_const.indicator hS).mul measurable_thEta).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    have hth : 0 ≤ σ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
    by_cases h : θ ∈ S
    · rw [Set.indicator_of_mem h, one_mul, Real.norm_of_nonneg hth]
    · rw [Set.indicator_of_notMem h, zero_mul, norm_zero]
      exact hth

/-- If `F` vanishes off the union of the two closed layers `Icc c₁ d₁`, `Icc c₂ d₂` and
satisfies `|F| ≤ K`, then `∫_{Iθ} σ F²` is bounded by `K² L₁ + K² L₂`, where `Lᵢ` bounds the
integrals of `σ` over the two layers. -/
lemma integral_two_layer_le {F : ℝ → ℝ} {K c₁ d₁ c₂ d₂ L₁ L₂ : ℝ}
    (hc₁ : c₁ ≤ d₁) (hc₂ : c₂ ≤ d₂)
    (hsub₁ : Set.Icc c₁ d₁ ⊆ Work.Spaces.Iθ) (hsub₂ : Set.Icc c₂ d₂ ⊆ Work.Spaces.Iθ)
    (hint : IntegrableOn (fun θ : ℝ => σ θ * (F θ) ^ 2) Work.Spaces.Iθ)
    (hb : ∀ θ : ℝ, |F θ| ≤ K)
    (hsupp : ∀ θ ∈ Work.Spaces.Iθ, θ ∉ Set.Icc c₁ d₁ ∪ Set.Icc c₂ d₂ → F θ = 0)
    (hL₁ : (∫ θ in c₁..d₁, σ θ) ≤ L₁) (hL₂ : (∫ θ in c₂..d₂, σ θ) ≤ L₂) :
    ∫ θ in Work.Spaces.Iθ, σ θ * (F θ) ^ 2 ≤ K ^ 2 * L₁ + K ^ 2 * L₂ := by
  have hS₁ : MeasurableSet (Set.Icc c₁ d₁) := measurableSet_Icc
  have hS₂ : MeasurableSet (Set.Icc c₂ d₂) := measurableSet_Icc
  have hpt : ∀ θ ∈ Work.Spaces.Iθ, σ θ * (F θ) ^ 2
      ≤ K ^ 2 * (Set.indicator (Set.Icc c₁ d₁) (fun _ => (1 : ℝ)) θ * σ θ)
        + K ^ 2 * (Set.indicator (Set.Icc c₂ d₂) (fun _ => (1 : ℝ)) θ * σ θ) := by
    intro θ hθ
    have hth : 0 ≤ σ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
    have hsq : (F θ) ^ 2 ≤ K ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (F θ)) (hb θ) 2
      rwa [sq_abs] at h
    have hkey : σ θ * (F θ) ^ 2 ≤ K ^ 2 * σ θ := by
      calc σ θ * (F θ) ^ 2 ≤ σ θ * K ^ 2 := mul_le_mul_of_nonneg_left hsq hth
        _ = K ^ 2 * σ θ := by ring
    have hι₁ : 0 ≤ Set.indicator (Set.Icc c₁ d₁) (fun _ => (1 : ℝ)) θ :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) θ
    have hι₂ : 0 ≤ Set.indicator (Set.Icc c₂ d₂) (fun _ => (1 : ℝ)) θ :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) θ
    rcases em (θ ∈ Set.Icc c₁ d₁) with h1 | h1
    · have e : K ^ 2 * (Set.indicator (Set.Icc c₁ d₁) (fun _ => (1 : ℝ)) θ * σ θ)
          = K ^ 2 * σ θ := by rw [Set.indicator_of_mem h1, one_mul]
      have hrem : 0 ≤ K ^ 2 * (Set.indicator (Set.Icc c₂ d₂) (fun _ => (1 : ℝ)) θ * σ θ) :=
        mul_nonneg (sq_nonneg K) (mul_nonneg hι₂ hth)
      rw [e]; linarith
    · rcases em (θ ∈ Set.Icc c₂ d₂) with h2 | h2
      · have e : K ^ 2 * (Set.indicator (Set.Icc c₂ d₂) (fun _ => (1 : ℝ)) θ * σ θ)
            = K ^ 2 * σ θ := by rw [Set.indicator_of_mem h2, one_mul]
        have hrem : 0 ≤ K ^ 2 * (Set.indicator (Set.Icc c₁ d₁) (fun _ => (1 : ℝ)) θ * σ θ) :=
          mul_nonneg (sq_nonneg K) (mul_nonneg hι₁ hth)
        rw [e]; linarith
      · have hF0 : F θ = 0 := hsupp θ hθ (by
          simp only [Set.mem_union, not_or]
          exact ⟨h1, h2⟩)
        have e₁ : Set.indicator (Set.Icc c₁ d₁) (fun _ => (1 : ℝ)) θ = 0 :=
          Set.indicator_of_notMem h1 _
        have e₂ : Set.indicator (Set.Icc c₂ d₂) (fun _ => (1 : ℝ)) θ = 0 :=
          Set.indicator_of_notMem h2 _
        rw [hF0, e₁, e₂]
        simp
  have hintR : Integrable (fun θ : ℝ =>
      K ^ 2 * (Set.indicator (Set.Icc c₁ d₁) (fun _ => (1 : ℝ)) θ * σ θ)
        + K ^ 2 * (Set.indicator (Set.Icc c₂ d₂) (fun _ => (1 : ℝ)) θ * σ θ))
      (volume.restrict Work.Spaces.Iθ) :=
    ((integrable_indicator_thEta hS₁).const_mul (K ^ 2)).add
      ((integrable_indicator_thEta hS₂).const_mul (K ^ 2))
  have hmono := integral_mono_ae hint hintR (ae_restrict_of_forall_mem measurableSet_Icc hpt)
  have hval₁ : (∫ θ : ℝ, Set.indicator (Set.Icc c₁ d₁) (fun _ => (1 : ℝ)) θ * σ θ
      ∂(volume.restrict Work.Spaces.Iθ)) = ∫ θ in c₁..d₁, σ θ := by
    have h1 : (∫ θ : ℝ, Set.indicator (Set.Icc c₁ d₁) (fun _ => (1 : ℝ)) θ * σ θ
        ∂(volume.restrict Work.Spaces.Iθ))
        = ∫ θ : ℝ, Set.indicator (Set.Icc c₁ d₁) (fun θ => σ θ) θ
            ∂(volume.restrict Work.Spaces.Iθ) := by
      refine integral_congr_ae ?_
      filter_upwards with θ
      by_cases h : θ ∈ Set.Icc c₁ d₁
      · rw [Set.indicator_of_mem h, one_mul, Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, zero_mul, Set.indicator_of_notMem h]
    rw [h1, MeasureTheory.integral_indicator hS₁, Measure.restrict_restrict hS₁,
      Set.inter_comm, Set.inter_eq_right.mpr hsub₁]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hc₁]
  have hval₂ : (∫ θ : ℝ, Set.indicator (Set.Icc c₂ d₂) (fun _ => (1 : ℝ)) θ * σ θ
      ∂(volume.restrict Work.Spaces.Iθ)) = ∫ θ in c₂..d₂, σ θ := by
    have h1 : (∫ θ : ℝ, Set.indicator (Set.Icc c₂ d₂) (fun _ => (1 : ℝ)) θ * σ θ
        ∂(volume.restrict Work.Spaces.Iθ))
        = ∫ θ : ℝ, Set.indicator (Set.Icc c₂ d₂) (fun θ => σ θ) θ
            ∂(volume.restrict Work.Spaces.Iθ) := by
      refine integral_congr_ae ?_
      filter_upwards with θ
      by_cases h : θ ∈ Set.Icc c₂ d₂
      · rw [Set.indicator_of_mem h, one_mul, Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, zero_mul, Set.indicator_of_notMem h]
    rw [h1, MeasureTheory.integral_indicator hS₂, Measure.restrict_restrict hS₂,
      Set.inter_comm, Set.inter_eq_right.mpr hsub₂]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hc₂]
  have hsplit : (∫ θ : ℝ, K ^ 2 * (Set.indicator (Set.Icc c₁ d₁) (fun _ => (1 : ℝ)) θ * σ θ)
        + K ^ 2 * (Set.indicator (Set.Icc c₂ d₂) (fun _ => (1 : ℝ)) θ * σ θ)
        ∂(volume.restrict Work.Spaces.Iθ))
      = K ^ 2 * (∫ θ in c₁..d₁, σ θ) + K ^ 2 * (∫ θ in c₂..d₂, σ θ) := by
    rw [integral_add ((integrable_indicator_thEta hS₁).const_mul (K ^ 2))
        ((integrable_indicator_thEta hS₂).const_mul (K ^ 2)),
      integral_const_mul, integral_const_mul, hval₁, hval₂]
  calc ∫ θ in Work.Spaces.Iθ, σ θ * (F θ) ^ 2
      = ∫ θ : ℝ, σ θ * (F θ) ^ 2 ∂(volume.restrict Work.Spaces.Iθ) := rfl
    _ ≤ ∫ θ : ℝ, K ^ 2 * (Set.indicator (Set.Icc c₁ d₁) (fun _ => (1 : ℝ)) θ * σ θ)
          + K ^ 2 * (Set.indicator (Set.Icc c₂ d₂) (fun _ => (1 : ℝ)) θ * σ θ)
          ∂(volume.restrict Work.Spaces.Iθ) := hmono
    _ = K ^ 2 * (∫ θ in c₁..d₁, σ θ) + K ^ 2 * (∫ θ in c₂..d₂, σ θ) := hsplit
    _ ≤ K ^ 2 * L₁ + K ^ 2 * L₂ := by
        have h1 := mul_le_mul_of_nonneg_left hL₁ (sq_nonneg K)
        have h2 := mul_le_mul_of_nonneg_left hL₂ (sq_nonneg K)
        linarith

/-! ## Integrability of `σ F²` -/

lemma integrableOn_thEta_mul_sq {F : ℝ → ℝ} {K : ℝ} (hcont : Continuous F)
    (hb : ∀ θ : ℝ, |F θ| ≤ K) :
    IntegrableOn (fun θ : ℝ => σ θ * (F θ) ^ 2) Work.Spaces.Iθ := by
  have hg : Integrable (fun θ : ℝ => K ^ 2 * σ θ) (volume.restrict Work.Spaces.Iθ) :=
    (Work.FTS.EllipticEst.integrableOn_thEta.1).const_mul (K ^ 2)
  refine Integrable.mono' hg ?_ ?_
  · exact measurable_thEta.aestronglyMeasurable.mul (hcont.aestronglyMeasurable.pow 2)
  · refine ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    have hth : 0 ≤ σ θ := Work.FTS.EllipticEst.thEta_nonneg hθ
    have hsq : (F θ) ^ 2 ≤ K ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (F θ)) (hb θ) 2
      rwa [sq_abs] at h
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hth (sq_nonneg _))]
    calc σ θ * (F θ) ^ 2 ≤ σ θ * K ^ 2 := mul_le_mul_of_nonneg_left hsq hth
      _ = K ^ 2 * σ θ := by ring

end Work.FTS.EllSol
