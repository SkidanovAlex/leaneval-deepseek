import Mathlib

/-!
# The planar Cauchy kernel: local integrability

The Cauchy–Pompeiu solution of `∂̄u = ω` on `ℂ` is the Cauchy transform

  `u z = ∫ ζ, ω ζ / (ζ - z)`  (area measure on `ℂ ≅ ℝ²`),

and the first prerequisite for it — missing from Mathlib, which only has the abstract
`MeasureTheory.locallyIntegrable_of_norm_le_rpow` criterion — is the local integrability of the
kernel `ζ ↦ (ζ - z)⁻¹`, i.e. of `ζ ↦ 1/‖ζ - z‖` in dimension two.

This module records

* `locallyIntegrable_inv_sub` — `ζ ↦ (ζ - z)⁻¹` is locally integrable on `ℂ`;
* `integrableOn_inv_sub_compact` — it is integrable on every compact set;
* `integrable_div_sub` — for compactly supported `ω`, `ζ ↦ ω ζ / (ζ - z)` is integrable.

The first two are proved directly from Mathlib's general criterion for `‖x‖ ^ (-α)` decay with
`α < finrank ℝ ℂ = 2`, plus translation invariance of Lebesgue measure; they are the `L¹` input of
the Cauchy–Pompeiu formula.
-/

open MeasureTheory
open scoped Topology

noncomputable section

namespace Work.Analysis.RiemannSurface

/-- **The Cauchy kernel is locally integrable.**  `ζ ↦ (ζ - z)⁻¹` is locally integrable on `ℂ`
for every `z`. -/
theorem locallyIntegrable_inv_sub (z : ℂ) :
    LocallyIntegrable (fun ζ : ℂ => (ζ - z)⁻¹) volume := by
  -- at the origin the criterion `‖x‖ ^ (-α)` with `α = 1 < finrank ℝ ℂ = 2` applies
  have h0 : LocallyIntegrable (fun w : ℂ => w⁻¹) volume := by
    refine locallyIntegrable_of_norm_le_rpow (E := ℂ) (F := ℂ) (f := fun w : ℂ => w⁻¹)
      (C := 1) (α := 1) ?_ ?_ ?_ ?_
    · rw [Complex.finrank_real_complex]; norm_num
    · rw [Complex.finrank_real_complex]; norm_num
    · filter_upwards with x
      rw [norm_inv, Real.rpow_neg_one, one_mul]
    · exact measurable_inv.aestronglyMeasurable
  -- translate to `z` using invariance of Lebesgue measure
  have hmap : Measure.map (fun x : ℂ => x + (-z)) volume = volume :=
    map_add_right_eq_self volume (-z)
  change LocallyIntegrable (fun ζ : ℂ => (ζ + (-z))⁻¹) volume
  exact (locallyIntegrable_map_homeomorph (Homeomorph.addRight (-z))).mp (by
    change LocallyIntegrable (fun w : ℂ => w⁻¹) (Measure.map (fun x : ℂ => x + (-z)) volume)
    rw [hmap]
    exact h0)

/-- **The Cauchy kernel is integrable on compact sets.** -/
theorem integrableOn_inv_sub_compact {K : Set ℂ} (hK : IsCompact K) (z : ℂ) :
    IntegrableOn (fun ζ : ℂ => (ζ - z)⁻¹) K volume :=
  (locallyIntegrable_inv_sub z).integrableOn_isCompact hK



/-- **The Cauchy transform integrand is integrable.**  For a continuous `ω` with compact support
and every `z`, the function `ζ ↦ ω ζ / (ζ - z)` is integrable on `ℂ` (area measure): it is locally
integrable (a continuous function times the locally integrable Cauchy kernel) and vanishes outside
the compact support of `ω`. -/
theorem integrable_div_sub {ω : ℂ → ℂ} (hω : Continuous ω) (hc : HasCompactSupport ω) (z : ℂ) :
    Integrable (fun ζ : ℂ => ω ζ / (ζ - z)) volume := by
  rw [integrable_iff_integrableAtFilter_cocompact]
  refine ⟨?_, ?_⟩
  · -- outside the (compact) support of `ω` the integrand vanishes
    refine ⟨(tsupport ω)ᶜ, Filter.mem_cocompact.mpr ⟨tsupport ω, hc, subset_rfl⟩, ?_⟩
    refine integrableOn_zero.congr_fun ?_ (isClosed_tsupport ω).isOpen_compl.measurableSet
    intro ζ hζ
    have hζ' : ζ ∉ Function.support ω := fun h => hζ (subset_tsupport ω h)
    have hz0 : ω ζ = 0 := by
      by_contra h
      exact hζ' (Function.mem_support.mpr h)
    change (0 : ℂ) = ω ζ / (ζ - z)
    rw [hz0, zero_div]
  · 
    have hker : LocallyIntegrable (fun ζ : ℂ => (ζ - z)⁻¹) volume := locallyIntegrable_inv_sub z
    have hloc : LocallyIntegrable (fun ζ : ℂ => (ζ - z)⁻¹ * ω ζ) volume :=
      hker.mul_continuous hω
    refine hloc.congr (Filter.Eventually.of_forall fun ζ => ?_)
    change (ζ - z)⁻¹ * ω ζ = ω ζ / (ζ - z)
    rw [div_eq_mul_inv, mul_comm]

end Work.Analysis.RiemannSurface
