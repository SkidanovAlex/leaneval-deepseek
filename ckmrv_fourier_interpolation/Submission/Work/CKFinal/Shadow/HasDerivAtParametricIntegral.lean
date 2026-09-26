import Submission.Work.FunctionalEquations.HasDerivAtParametricIntegral
import Submission.Work.CKFinal.Shadow.Util

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow


namespace Work.FunctionalEquations

open scoped Interval ContDiff
open Filter Topology MeasureTheory

/-- **Differentiability of a parametric interval integral of iterated derivatives.**
If `K : ℝ → ℝ → ℂ` is smooth in the second variable, if `t ↦ ∂^j_r K t r` is measurable for every
`r`, and if the derivatives in the second variable up to order `j + 1` are bounded by `C i`
uniformly for `t ∈ [0,1]` and `r : ℝ`, then `r ↦ ∫ t in (0:ℝ)..1, ∂^j_r K t r` is differentiable
at every `r₀`, with derivative the integral of the `(j+1)`-st derivatives.  The bound at order `j`
is what makes the integrand interval-integrable (so that the integral is not the junk value `0`). -/
theorem HasDerivAtParametricIntegral {K : ℝ → ℝ → ℂ} {j : ℕ} {r₀ : ℝ}
    (hK : ∀ t : ℝ, ContDiff ℝ ∞ (K t))
    (hmeas : ∀ r : ℝ, Measurable fun t : ℝ => iteratedDeriv j (K t) r)
    (C : ℕ → ℝ) (hC0 : ∀ i : ℕ, 0 ≤ C i)
    (hb : ∀ i ≤ j + 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ r : ℝ,
      ‖iteratedDeriv i (K t) r‖ ≤ C i) :
    HasDerivAt (fun r : ℝ => ∫ t in (0 : ℝ)..1, iteratedDeriv j (K t) r)
      (∫ t in (0 : ℝ)..1, iteratedDeriv (j + 1) (K t) r₀) r₀ := by
  -- Each slice `K t` is smooth in its second variable, so the `(i+1)`-st derivative is the
  -- derivative of the `i`-th one at every point.
  have hderiv_gen : ∀ (i : ℕ) (t x : ℝ),
      HasDerivAt (fun y : ℝ => iteratedDeriv i (K t) y) (iteratedDeriv (i + 1) (K t) x) x := by
    intro i t x
    have hgs : ContDiff ℝ ∞ (iteratedDeriv i (K t)) := by
      rw [iteratedDeriv_eq_iterate]
      exact ContDiff.iterate_deriv i ((hK t).of_le coe_le_smooth)
    have hd : Differentiable ℝ (iteratedDeriv i (K t)) := (contDiff_infty_iff_deriv.mp hgs).1
    rw [iteratedDeriv_succ]
    exact (hd x).hasDerivAt
  -- Measurability in `t` propagates from order `i` to order `i + 1`: the `(i+1)`-st derivative is
  -- a pointwise limit of the difference quotients of the `i`-th derivative in the second variable.
  have hmeas_succ : ∀ (i : ℕ),
      (∀ r : ℝ, Measurable fun t : ℝ => iteratedDeriv i (K t) r) →
      (∀ r : ℝ, Measurable fun t : ℝ => iteratedDeriv (i + 1) (K t) r) := by
    intro i hi r
    have ha : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝[≠] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact tendsto_one_div_add_atTop_nhds_zero_nat
      · exact Filter.Eventually.of_forall (fun n => ne_of_gt (div_pos one_pos (by positivity)))
    have hf_meas : ∀ n : ℕ, Measurable (fun t : ℝ =>
        ((1 : ℝ) / (n + 1))⁻¹ • (iteratedDeriv i (K t) (r + (1 : ℝ) / (n + 1))
          - iteratedDeriv i (K t) r)) := by
      intro n
      exact ((hi (r + (1 : ℝ) / (n + 1))).sub (hi r)).const_smul (((1 : ℝ) / (n + 1))⁻¹)
    refine measurable_of_tendsto_metrizable hf_meas ?_
    rw [tendsto_pi_nhds]
    intro t
    exact (hderiv_gen i t r).tendsto_slope_zero.comp ha
  have hmeas_j1 : Measurable fun t : ℝ => iteratedDeriv (j + 1) (K t) r₀ :=
    hmeas_succ j hmeas r₀
  have huIoc : Set.uIoc (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := by
    rw [← Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Set.uIoc_subset_uIcc
  -- The `j`-th derivatives are interval-integrable: they are measurable and bounded by the
  -- constant `C j` on `(0,1]`.
  have hint : IntervalIntegrable (fun t : ℝ => iteratedDeriv j (K t) r₀) volume 0 1 := by
    rw [intervalIntegrable_iff]
    refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => C j)
      (intervalIntegrable_iff.mp
        (intervalIntegrable_const (c := C j) (μ := volume) (a := (0 : ℝ)) (b := 1)))
      (hmeas r₀).aestronglyMeasurable ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    exact Filter.Eventually.of_forall (fun t ht => hb j (Nat.le_succ j) t (huIoc ht) r₀)
  -- Differentiate under the interval integral sign.
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := (0 : ℝ)) (b := 1)
      (F := fun x : ℝ => fun t : ℝ => iteratedDeriv j (K t) x)
      (F' := fun x : ℝ => fun t : ℝ => iteratedDeriv (j + 1) (K t) x)
      (bound := fun _ : ℝ => C (j + 1)) (x₀ := r₀) (s := Set.univ)
      Filter.univ_mem
      (Filter.Eventually.of_forall (fun x => (hmeas x).aestronglyMeasurable))
      hint
      hmeas_j1.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t ht x _ => hb (j + 1) le_rfl t (huIoc ht) x))
      (intervalIntegrable_const (c := C (j + 1)) (μ := volume) (a := (0 : ℝ)) (b := 1))
      (Filter.Eventually.of_forall (fun t ht x _ => hderiv_gen j t x))
  exact key.2

end Work.FunctionalEquations


end Work.CKFinal.Shadow
