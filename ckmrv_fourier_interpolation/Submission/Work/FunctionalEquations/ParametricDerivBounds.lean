import Mathlib

open Filter Topology MeasureTheory

namespace Work.FunctionalEquations

open scoped Interval ContDiff

/-- **Iterated differentiation under the interval integral sign, with a uniform bound.**
Let `K : ℝ → ℝ → ℂ` be a family of smooth functions of the second variable, measurable in the
first variable, whose `j`-th derivatives in the second variable are bounded by `C j` uniformly
for `t ∈ [0,1]` and `r : ℝ`, for all `j ≤ ℓ + 1`.  Then, for every `j ≤ ℓ`,

* `t ↦ iteratedDeriv j (K t) r` is measurable,
* the `j`-th derivative of the parametric integral `r ↦ ∫ t in (0:ℝ)..1, K t r` is the integral
  of the `j`-th derivatives,
* and it is bounded by `C j`. -/
theorem ParametricDerivBounds {K : ℝ → ℝ → ℂ} {ℓ : ℕ}
    (hK : ∀ t, ContDiff ℝ ⊤ (K t))
    (hmeas : ∀ r : ℝ, Measurable fun t : ℝ => K t r)
    (C : ℕ → ℝ) (hC0 : ∀ j : ℕ, 0 ≤ C j)
    (hb : ∀ j ≤ ℓ + 1, ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ r : ℝ, ‖iteratedDeriv j (K t) r‖ ≤ C j) :
    (∀ j ≤ ℓ, ∀ r : ℝ, Measurable fun t : ℝ => iteratedDeriv j (K t) r) ∧
    (∀ j ≤ ℓ, ∀ r : ℝ,
      iteratedDeriv j (fun r => ∫ t in (0:ℝ)..1, K t r) r
        = ∫ t in (0:ℝ)..1, iteratedDeriv j (K t) r) ∧
    (∀ j ≤ ℓ, ∀ r : ℝ, ‖iteratedDeriv j (fun r => ∫ t in (0:ℝ)..1, K t r) r‖ ≤ C j) := by
  have hderiv_gen : ∀ (j : ℕ) (t x : ℝ),
      HasDerivAt (fun y : ℝ => iteratedDeriv j (K t) y) (iteratedDeriv (j+1) (K t) x) x := by
    intro j t x
    have hgs : ContDiff ℝ ∞ (iteratedDeriv j (K t)) := by
      rw [iteratedDeriv_eq_iterate]
      exact ContDiff.iterate_deriv j ((hK t).of_le le_top)
    have hd : Differentiable ℝ (iteratedDeriv j (K t)) := (contDiff_infty_iff_deriv.mp hgs).1
    rw [iteratedDeriv_succ]
    exact (hd x).hasDerivAt
  have hmeas_all : ∀ j : ℕ, ∀ r : ℝ, Measurable fun t : ℝ => iteratedDeriv j (K t) r := by
    intro j
    induction j with
    | zero =>
      intro r
      simpa [iteratedDeriv_zero] using hmeas r
    | succ j ih =>
      intro r
      have ha : Filter.Tendsto (fun n : ℕ => (1:ℝ)/(n+1)) Filter.atTop (𝓝[≠] (0:ℝ)) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · exact tendsto_one_div_add_atTop_nhds_zero_nat
        · exact Filter.Eventually.of_forall (fun n => ne_of_gt (div_pos one_pos (by positivity)))
      have hf_meas : ∀ n : ℕ, Measurable (fun t : ℝ =>
          ((1:ℝ)/(n+1))⁻¹ • (iteratedDeriv j (K t) (r + (1:ℝ)/(n+1))
            - iteratedDeriv j (K t) r)) := by
        intro n
        have h1 : Measurable (fun t : ℝ => iteratedDeriv j (K t) (r + (1:ℝ)/(n+1))) :=
          ih (r + (1:ℝ)/(n+1))
        have h2 : Measurable (fun t : ℝ => iteratedDeriv j (K t) r) := ih r
        exact (h1.sub h2).const_smul (c := ((1:ℝ)/(n+1))⁻¹)
      refine measurable_of_tendsto_metrizable hf_meas ?_
      rw [tendsto_pi_nhds]
      intro t
      exact (hderiv_gen j t r).tendsto_slope_zero.comp ha
  have huIoc : Set.uIoc (0:ℝ) 1 ⊆ Set.Icc (0:ℝ) 1 := by
    rw [← Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Set.uIoc_subset_uIcc
  have hint : ∀ (j : ℕ) (x₀ : ℝ), j ≤ ℓ + 1 →
      IntervalIntegrable (fun t : ℝ => iteratedDeriv j (K t) x₀) volume 0 1 := by
    intro j x₀ hj
    rw [intervalIntegrable_iff]
    refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => C j)
      (intervalIntegrable_iff.mp
        (intervalIntegrable_const (c := C j) (μ := volume) (a := (0:ℝ)) (b := 1)))
      (hmeas_all j x₀).aestronglyMeasurable ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    exact Filter.Eventually.of_forall (fun t ht => hb j hj t (huIoc ht) x₀)
  have hinter : ∀ j : ℕ, j ≤ ℓ →
      iteratedDeriv j (fun r => ∫ t in (0:ℝ)..1, K t r)
        = fun r => ∫ t in (0:ℝ)..1, iteratedDeriv j (K t) r := by
    intro j
    induction j with
    | zero =>
      intro _
      funext r
      simp [iteratedDeriv_zero]
    | succ j ih =>
      intro hj
      have hj' : j ≤ ℓ := Nat.le_of_succ_le hj
      rw [iteratedDeriv_succ, ih hj']
      funext x₀
      have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
          (μ := volume) (a := (0:ℝ)) (b := 1)
          (F := fun x : ℝ => fun t : ℝ => iteratedDeriv j (K t) x)
          (F' := fun x : ℝ => fun t : ℝ => iteratedDeriv (j+1) (K t) x)
          (bound := fun _ : ℝ => C (j+1)) (x₀ := x₀) (s := Set.univ)
          Filter.univ_mem
          (Filter.Eventually.of_forall (fun x => (hmeas_all j x).aestronglyMeasurable))
          (hint j x₀ (Nat.le_succ_of_le hj'))
          (hmeas_all (j+1) x₀).aestronglyMeasurable
          (Filter.Eventually.of_forall (fun t ht x _ => hb (j+1) (by omega) t (huIoc ht) x))
          intervalIntegrable_const
          (Filter.Eventually.of_forall (fun t ht x _ => hderiv_gen j t x))
      simpa using key.2.deriv
  refine ⟨fun j hj r => hmeas_all j r, fun j hj r => congrFun (hinter j hj) r, ?_⟩
  intro j hj r
  rw [congrFun (hinter j hj) r]
  calc ‖∫ t in (0:ℝ)..1, iteratedDeriv j (K t) r‖
      ≤ C j * |(1:ℝ) - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (fun t ht => hb j (by omega) t (huIoc ht) r)
    _ = C j := by norm_num

end Work.FunctionalEquations
