import Mathlib
import Submission.Commons.NumberTheory.Linnik.partialFraction_tail

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex DirichletCharacter Metric Filter Topology
open scoped Real BigOperators
set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.Linnik

lemma log_div_self_tendsto_zero :
    Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
  simpa using (Real.tendsto_pow_log_div_mul_add_atTop (a := (1 : ℝ)) (b := (0 : ℝ)) (n := 1) one_ne_zero)

lemma add_two_tendsto_atTop : Tendsto (fun R : ℝ => R + 2) atTop atTop := by
  simpa using (Filter.tendsto_atTop_add_const_right atTop (2 : ℝ) Filter.tendsto_id)

lemma log_add_two_div_add_two_tendsto_zero :
    Tendsto (fun R : ℝ => Real.log (R + 2) / (R + 2)) atTop (𝓝 0) := by
  simpa [Function.comp_def] using (log_div_self_tendsto_zero.comp add_two_tendsto_atTop)

lemma ratio_add_two_div_self_tendsto_one :
    Tendsto (fun R : ℝ => (R + 2) / R) atTop (𝓝 1) := by
  have hinv : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have htwo : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hsum : Tendsto (fun R : ℝ => (1 : ℝ) + (2 : ℝ) * R⁻¹) atTop (𝓝 1) := by
    have hprod : Tendsto (fun R : ℝ => (2 : ℝ) * R⁻¹) atTop (𝓝 (0 : ℝ)) := by
      simpa using htwo.mul hinv
    simpa using hone.add hprod
  have heq : (fun R : ℝ => (1 : ℝ) + (2 : ℝ) * R⁻¹) =ᶠ[atTop] fun R : ℝ => (R + 2) / R := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hRne : R ≠ 0 := ne_of_gt hR
    field_simp [hRne]
  simpa using hsum.congr' heq

lemma log_add_two_div_self_tendsto_zero :
    Tendsto (fun R : ℝ => Real.log (R + 2) / R) atTop (𝓝 0) := by
  have hmain : Tendsto (fun R : ℝ => (Real.log (R + 2) / (R + 2)) * ((R + 2) / R)) atTop (𝓝 0) := by
    simpa using (log_add_two_div_add_two_tendsto_zero.mul ratio_add_two_div_self_tendsto_one)
  have heq : (fun R : ℝ => (Real.log (R + 2) / (R + 2)) * ((R + 2) / R)) =ᶠ[atTop]
      fun R : ℝ => Real.log (R + 2) / R := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hR2 : R + 2 ≠ 0 := by linarith
    field_simp [hR2]
  simpa using hmain.congr' heq

lemma log_add_two_add_const_div_self_tendsto_zero (D : ℝ) :
    Tendsto (fun R : ℝ => (Real.log (R + 2) + D) / R) atTop (𝓝 0) := by
  have hD : Tendsto (fun R : ℝ => D / R) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℝ => D) atTop (𝓝 D) := tendsto_const_nhds
    have hinv : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa [div_eq_mul_inv] using hconst.mul hinv
  have hsum : Tendsto (fun R : ℝ => Real.log (R + 2) / R + D / R) atTop (𝓝 0) := by
    simpa using (log_add_two_div_self_tendsto_zero.add hD)
  have heq : (fun R : ℝ => Real.log (R + 2) / R + D / R) =ᶠ[atTop]
      fun R : ℝ => (Real.log (R + 2) + D) / R := by
    filter_upwards with R
    rw [add_div]
  simpa using hsum.congr' heq

lemma bound_tendsto_zero {N : ℕ} [NeZero N] (A : ℝ) :
    Tendsto (fun R : ℝ => A * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R) atTop (𝓝 0) := by
  have hT : Tendsto (fun R : ℝ => (Real.log (R + 2) + (Real.log (N : ℝ) + 2)) / R) atTop (𝓝 0) :=
    log_add_two_add_const_div_self_tendsto_zero (Real.log (N : ℝ) + 2)
  have hconst : Tendsto (fun _ : ℝ => A) atTop (𝓝 A) := tendsto_const_nhds
  have hmain : Tendsto (fun R : ℝ => A * ((Real.log (R + 2) + (Real.log (N : ℝ) + 2)) / R)) atTop (𝓝 0) := by
    simpa using hconst.mul hT
  have heq : (fun R : ℝ => A * ((Real.log (R + 2) + (Real.log (N : ℝ) + 2)) / R)) =ᶠ[atTop]
      fun R : ℝ => A * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := by
    filter_upwards with R
    ring
  simpa using hmain.congr' heq

theorem partialFraction_conv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (s : ℂ) :
    ∃ L : ℂ, Tendsto (fun R : ℝ =>
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u))) atTop (nhds L) := by
  classical
  let F : ℝ → ℂ := fun R =>
        ∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R)) u : ℤ) : ℂ) * (1 / (s - u) + 1 / u)
  let T : ℝ → ℝ := fun R => Real.log (R + 2) + Real.log (N : ℝ) + 2
  rcases Commons.NumberTheory.Linnik.partialFraction_tail χ hχ hχprim with ⟨c, hc⟩
  have hb : ∀ ⦃R R' : ℝ⦄, 2 ≤ R → R ≤ R' → ‖s‖ ≤ R / 4 →
      ‖F R' - F R‖ ≤ c * ‖s‖ * T R / R := by
    intro R R' hR hRR' hs
    simpa [F, T] using hc s R R' hR hRR' hs
  have hdec : Tendsto (fun R : ℝ => c * ‖s‖ * T R / R) atTop (𝓝 0) := by
    dsimp [T]
    simpa using (bound_tendsto_zero (N := N) (A := c * ‖s‖))
  have hcauchy : ∀ ε > 0, ∃ R₀ : ℝ, ∀ R R' : ℝ, R₀ ≤ R → R₀ ≤ R' → ‖F R - F R'‖ < ε := by
    intro ε hε
    have hsmall : ∀ᶠ R : ℝ in atTop, c * ‖s‖ * T R / R < ε := by
      simpa [T] using hdec.eventually (Iio_mem_nhds hε)
    rcases (Filter.eventually_atTop.mp hsmall) with ⟨R₁, hR₁⟩
    let base : ℝ := max 2 (max (4 * ‖s‖) R₁)
    refine ⟨base, ?_⟩
    intro R R' hR₀R hR₀R'
    have h2R : 2 ≤ R := le_trans (le_max_left 2 (max (4 * ‖s‖) R₁)) hR₀R
    have h2R' : 2 ≤ R' := le_trans (le_max_left 2 (max (4 * ‖s‖) R₁)) hR₀R'
    have h4sR : (4 : ℝ) * ‖s‖ ≤ R := by
      exact le_trans (le_trans (le_max_left (4 * ‖s‖) R₁)
        (le_max_right 2 (max (4 * ‖s‖) R₁))) hR₀R
    have h4sR' : (4 : ℝ) * ‖s‖ ≤ R' := by
      exact le_trans (le_trans (le_max_left (4 * ‖s‖) R₁)
        (le_max_right 2 (max (4 * ‖s‖) R₁))) hR₀R'
    have hsR : ‖s‖ ≤ R / 4 := by nlinarith
    have hsR' : ‖s‖ ≤ R' / 4 := by nlinarith
    have hR1R : R₁ ≤ R := by
      exact le_trans (le_trans (le_max_right (4 * ‖s‖) R₁)
        (le_max_right 2 (max (4 * ‖s‖) R₁))) hR₀R
    have hR1R' : R₁ ≤ R' := by
      exact le_trans (le_trans (le_max_right (4 * ‖s‖) R₁)
        (le_max_right 2 (max (4 * ‖s‖) R₁))) hR₀R'
    have gRlt : c * ‖s‖ * T R / R < ε := by
      have h := hR₁ R hR1R
      simpa [T] using h
    have gR'lt : c * ‖s‖ * T R' / R' < ε := by
      have h := hR₁ R' hR1R'
      simpa [T] using h
    by_cases hle : R ≤ R'
    · have hb' := hb h2R hle hsR
      have hlelt : ‖F R - F R'‖ < ε := by
        rw [norm_sub_rev]
        exact lt_of_le_of_lt hb' gRlt
      simpa [dist_eq_norm] using hlelt
    · have hle' : R' ≤ R := le_of_not_ge hle
      have hb' := hb h2R' hle' hsR'
      have hlelt : ‖F R - F R'‖ < ε := lt_of_le_of_lt hb' gR'lt
      simpa [dist_eq_norm] using hlelt
  have hFcauchy : Cauchy (Filter.map F atTop) := by
    rw [cauchy_map_iff]
    constructor
    · exact Filter.atTop_neBot
    · rw [Metric.uniformity_basis_dist.tendsto_right_iff]
      intro ε hε
      rcases hcauchy ε hε with ⟨R₀, hR₀⟩
      rw [Filter.eventually_prod_iff]
      refine ⟨(fun R : ℝ => R₀ ≤ R), ?_, (fun R : ℝ => R₀ ≤ R), ?_, ?_⟩
      · exact (Filter.eventually_atTop.mpr ⟨R₀, fun b hb => hb⟩)
      · exact (Filter.eventually_atTop.mpr ⟨R₀, fun b hb => hb⟩)
      · intro R hR R' hR'
        simpa [dist_eq_norm] using hR₀ R R' hR hR'
  rcases (cauchy_map_iff_exists_tendsto (l := atTop) (f := F)).mp hFcauchy with ⟨L, hL⟩
  refine ⟨L, ?_⟩
  simpa [F] using hL

end Commons.NumberTheory.Linnik
