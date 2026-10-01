import Mathlib
import Submission.Commons.NumberTheory.Linnik.partialFraction_tail

open Complex DirichletCharacter Metric
open scoped Real BigOperators
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Commons.NumberTheory.Linnik

/-!
# The "tiny" region contribution to the partial-fraction divisor sums

For a primitive non-trivial Dirichlet character `χ mod N` we bound the contribution to the
partial-fraction divisor sum coming from zeros of the completed L-function `Λ(s, χ)` lying in the
unit disk `‖u‖ < 1`.

Let `D_T(u)` be the divisor coefficient of `Λ` at `u` in the closed ball `|s| ≤ T`.  For
`R ≥ 2`, `‖w‖ = R` and `T ≥ R + 1`:

1. any `u` with `‖u‖ < 1` automatically satisfies `1 < ‖w - u‖` (reverse triangle inequality and
   `‖u‖ < 1 ≤ R/2`), so the weight
   `‖w‖ / (‖u‖ · ‖w - u‖) ≤ 2 / ‖u‖`;
2. on `‖u‖ < 1` the divisors `D_T(u)` and `D_1(u)` agree
   (`divisor_closedBall_eq_of_le`), and both are non-negative (Λ is entire);

hence the whole sum is bounded, uniformly in `R, w, T`, by the *fixed* constant

`K := ∑ᶠ u, D_1(u) · (if ‖u‖ < 1 then 2/‖u‖ else 0)`,

which is finite because the divisor on the compact ball `closedBall 0 1` has finite support.
-/

/-- The weight bound: for `2 ≤ R = ‖w‖` and `‖u‖ < 1`, `u ≠ 0`,
`‖w‖ / (‖u‖ * ‖w - u‖) ≤ 2 / ‖u‖`. -/
private lemma tiny_weight_le {R : ℝ} (hR : 2 ≤ R) {w u : ℂ} (hw : ‖w‖ = R)
    (hu : ‖u‖ < 1) (hu0 : u ≠ 0) :
    ‖w‖ / (‖u‖ * ‖w - u‖) ≤ 2 / ‖u‖ := by
  have huN : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hwpos : 0 < ‖w‖ := by rw [hw]; linarith
  have hwu_sub : ‖w‖ / 2 ≤ ‖w - u‖ := by
    have h1 : ‖w‖ - ‖u‖ ≤ ‖w - u‖ := by
      have h := abs_norm_sub_norm_le w u
      exact le_trans (le_abs_self _) h
    have h2 : ‖w‖ / 2 ≤ ‖w‖ - ‖u‖ := by
      have h2u : 2 * ‖u‖ ≤ ‖w‖ := by
        rw [hw]
        nlinarith
      nlinarith
    exact le_trans h2 h1
  calc
    ‖w‖ / (‖u‖ * ‖w - u‖) ≤ ‖w‖ / (‖u‖ * (‖w‖ / 2)) := by
        apply div_le_div₀
        · exact le_of_lt hwpos
        · rfl
        · exact mul_pos huN (div_pos hwpos (by norm_num))
        · exact mul_le_mul_of_nonneg_left hwu_sub (le_of_lt huN)
    _ = 2 / ‖u‖ := by
        field_simp [ne_of_gt huN, ne_of_gt hwpos]

/-- **The tiny-region partial sum is bounded by a constant** depending only on `χ`.
For every `R ≥ 2`, `w` with `‖w‖ = R` and `T ≥ R + 1`,

`∑ᶠ u, D_T(u) · (if ‖u‖ < 1 ∧ 1 < ‖w - u‖ then ‖w‖ / (‖u‖ * ‖w - u‖) else 0) ≤ K`. -/
theorem partialSum_tiny {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 2 ≤ R → ∀ w : ℂ, ‖w‖ = R → ∀ T : ℝ, R + 1 ≤ T →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall 0 T)) u : ℤ) : ℝ) *
          (if ‖u‖ < 1 ∧ 1 < ‖w - u‖ then ‖w‖ / (‖u‖ * ‖w - u‖) else 0)) ≤ K := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  have hΛdiff : Differentiable ℂ Λ := by simpa [Λ] using differentiable_completedLFunction hχ
  have hΛan : ∀ U : Set ℂ, AnalyticOnNhd ℂ Λ U := by
    intro U z hz
    exact hΛdiff.analyticAt z
  have hΛmer : ∀ U : Set ℂ, MeromorphicOn Λ U := fun U => (hΛan U).meromorphicOn
  have hdiv_nonneg (U : Set ℂ) : ∀ u : ℂ,
      (0 : ℝ) ≤ (((MeromorphicOn.divisor Λ U) u : ℤ) : ℝ) := by
    intro u
    exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hΛan U) u)
  let K : ℝ := ∑ᶠ u : ℂ,
      (((MeromorphicOn.divisor Λ (closedBall (0 : ℂ) 1)) u : ℤ) : ℝ) *
        (if ‖u‖ < 1 then 2 / ‖u‖ else 0)
  refine ⟨K, ?_, ?_⟩
  · -- 0 ≤ K : every summand is non-negative
    dsimp [K]
    refine finsum_nonneg ?_
    intro u
    by_cases hu1 : ‖u‖ < 1
    · have hw0 : (0 : ℝ) ≤ (if ‖u‖ < 1 then 2 / ‖u‖ else 0) := by
        rw [if_pos hu1]
        exact div_nonneg (by norm_num) (norm_nonneg u)
      exact mul_nonneg (hdiv_nonneg (closedBall (0 : ℂ) 1) u) hw0
    · simp [hu1]
  · -- main bound
    intro R hR w hw T hT
    let g : ℂ → ℝ := fun u =>
      (((MeromorphicOn.divisor Λ (closedBall (0 : ℂ) T)) u : ℤ) : ℝ) *
        (if ‖u‖ < 1 ∧ 1 < ‖w - u‖ then ‖w‖ / (‖u‖ * ‖w - u‖) else 0)
    let h : ℂ → ℝ := fun u =>
      (((MeromorphicOn.divisor Λ (closedBall (0 : ℂ) 1)) u : ℤ) : ℝ) *
        (if ‖u‖ < 1 then 2 / ‖u‖ else 0)
    -- whenever `‖u‖ < 1`, the point `w` (with `‖w‖ = R ≥ 2`) is at distance > 1 from `u`
    have hWU : ∀ u : ℂ, ‖u‖ < 1 → 1 < ‖w - u‖ := by
      intro u hu1
      have h1 : ‖w‖ - ‖u‖ ≤ ‖w - u‖ := by
        have h := abs_norm_sub_norm_le w u
        exact le_trans (le_abs_self _) h
      have h2 : 1 < ‖w‖ - ‖u‖ := by
        rw [hw]
        nlinarith
      exact lt_of_lt_of_le h2 h1
    -- pointwise: `g ≤ h`
    have hg_le_h : g ≤ h := by
      intro u
      dsimp [g, h]
      by_cases hu0 : u = 0
      · -- at `u = 0` both weights vanish by total division (`1/0 = 0`)
        subst u
        simp
      · by_cases hu1 : ‖u‖ < 1
        · -- `‖u‖ < 1`: divisors agree, coefficients are nonnegative, weight bounded by `2/‖u‖`
          have hEqD : (MeromorphicOn.divisor Λ (closedBall (0 : ℂ) T)) u =
                (MeromorphicOn.divisor Λ (closedBall (0 : ℂ) 1)) u := by
            have hle1 : ‖u‖ ≤ (1 : ℝ) := le_of_lt hu1
            have hleT : ‖u‖ ≤ T := by linarith
            exact (divisor_closedBall_eq_of_le hΛmer (u := u) (ρ₁ := (1 : ℝ)) (ρ₂ := T) hle1 hleT).symm
          have hineq : (if ‖u‖ < 1 ∧ 1 < ‖w - u‖ then ‖w‖ / (‖u‖ * ‖w - u‖) else 0) ≤
              (if ‖u‖ < 1 then 2 / ‖u‖ else 0) := by
            rw [if_pos ⟨hu1, hWU u hu1⟩, if_pos hu1]
            exact tiny_weight_le (R := R) hR (w := w) hw (u := u) hu1 hu0
          rw [hEqD]
          exact mul_le_mul_of_nonneg_left hineq (hdiv_nonneg (closedBall (0 : ℂ) 1) u)
        · -- `‖u‖ ≥ 1`: both weights vanish
          simp [hu1]
    -- finite support of the divisors on compact balls
    have hfinD (ρ : ℝ) : Function.HasFiniteSupport
        (fun u : ℂ => (MeromorphicOn.divisor Λ (closedBall (0 : ℂ) ρ)) u) := by
      simpa [Function.HasFiniteSupport] using
        ((MeromorphicOn.divisor Λ (closedBall (0 : ℂ) ρ)).finiteSupport
          (isCompact_closedBall (0 : ℂ) ρ))
    have hfin_g : Function.HasFiniteSupport g := by
      have hsub : Function.support g ⊆ Function.support
          (fun u : ℂ => (MeromorphicOn.divisor Λ (closedBall (0 : ℂ) T)) u) := by
        intro u hu
        rw [Function.mem_support] at hu ⊢
        intro hD0
        apply hu
        simp [g, hD0]
      exact (hfinD T).subset hsub
    have hfin_h : Function.HasFiniteSupport h := by
      have hsub : Function.support h ⊆ Function.support
          (fun u : ℂ => (MeromorphicOn.divisor Λ (closedBall (0 : ℂ) 1)) u) := by
        intro u hu
        rw [Function.mem_support] at hu ⊢
        intro hD0
        apply hu
        simp [h, hD0]
      exact (hfinD (1 : ℝ)).subset hsub
    -- sum the pointwise inequality
    have hsum_le : (∑ᶠ u : ℂ, g u) ≤ (∑ᶠ u : ℂ, h u) :=
      finsum_le_finsum' hfin_g hfin_h hg_le_h
    have hK : (∑ᶠ u : ℂ, h u) = K := by
      dsimp [K, h]
    change (∑ᶠ u : ℂ, g u) ≤ (∑ᶠ u : ℂ, h u)
    exact hsum_le

end Commons.NumberTheory.Linnik
