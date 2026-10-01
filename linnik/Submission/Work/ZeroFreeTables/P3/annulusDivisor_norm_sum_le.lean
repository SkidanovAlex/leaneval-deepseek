import Mathlib
import Submission.Work.ZeroFreeTables.P3.AnnulusDiffDefs

open scoped Classical BigOperators

namespace Work.ZeroFreeTables.P3

/-- The annulus divisor of the completed L-function is nonnegative whenever `R ≤ R'`
(its real cast is the annulus mass, which is nonnegative). -/
lemma annulusDivisor_nonneg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {R R' : ℝ} (hR : R ≤ R') (u : ℂ) :
    0 ≤ annulusDivisor χ R R' u := by
  have h : ((annulusDivisor χ R R' u : ℤ) : ℝ) = annulusMass χ R R' u :=
    annulusDivisor_cast_eq χ hχ hR u
  have hm := annulusMass_nonneg χ hχ R R' u
  rw [← h] at hm
  exact Int.cast_nonneg_iff.mp hm

/-- The norm of the annulus part of the partial-fraction expansion is bounded by the
corresponding weighted sum of the annulus masses: the divisor coefficients are nonnegative,
so taking norms termwise (triangle inequality for the finite sum over the support) and using
`annulusDivisor_cast_eq` turns the left-hand side into the right-hand side. -/
theorem annulusDivisor_norm_sum_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (n : ℕ) (s : ℂ) {R R' : ℝ} (hR : R ≤ R') :
    ‖∑ᶠ u : ℂ, ((annulusDivisor χ R R' u : ℤ) : ℂ) * (1 / (s - u)) ^ n‖
      ≤ ∑ᶠ u : ℂ, annulusMass χ R R' u * (1 / ‖s - u‖) ^ n := by
  classical
  have hfin : (Function.support (annulusMass χ R R')).Finite :=
    annulusMass_finiteSupport χ hχ R R'
  have hmemS : ∀ u : ℂ, u ∈ (hfin.toFinset : Set ℂ) ↔ annulusMass χ R R' u ≠ 0 := by
    intro u
    rw [hfin.coe_toFinset]
    exact Function.mem_support
  have hfS : Function.support
        (fun u : ℂ => ((annulusDivisor χ R R' u : ℤ) : ℂ) * (1 / (s - u)) ^ n)
      ⊆ (hfin.toFinset : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    rw [hmemS]
    intro hm0
    apply hu
    have hc := annulusDivisor_cast_eq χ hχ hR u
    have hd0 : annulusDivisor χ R R' u = 0 := by
      have : ((annulusDivisor χ R R' u : ℤ) : ℝ) = 0 := by rw [hc, hm0]
      exact_mod_cast this
    rw [hd0]; simp
  have hgS : Function.support (fun u : ℂ => annulusMass χ R R' u * (1 / ‖s - u‖) ^ n)
      ⊆ (hfin.toFinset : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    rw [hmemS]
    intro hm0
    exact hu (by rw [hm0, zero_mul])
  have hdnn : ∀ u : ℂ, (0 : ℝ) ≤ ((annulusDivisor χ R R' u : ℤ) : ℝ) := by
    intro u
    rw [annulusDivisor_cast_eq χ hχ hR u]
    exact annulusMass_nonneg χ hχ R R' u
  have hpoint : ∀ u : ℂ, ‖((annulusDivisor χ R R' u : ℤ) : ℂ) * (1 / (s - u)) ^ n‖
      = annulusMass χ R R' u * (1 / ‖s - u‖) ^ n := by
    intro u
    rw [norm_mul, norm_pow, norm_div, norm_one, Complex.norm_intCast,
        abs_of_nonneg (hdnn u), annulusDivisor_cast_eq χ hχ hR u]
  have e1 : (∑ᶠ u : ℂ, ((annulusDivisor χ R R' u : ℤ) : ℂ) * (1 / (s - u)) ^ n)
      = ∑ u ∈ hfin.toFinset, ((annulusDivisor χ R R' u : ℤ) : ℂ) * (1 / (s - u)) ^ n :=
    finsum_eq_finsetSum_of_support_subset _ hfS
  have e2 : (∑ᶠ u : ℂ, annulusMass χ R R' u * (1 / ‖s - u‖) ^ n)
      = ∑ u ∈ hfin.toFinset, annulusMass χ R R' u * (1 / ‖s - u‖) ^ n :=
    finsum_eq_finsetSum_of_support_subset _ hgS
  rw [e1, e2]
  calc ‖∑ u ∈ hfin.toFinset, ((annulusDivisor χ R R' u : ℤ) : ℂ) * (1 / (s - u)) ^ n‖
      ≤ ∑ u ∈ hfin.toFinset,
          ‖((annulusDivisor χ R R' u : ℤ) : ℂ) * (1 / (s - u)) ^ n‖ :=
        norm_sum_le _ _
    _ = ∑ u ∈ hfin.toFinset, annulusMass χ R R' u * (1 / ‖s - u‖) ^ n :=
        Finset.sum_congr rfl (fun u _ => hpoint u)

end Work.ZeroFreeTables.P3
