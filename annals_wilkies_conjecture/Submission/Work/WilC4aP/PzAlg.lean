/-
  annals_wilkies_conjecture, hole `C4a_puiseux` (`PuiseuxReal`): shared algebraic helpers
  for the complex Puiseux development.

  These are elementary facts about `Pz` (the fibre of a polynomial with function
  coefficients) and about composition of polynomials with a linear polynomial, together
  with two auxiliary lemmas (an analyticity helper and a `Fin`-indexed product splitting).
  They are used both by the main assembly (`Work.WilC4aP.complex_puiseux`) and by the
  auxiliary lemmas about `FactoredOn`.
-/
import Mathlib
import Submission.Work.WilC4aP.Basic

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators Topology

namespace Work.WilC4aP

open Polynomial

/-! ## `Pz` and composition -/

/-- `Pz` commutes with composition of polynomials over the function ring. -/
lemma Pz_comp (P Q : Polynomial (ℂ → ℂ)) (z : ℂ) :
    Pz (P.comp Q) z = (Pz P z).comp (Pz Q z) := by
  rw [Pz, Polynomial.map_comp]
  rfl

/-- Fibres of a shift `Y ↦ Y + d(z)`. -/
lemma Pz_comp_X_add_C (P : Polynomial (ℂ → ℂ)) (d : ℂ → ℂ) (z : ℂ) :
    Pz (P.comp (X + C d)) z = (Pz P z).comp (X + C (d z)) := by
  rw [Pz_comp, Pz, Pz, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  rfl

/-- The fibre of the variable is the variable. -/
@[simp] lemma Pz_X (z : ℂ) : Pz (X : Polynomial (ℂ → ℂ)) z = X := by
  rw [Pz, Polynomial.map_X]

/-! ## Substitutions by a non-constant linear polynomial -/

/-- The two shifts by `a` and `b` compose to the shift by `a + b`. -/
lemma comp_X_add_C_comp {R : Type*} [CommSemiring R] (a b : R) :
    (X + C a).comp (X + C b) = X + C (a + b) := by
  rw [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp, add_assoc, ← Polynomial.C_add,
    add_comm b a]

/-- Substitution of `X + C c` is injective (the inverse substitution is `X + C (-c)`). -/
lemma comp_X_add_C_injective (c : ℂ) :
    Function.Injective fun p : ℂ[X] => p.comp (X + C c) := by
  intro p q h
  have h' := congrArg (fun r : ℂ[X] => r.comp (X + C (-c))) h
  have hX : (X + C c).comp (X + C (-c)) = X := by
    rw [comp_X_add_C_comp, add_neg_cancel, Polynomial.C_0, add_zero]
  simpa [Polynomial.comp_assoc, hX] using h'

/-- Substitution of `C c * X` with `c ≠ 0` is injective. -/
lemma comp_C_mul_X_injective {c : ℂ} (hc : c ≠ 0) :
    Function.Injective fun p : ℂ[X] => p.comp (C c * X) := by
  intro p q h
  have h' := congrArg (fun r : ℂ[X] => r.comp (C c⁻¹ * X)) h
  have hX : (C c * X).comp (C c⁻¹ * X) = X := by
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, ← mul_assoc,
      ← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1, one_mul]
  simpa [Polynomial.comp_assoc, hX] using h'

/-- Coefficient of the substitution `X ↦ c * X`. -/
lemma coeff_comp_C_mul_X (p : ℂ[X]) (c : ℂ) (i : ℕ) :
    (p.comp (C c * X)).coeff i = p.coeff i * c ^ i := by
  have hkey : ∀ e : ℕ, (C (p.coeff e * c ^ e) * X ^ e : ℂ[X]).coeff i =
      if i = e then p.coeff e * c ^ e else 0 := by
    intro e
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases h : i = e
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
  have hexp : p.comp (C c * X) = ∑ e ∈ p.support, C (p.coeff e * c ^ e) * X ^ e := by
    conv_lhs => rw [← Polynomial.sum_C_mul_X_pow_eq p, Polynomial.sum_def]
    rw [Polynomial.sum_comp]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp, mul_pow, ← Polynomial.C_pow,
      ← mul_assoc, ← Polynomial.C_mul]
  rw [hexp, Polynomial.finsetSum_coeff]
  simp only [hkey]
  rw [Finset.sum_ite_eq p.support i (fun e => p.coeff e * c ^ e)]
  by_cases hi : i ∈ p.support
  · rw [if_pos hi]
  · rw [if_neg hi]
    have h0 : p.coeff i = 0 := by
      by_contra h
      exact hi (Polynomial.mem_support_iff.mpr h)
    rw [h0, zero_mul]

/-! ## Analyticity helpers -/

private lemma pow_le_self_of_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {N : ℕ} (hN : 0 < N) :
    x ^ N ≤ x := by
  rw [show N = (N - 1) + 1 by omega, pow_succ]
  have h1 : x ^ (N - 1) ≤ 1 := pow_le_one₀ (n := N - 1) hx0 hx1
  nlinarith

/-- If `f` is analytic on a disk of radius `R` and `N > 0`, then `u ↦ f (u ^ N)` is analytic on
any disk of radius `ρ ≤ min 1 R`. -/
lemma AnalyticOnNhd.comp_pow {f : ℂ → ℂ} {R ρ : ℝ} (hf : AnalyticOnNhd ℂ f (Metric.ball 0 R))
    (hρ1 : ρ ≤ 1) (hρR : ρ ≤ R) {N : ℕ} (hN : 0 < N) :
    AnalyticOnNhd ℂ (fun u => f (u ^ N)) (Metric.ball 0 ρ) := by
  intro u hu
  have huρ : ‖u‖ < ρ := by simpa [dist_eq_norm] using Metric.mem_ball.mp hu
  have hu1 : ‖u‖ ≤ 1 := le_trans huρ.le hρ1
  have hnorm : ‖u ^ N‖ ≤ ‖u‖ := by
    rw [norm_pow]
    exact pow_le_self_of_le_one (norm_nonneg u) hu1 hN
  have hmem : u ^ N ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt hnorm (lt_of_lt_of_le huρ hρR)
  exact AnalyticAt.comp (f := fun v : ℂ => v ^ N) (x := u) (hf _ hmem) (analyticAt_id.pow N)

/-! ## Splitting a `Fin`-indexed product -/

/-- The family of branches of a product `G * H`: the `k` branches of `G` evaluated after the
substitution `u ↦ u ^ N₂`, followed by the `n` branches of `H` evaluated after `u ↦ u ^ N₁`. -/
def combineFamily {k n : ℕ} (N₁ N₂ : ℕ) (η₁ : Fin k → ℂ → ℂ) (η₂ : Fin n → ℂ → ℂ) :
    Fin (k + n) → ℂ → ℂ :=
  fun j => Sum.elim (fun i : Fin k => fun u : ℂ => η₁ i (u ^ N₂))
    (fun i : Fin n => fun u : ℂ => η₂ i (u ^ N₁)) (finSumFinEquiv.symm j)

/-- Every member of `combineFamily` is analytic at `0` when the members of `η₁` and `η₂` are. -/
lemma combineFamily_analytic {k n N₁ N₂ : ℕ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    {η₁ : Fin k → ℂ → ℂ} {η₂ : Fin n → ℂ → ℂ} (h₁ : ∀ j, AnalyticAt ℂ (η₁ j) 0)
    (h₂ : ∀ j, AnalyticAt ℂ (η₂ j) 0) :
    ∀ j, AnalyticAt ℂ (combineFamily N₁ N₂ η₁ η₂ j) 0 := by
  intro j
  rcases e : finSumFinEquiv.symm j with i | i
  · rw [show combineFamily N₁ N₂ η₁ η₂ j = fun u : ℂ => η₁ i (u ^ N₂) by simp [combineFamily, e]]
    have h0 : (0 : ℂ) ^ N₂ = 0 := zero_pow hN₂.ne'
    exact AnalyticAt.comp (f := fun u : ℂ => u ^ N₂) (x := (0 : ℂ))
      (by rw [h0]; exact h₁ i) (analyticAt_id.pow N₂)
  · rw [show combineFamily N₁ N₂ η₁ η₂ j = fun u : ℂ => η₂ i (u ^ N₁) by simp [combineFamily, e]]
    have h0 : (0 : ℂ) ^ N₁ = 0 := zero_pow hN₁.ne'
    exact AnalyticAt.comp (f := fun u : ℂ => u ^ N₁) (x := (0 : ℂ))
      (by rw [h0]; exact h₂ i) (analyticAt_id.pow N₁)

/-- `u ↦ f (u ^ N)` is analytic at `0` when `f` is and `N > 0`. -/
lemma analyticAt_comp_pow {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) {N : ℕ} (hN : 0 < N) :
    AnalyticAt ℂ (fun u => f (u ^ N)) 0 := by
  have h0 : (0 : ℂ) ^ N = 0 := zero_pow hN.ne'
  exact AnalyticAt.comp (f := fun u : ℂ => u ^ N) (x := (0 : ℂ))
    (by rw [h0]; exact hf) (analyticAt_id.pow N)

/-- Splitting a product over `Fin (k + n)` into its first `k` and last `n` factors. -/
lemma prod_fin_add {M : Type*} [CommMonoid M] {k n : ℕ} (f : Fin (k + n) → M) :
    ∏ j, f j =
      (∏ j : Fin k, f (finSumFinEquiv (Sum.inl j))) *
        (∏ j : Fin n, f (finSumFinEquiv (Sum.inr j))) := by
  rw [← Fintype.prod_sum_type (M := M) (fun x : Fin k ⊕ Fin n => f (finSumFinEquiv x))]
  exact Fintype.prod_equiv finSumFinEquiv.symm (fun j : Fin (k + n) => f j)
    (fun x : Fin k ⊕ Fin n => f (finSumFinEquiv x)) (fun y => by simp)

/-- The product of `m` copies of `X - C a`. -/
lemma prod_fin_const (m : ℕ) (a : ℂ) :
    ∏ j : Fin m, (X - C a : ℂ[X]) = (X - C a) ^ m := by
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Work.WilC4aP
