import Mathlib
import Submission.Work.LinnikAreas.BGTZ.SieveLocalBound
import Submission.Work.LinnikAreas.BGTZ.GEstimateDefs

namespace Work.LinnikAreas.BGTZ

open scoped Classical BigOperators

/-- The lcm of two squarefree natural numbers is squarefree. -/
lemma squarefree_lcm_of_squarefree {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  rw [Nat.squarefree_iff_factorization_le_one (Nat.lcm_ne_zero ha.ne_zero hb.ne_zero)]
  intro p
  rw [Nat.factorization_lcm ha.ne_zero hb.ne_zero]
  exact max_le (ha.natFactorization_le_one p) (hb.natFactorization_le_one p)

/-- The modulus of the product of the local sieve factors over the primes of `n` is bounded by
the product of the local weights `gwt`; this is `SieveLocalBound` combined with the triangle
inequality for the product. -/
lemma sieveLocal_prod_norm_le {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : s.re = 1 / 2) (n : ℕ) :
    ‖∏ p ∈ n.primeFactors, sieveLocal χ₁ χ s p‖
      ≤ ∏ p ∈ n.primeFactors, gwt χ₁ p :=
  calc ‖∏ p ∈ n.primeFactors, sieveLocal χ₁ χ s p‖
      ≤ ∏ p ∈ n.primeFactors, ‖sieveLocal χ₁ χ s p‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ p ∈ n.primeFactors, gwt χ₁ p :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun p _ => SieveLocalBound χ₁ χ hs p)

/-- The full sieve term is dominated by the product of the local weights: this multiplies the
bound on the local factor by the trivial bound `|θw d|, |θw e| ≤ 1`. -/
lemma sieveTerm_le_prod_gwt {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) {R : ℕ}
    {θw : ℕ → ℝ} (hθ : IsSieveWeight R θw) {s : ℂ} (hs : s.re = 1 / 2) (d e : ℕ) :
    ‖(θw d : ℂ) * (θw e : ℂ) * ∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ s p‖
      ≤ ∏ p ∈ (Nat.lcm d e).primeFactors, gwt χ₁ p := by
  have hP := sieveLocal_prod_norm_le χ₁ χ hs (Nat.lcm d e)
  have hd : |θw d| ≤ 1 := hθ.2.2 d
  have he : |θw e| ≤ 1 := hθ.2.2 e
  have hmul : |θw d| * |θw e| ≤ 1 := by nlinarith [abs_nonneg (θw d), abs_nonneg (θw e)]
  have hnorm : ‖(θw d : ℂ) * (θw e : ℂ)
        * ∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ s p‖
      = |θw d| * |θw e|
        * ‖∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ s p‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
  rw [hnorm]
  calc |θw d| * |θw e| * ‖∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ s p‖
      ≤ 1 * ‖∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ s p‖ :=
        mul_le_mul_of_nonneg_right hmul (norm_nonneg _)
    _ = ‖∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ s p‖ := one_mul _
    _ ≤ ∏ p ∈ (Nat.lcm d e).primeFactors, gwt χ₁ p := hP

theorem SieveGsumTermLe {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) {R : ℕ} {θw : ℕ → ℝ} (hθ : Work.LinnikAreas.BGTZ.IsSieveWeight R θw) {s : ℂ} (hs : s.re = 1 / 2) (d e : ℕ) : ‖(θw d : ℂ) * (θw e : ℂ) * ∏ p ∈ (Nat.lcm d e).primeFactors, Work.LinnikAreas.BGTZ.sieveLocal χ₁ χ s p‖ ≤ Work.LinnikAreas.BGTZ.gw χ₁ (Nat.lcm d e) := by
  rcases Classical.em (Squarefree (Nat.lcm d e)) with hsq | hnsq
  · rw [gw_of_squarefree χ₁ hsq]
    exact sieveTerm_le_prod_gwt χ₁ χ hθ hs d e
  · rw [gw_of_not_squarefree χ₁ hnsq]
    have hcase : ¬ Squarefree d ∨ ¬ Squarefree e := by
      by_contra h
      push Not at h
      exact hnsq (squarefree_lcm_of_squarefree h.1 h.2)
    rcases hcase with h | h
    · have hz : θw d = 0 := hθ.2.1 d (Or.inl h)
      rw [hz]
      simp
    · have hz : θw e = 0 := hθ.2.1 e (Or.inl h)
      rw [hz]
      simp

end Work.LinnikAreas.BGTZ
