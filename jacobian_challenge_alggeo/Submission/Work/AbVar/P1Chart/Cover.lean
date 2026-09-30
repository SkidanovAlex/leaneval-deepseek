/-
Area AV: the two affine charts of `P¹` and the irrelevant ideal.
-/
import Mathlib
import Submission.Work.AbVar.P1Chart.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open HomogeneousLocalization MvPolynomial

noncomputable section

universe u

namespace Work.AbVar.P1Chart

/-- For `n ≥ 1`, the degree-`n` part of `k[X₀,X₁]` lies in the ideal `(X₀, X₁)`. -/
theorem gr_le_span_X (k : Type u) [Field k] {n : ℕ} (hn : 0 < n) :
    ∀ a : MvPolynomial (Fin 2) k, a ∈ gr k n →
      a ∈ Ideal.span (Set.range (fun i : Fin 2 => (MvPolynomial.X i : MvPolynomial (Fin 2) k))) := by
  intro a ha
  have ha' : ∀ d ∈ a.coeff.support, d.degree = n := by
    intro d hd
    have h2 : a ∈ AddMonoidAlgebra.supported k k {d : Fin 2 →₀ ℕ | d.degree = n} := by
      rw [← MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]; exact ha
    exact (AddMonoidAlgebra.mem_supported.mp h2) hd
  rw [MvPolynomial.as_sum a]
  refine Ideal.sum_mem _ fun d hd => ?_
  rcases eq_or_ne d 0 with rfl | hd0
  · exfalso
    have h0 : (0 : ℕ) = n := by simpa using (ha' 0 hd : Finsupp.degree (0 : Fin 2 →₀ ℕ) = n)
    omega
  · obtain ⟨i, hi⟩ : ∃ i : Fin 2, d i ≠ 0 := by
      by_contra h
      push Not at h
      exact hd0 (Finsupp.ext fun i => h i)
    have hsum : (d - Finsupp.single i (1 : ℕ)) + Finsupp.single i 1 = d := by
      ext j
      rcases eq_or_ne j i with hj | hj
      · subst hj
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
      · simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_of_ne hj, tsub_zero, add_zero]
    have hX : (MvPolynomial.X i : MvPolynomial (Fin 2) k)
        = MvPolynomial.monomial (Finsupp.single i 1) (1 : k) := by
      rw [← MvPolynomial.X_pow_eq_monomial, pow_one]
    have hmul : MvPolynomial.monomial (d - Finsupp.single i (1 : ℕ)) (a.coeff d) *
          (MvPolynomial.X i : MvPolynomial (Fin 2) k)
        = MvPolynomial.monomial d (a.coeff d) := by
      rw [hX, MvPolynomial.monomial_mul_monomial, hsum, mul_one]
    rw [← hmul]
    exact Ideal.mul_mem_left _ _
      (Ideal.subset_span (Set.mem_range.mpr ⟨i, rfl⟩))

/-- The irrelevant ideal of the standard grading on `k[X₀,X₁]` is spanned by `X₀` and `X₁`. -/
theorem irrelevant_le_span_X (k : Type u) [Field k] :
    (HomogeneousIdeal.irrelevant (gr k)).toIdeal ≤
      Ideal.span (Set.range (fun i : Fin 2 => (MvPolynomial.X i : MvPolynomial (Fin 2) k))) := by
  rw [HomogeneousIdeal.irrelevant_eq_span, Ideal.span_le]
  intro a ha
  simp only [Set.mem_iUnion] at ha
  obtain ⟨n, hn, hna⟩ := ha
  exact gr_le_span_X k hn a hna

end Work.AbVar.P1Chart
