import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SymQuot.DivOf

/-- **Coefficients of a product of polynomials, over a family of ideals.**

If for every `i ∈ s` every coefficient of `f i` lies in the ideal `J i`, then every
coefficient of `∏ i ∈ s, f i` lies in the product ideal `∏ i ∈ s, J i`.

This is the general version of `coeff_prod_mem_prod_ideal`: the coefficient `α` is
universally quantified inside the induction so that the recursion on `s` can use the
induction hypothesis at the second component of an element of the antidiagonal. -/
private theorem coeff_prod_mem_prod_ideal_aux {R : Type*} [CommRing R] {σ : Type*}
    [DecidableEq σ] {ι : Type*} (s : Finset ι) (J : ι → Ideal R) (f : ι → MvPolynomial σ R)
    (hf : ∀ i β, (f i).coeff β ∈ J i) (α : σ →₀ ℕ) :
    (∏ i ∈ s, f i).coeff α ∈ ∏ i ∈ s, J i := by
  classical
  have key : ∀ (s : Finset ι), ∀ α : σ →₀ ℕ,
      (∏ i ∈ s, f i).coeff α ∈ ∏ i ∈ s, J i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro α
        rw [Finset.prod_empty, Finset.prod_empty, Ideal.one_eq_top]
        exact Submodule.mem_top
    | insert a t ha ih =>
        intro α
        rw [Finset.prod_insert ha, Finset.prod_insert ha, MvPolynomial.coeff_mul]
        apply Ideal.sum_mem
        rintro ⟨x1, x2⟩ hx
        exact Ideal.mul_mem_mul (hf a x1) (ih x2)
  exact key s α

theorem coeff_prod_mem_prod_ideal {R : Type*} [CommRing R] {n r : ℕ} (I : Fin n → Ideal R)
    (c : Fin n → Fin r → R) (hc : ∀ m i, c m i ∈ I m) (α : Fin r →₀ ℕ) :
    (∏ m, ∑ i, MvPolynomial.C (c m i) * MvPolynomial.X i).coeff α ∈ ∏ m, I m := by
  classical
  refine coeff_prod_mem_prod_ideal_aux Finset.univ I
    (fun m => ∑ i, MvPolynomial.C (c m i) * MvPolynomial.X i) ?_ α
  intro m β
  rw [MvPolynomial.coeff_sum]
  apply Ideal.sum_mem
  intro i hi
  rw [MvPolynomial.coeff_C_mul]
  rw [← Ideal.mul_top (I m)]
  exact Ideal.mul_mem_mul (hc m i) trivial

end Work.SymQuot.DivOf
