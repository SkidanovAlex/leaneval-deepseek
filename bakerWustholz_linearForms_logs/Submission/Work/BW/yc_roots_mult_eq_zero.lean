import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial

/-- A polynomial `Q` over `ℂ` whose Hasse derivatives of all orders `< m` vanish at `a` has a zero
of order at least `m` at `a`, i.e. `(X - C a)^m ∣ Q`.

This is the Hasse-derivative form of the Taylor expansion: composing with `X + C a` (the `taylor`
shift) turns the condition on the Hasse derivatives into the vanishing of the lowest `m`
coefficients, which is exactly divisibility by `X^m`, transported back along the algebra
equivalence `X ↦ X + C a`. -/
theorem yc_hasseDeriv_roots_dvd (Q : ℂ[X]) (a : ℂ) (m : ℕ)
    (h : ∀ j, j < m → (hasseDeriv j Q).eval a = 0) :
    (X - C a) ^ m ∣ Q := by
  rw [X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
  intro d hd
  rw [← taylor_apply, taylor_coeff]
  exact h d hd

/-- A product of divisors that are pairwise coprime divides the target: specialised to the
`X - C (s i)` powers appearing in the root-counting argument. -/
theorem yc_prod_X_sub_C_pow_dvd (Q : ℂ[X]) (m : ℕ) {M : ℕ} (s : Fin M → ℂ)
    (hinj : Function.Injective s)
    (h : ∀ i, (X - C (s i)) ^ m ∣ Q) :
    (∏ i : Fin M, (X - C (s i)) ^ m) ∣ Q := by
  refine Fintype.prod_dvd_of_coprime ?_ h
  intro i j hij
  exact ((pairwise_coprime_X_sub_C hinj) hij).pow

/-- The degree of `∏ i, (X - C (s i))^m` is `m * M`: each factor is monic of degree `m`, and the
degree of a product of monics is the sum of the degrees. -/
theorem yc_natDegree_prod_X_sub_C_pow (m M : ℕ) (s : Fin M → ℂ) :
    (∏ i : Fin M, (X - C (s i)) ^ m).natDegree = m * M := by
  rw [natDegree_prod_of_monic (s := Finset.univ)]
  · simp [Nat.mul_comm]
  · intro i _
    exact (monic_X_sub_C (s i)).pow m

/-- Multiplicity form of the obstruction used at the degenerate (Y-free) descent levels: a
polynomial `Q ∈ ℂ[X]` which has a zero of multiplicity `≥ m` at each of `M` distinct points, and
whose degree is `< m * M`, is identically zero. -/
theorem yc_roots_mult_eq_zero (Q : Polynomial ℂ) (m M : ℕ) (s : Fin M → ℂ)
    (hinj : Function.Injective s)
    (hroot : ∀ i : Fin M, ∀ j : ℕ, j < m → Polynomial.eval (s i) (Polynomial.hasseDeriv j Q) = 0)
    (hdeg : Q.natDegree < m * M) : Q = 0 := by
  by_contra hQ
  -- Each point `s i` is a zero of multiplicity `≥ m`, hence `(X - C (s i))^m ∣ Q`.
  have hdvd : (∏ i : Fin M, (X - C (s i)) ^ m) ∣ Q :=
    yc_prod_X_sub_C_pow_dvd Q m s hinj (fun i => yc_hasseDeriv_roots_dvd Q (s i) m (hroot i))
  -- The product of the `M` pairwise-coprime factors is monic of degree exactly `m * M`.
  have hmonic : (∏ i : Fin M, (X - C (s i)) ^ m).Monic :=
    monic_prod_of_monic _ _ (fun i _ => (monic_X_sub_C (s i)).pow m)
  have hle := hmonic.natDegree_le_of_dvd hQ hdvd
  rw [yc_natDegree_prod_X_sub_C_pow m M s] at hle
  omega

end Work.BW
