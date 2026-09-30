import Mathlib
import Submission.Work.RB.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RB

open MvPolynomial

/-- If `X v` divides `p`, then it divides every weighted homogeneous component of `p`.
This is the coefficient-wise statement that the homogeneity decomposition of a multiple of
`X v` is again a multiple of `X v`. -/
lemma X_dvd_weightedHomogeneousComponent {n : ℕ} {σ : Type*} [Fintype σ]
    (w : σ → Fin n →₀ ℕ) {v : σ} {p : MvPolynomial σ ℂ}
    (h : MvPolynomial.X v ∣ p) (d : Fin n →₀ ℕ) :
    MvPolynomial.X v ∣ MvPolynomial.weightedHomogeneousComponent w d p := by
  rw [MvPolynomial.X_dvd_iff_modMonomial_eq_zero] at h ⊢
  ext m
  by_cases hm : Finsupp.single v 1 ≤ m
  · rw [MvPolynomial.coeff_modMonomial_of_le _ hm]; simp
  · rw [MvPolynomial.coeff_modMonomial_of_not_le _ hm,
      MvPolynomial.coeff_weightedHomogeneousComponent]
    have hp : p.coeff m = 0 := by
      rw [← MvPolynomial.coeff_modMonomial_of_not_le p hm, h]
      simp
    rw [hp]; simp

/-- A sum of two `w`-homogeneous ideals is `w`-homogeneous. -/
lemma isWHomog_sup {n : ℕ} {σ : Type*} [Fintype σ] (w : σ → Fin n →₀ ℕ)
    {I J : Ideal (MvPolynomial σ ℂ)} (hI : IsWHomog w I) (hJ : IsWHomog w J) :
    IsWHomog w (I ⊔ J) := by
  intro p hp d
  rw [Submodule.mem_sup] at hp
  obtain ⟨a, ha, b, hb, hab⟩ := hp
  rw [← hab, map_add]
  exact Submodule.add_mem_sup (hI a ha d) (hJ b hb d)

/-- The principal ideal `(X v)` is `w`-homogeneous, since its generator `X v` is
`w`-homogeneous of weight `w v`. -/
lemma isWHomog_span_X {n : ℕ} {σ : Type*} [Fintype σ] (w : σ → Fin n →₀ ℕ) (v : σ) :
    IsWHomog w (Ideal.span {MvPolynomial.X v}) := by
  intro p hp d
  rw [Ideal.mem_span_singleton] at hp ⊢
  exact X_dvd_weightedHomogeneousComponent w hp d

/-- `I + (X v)` of a `w`-homogeneous ideal `I` is again `w`-homogeneous. -/
theorem isWHomog_sup_span_X {n : ℕ} {σ : Type*} [Fintype σ] (w : σ → Fin n →₀ ℕ) {v : σ}
    {I : Ideal (MvPolynomial σ ℂ)} (hI : IsWHomog w I) :
    IsWHomog w (I ⊔ Ideal.span {MvPolynomial.X v}) :=
  isWHomog_sup w hI (isWHomog_span_X w v)

end Work.RB
