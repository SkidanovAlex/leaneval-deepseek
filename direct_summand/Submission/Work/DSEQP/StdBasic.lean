/-
DSEQP: elementary computations with the `R`-linear "standard form" map `std` of `BoxDefs.lean`.

* `mk_monomial`: the quotient image of the monomial `X^s` is the product `∏ i, Z i ^ s i`.
* `std_monomial`: `std` on a monomial, in explicit form.
* `std_boxIdx`: `std (X^u) = e_u` for a box index `u : Fin d → Fin p`.
* `boxMono_eq_mk`: the box monomial `Z^u = ∏ i, Z i ^ u i` is the image of `X^u`.
-/
import Mathlib
import Submission.Work.DSEQP.BoxDefs

universe u

namespace Work.DSEQP

open MvPolynomial

variable {R : Type u} [CommRing R]

/-- The image of the monomial `X^s` in `R[X]/(Z_i^p - z_i)` is the product of the `Z i`. -/
theorem mk_monomial (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (z : Fin d → R)
    (s : Fin d →₀ ℕ) :
    (Ideal.Quotient.mk (Work.DSSER.serRel R p z) (MvPolynomial.monomial s 1) :
        Work.DSSER.serRing R p z) = ∏ i, Work.DSSER.serZ p z i ^ (s i) := by
  nth_rewrite 1 [← MvPolynomial.prod_X_pow_eq_monomial (s := s)]
  rw [map_prod]
  rw [← Finset.prod_subset (Finset.subset_univ s.support)
      (fun i _ hi => by simp only [Finsupp.mem_support_iff, not_not] at hi; rw [hi, pow_zero])]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow]

/-- `std` on a monomial has the explicit form `u ↦ c * ∏ i, z i ^ (s i / p)` on the residue
class of `s` modulo `p`, and is zero elsewhere. -/
theorem std_monomial (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (z : Fin d → R)
    (s : Fin d →₀ ℕ) (c : R) :
    std R p z (MvPolynomial.monomial s c) =
      c • (fun u : Fin d → Fin p => if ∀ i, s i % p = (u i : ℕ)
        then Work.DSSER.zMono z (fun i => s i / p) else 0) := by
  have h1 : (MvPolynomial.monomial s c : MvPolynomial (Fin d) R) =
      c • MvPolynomial.monomial s 1 := by
    rw [← MvPolynomial.C_mul', MvPolynomial.C_mul_monomial, mul_one]
  rw [h1, map_smul]
  congr 1
  exact Module.Basis.constr_basis (MvPolynomial.basisMonomials (Fin d) R) R _ s

/-- `std` sends the box monomial `X^u` to the coordinate function `e_u`. -/
theorem std_boxIdx (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (z : Fin d → R)
    (u : Fin d → Fin p) :
    std R p z (MvPolynomial.monomial (boxIdx u) 1) = Pi.single u 1 := by
  rw [std_monomial, one_smul]
  funext u'
  have hdiv : (fun i => boxIdx u i / p) = fun _ => 0 := by
    funext i
    rw [boxIdx_apply, Nat.div_eq_of_lt (u i).isLt]
  rw [hdiv, Work.DSSER.zMono_zero, Pi.single_apply]
  have hc : (∀ i, boxIdx u i % p = (u' i : ℕ)) ↔ u' = u := by
    constructor
    · intro hh
      funext i
      refine Fin.ext ?_
      have h1 := hh i
      rw [boxIdx_apply, Nat.mod_eq_of_lt (u i).isLt] at h1
      exact h1.symm
    · intro h i
      rw [h, boxIdx_apply, Nat.mod_eq_of_lt (u i).isLt]
  by_cases h : u' = u
  · rw [if_pos (hc.mpr h), if_pos h]
  · rw [if_neg (fun hh => h (hc.mp hh)), if_neg h]

/-- The box monomial `Z^u` is the image of the monomial `X^u`. -/
theorem boxMono_eq_mk (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (z : Fin d → R)
    (u : Fin d → Fin p) :
    boxMono R p z u = (Ideal.Quotient.mk (Work.DSSER.serRel R p z)
      (MvPolynomial.monomial (boxIdx u) 1) : Work.DSSER.serRing R p z) := by
  rw [mk_monomial]
  simp only [boxMono, boxIdx_apply]

end Work.DSEQP
