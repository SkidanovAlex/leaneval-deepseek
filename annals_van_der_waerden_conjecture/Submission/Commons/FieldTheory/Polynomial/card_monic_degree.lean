import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

set_option autoImplicit false

open Polynomial

/-!
# The number of monic polynomials of degree `n` over a finite field

The number of monic polynomials of degree `n` with coefficients in a finite
field `F` is `q^n`, `q = Fintype.card F`.  A monic degree-`n` polynomial is
uniquely determined by its `n` trailing coefficients
`coeff 0, …, coeff (n-1)`: this gives the bijection
`monicDegreeEquiv` between monic degree-`n` polynomials and `Fin n → F`
(the inverse sends `v` to `X^n + Polynomial.ofFn n v`), and then we count.

The statement is phrased with `Set.ncard` (which needs no `Fintype` instance
on the polynomial subtype); since `Set.ncard` is definitionally
`Nat.card` of the subtype, we count through the equivalence.
-/

namespace Commons.FieldTheory.Polynomial

noncomputable section

/-- The first `n` coefficients of `X ^ n` vanish, i.e. `Polynomial.toFn n (X ^ n) = 0`. -/
lemma toFn_X_pow_eq_zero {F : Type*} [Semiring F] (n : ℕ) :
    Polynomial.toFn n (X ^ n : F[X]) = 0 := by
  ext i
  simp only [Polynomial.toFn, Polynomial.lcoeff_apply, LinearMap.pi_apply, Polynomial.coeff_X_pow]
  have hi : (i : ℕ) ≠ n := ne_of_lt i.isLt
  simp [hi]

/-- A monic polynomial of degree `n` agrees with `X ^ n` only at the leading term: it is
`X ^ n` plus its `Polynomial.ofFn`-reconstruction from the first `n` coefficients. -/
lemma ofFn_toFn_eq_sub_X_pow {F : Type*} [Ring F] [DecidableEq F] {p : F[X]} {n : ℕ}
    (hp : p.Monic) (hdeg : p.natDegree = n) :
    Polynomial.ofFn n (Polynomial.toFn n p) = p - X ^ n := by
  ext i
  by_cases hi : i < n
  · rw [ofFn_coeff_eq_val_of_lt (Polynomial.toFn n p) hi]
    simp [Polynomial.toFn, Polynomial.lcoeff_apply, LinearMap.pi_apply, Polynomial.coeff_X_pow,
      ne_of_lt hi]
  · by_cases he : i = n
    · rw [he]
      have hc : p.coeff n = 1 := by
        simpa [hdeg] using (hp.coeff_natDegree)
      rw [ofFn_coeff_eq_zero_of_ge (Polynomial.toFn n p) le_rfl]
      simp [hc]
    · have hn : n ≤ i := Nat.le_of_not_gt hi
      have hlt : p.natDegree < i := by
        rw [hdeg]
        exact Nat.lt_of_le_of_ne hn (Ne.symm he)
      have hpi : p.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt
      rw [ofFn_coeff_eq_zero_of_ge (Polynomial.toFn n p) hn]
      simp [Polynomial.coeff_X_pow, he, hpi]

/-- `X ^ n + Polynomial.ofFn n v` is monic of degree `n`, for any trailing coefficient
vector `v : Fin n → F`. -/
lemma isMonicOfDegree_X_pow_add_ofFn {F : Type*} [Field F] [DecidableEq F] (n : ℕ)
    (v : Fin n → F) : IsMonicOfDegree (X ^ n + ofFn n v : F[X]) n := by
  by_cases hn : n = 0
  · subst n
    rw [show X ^ 0 + ofFn 0 v = (1 : F[X]) by simp]
    simp
  · have hq : (ofFn n v : F[X]).natDegree < n :=
      ofFn_natDegree_lt (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)) v
    exact (isMonicOfDegree_X_pow F n).add_right hq

/-- The monic polynomials of degree `n` over `F` are in bijection with the vector of their
first `n` coefficients.  The inverse of the trailing-coefficient map sends
`v : Fin n → F` to `X ^ n + Polynomial.ofFn n v`. -/
noncomputable def monicDegreeEquiv (F : Type*) [Field F] [DecidableEq F] (n : ℕ) :
    {p : F[X] // p.Monic ∧ p.natDegree = n} ≃ (Fin n → F) where
  toFun p := Polynomial.toFn n p.1
  invFun v :=
    ⟨X ^ n + ofFn n v,
      by
        have h : IsMonicOfDegree (X ^ n + ofFn n v : F[X]) n :=
          isMonicOfDegree_X_pow_add_ofFn n v
        exact ⟨h.monic, h.natDegree_eq⟩⟩
  left_inv := by
    intro p
    apply Subtype.ext
    have h := ofFn_toFn_eq_sub_X_pow (F := F) (p := p.1) (n := n) p.2.1 p.2.2
    calc
      X ^ n + ofFn n (toFn n p.1) = X ^ n + (p.1 - X ^ n) := by rw [h]
      _ = p.1 := by ring
  right_inv := by
    intro v
    calc
      toFn n (X ^ n + ofFn n v) = toFn n (X ^ n) + toFn n (ofFn n v) := by rw [map_add]
      _ = v := by rw [toFn_X_pow_eq_zero, zero_add, toFn_comp_ofFn_eq_id]

/-- The number of monic polynomials of degree `n` with coefficients in a finite field `F`
is `(Fintype.card F)^n`. -/
theorem card_monic_degree {F : Type*} [Field F] [Fintype F] (n : ℕ) :
    ({p : F[X] | p.Monic ∧ p.natDegree = n} : Set (F[X])).ncard =
      Fintype.card F ^ n := by
  classical
  let e : {p : F[X] // p.Monic ∧ p.natDegree = n} ≃ (Fin n → F) := monicDegreeEquiv F n
  change Nat.card {p : F[X] // p.Monic ∧ p.natDegree = n} = Fintype.card F ^ n
  calc
    Nat.card {p : F[X] // p.Monic ∧ p.natDegree = n} = Nat.card (Fin n → F) := Nat.card_congr e
    _ = Fintype.card (Fin n → F) := by simp [Nat.card_eq_fintype_card]
    _ = Fintype.card F ^ n := by simp

end

end Commons.FieldTheory.Polynomial