/-
Elementary properties of the Toeplitz matrices `toeplitz n p` and of the map
`U → ∏_n M_{n+1}(U)`, `a ↦ (n ↦ toeplitz (n+1) (a))`.
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.envelopeDefs
import Submission.Work.ORHughesFree.NaturalExtension.skewToeplitz

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORHughesFree.NaturalExtension

open Matrix

variable {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]

/-- The entries of a Toeplitz matrix. -/
theorem toeplitz_apply (N : ℕ) (p : SkewL U) (r s : Fin N) :
    toeplitz N p r s =
      (Multiplicative.ofAdd (((r : ℕ) : ℤ))) • (coeffElt p (((s : ℕ) : ℤ) - ((r : ℕ) : ℤ))) :=
  rfl

/-- Coefficients are additive in the element. -/
theorem coeffElt_add_skew (p q : SkewL U) (k : ℤ) :
    coeffElt (p + q) k = coeffElt p k + coeffElt q k := by
  simp [coeffElt, SkewMonoidAlgebra.coeff_add, Finsupp.add_apply]

/-- The coefficients of a monomial. -/
theorem coeffElt_single_monomial (m : Multiplicative ℤ) (a : U) (k : ℤ) :
    coeffElt (SkewMonoidAlgebra.single m a) k =
      (if Multiplicative.ofAdd k = m then a else 0) := by
  rw [coeffElt, SkewMonoidAlgebra.coeff_single_apply]
  by_cases h : Multiplicative.ofAdd k = m
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (fun hh => h hh.symm), if_neg h]

/-- A monomial `a t^j` with `j ≥ 0` has no coefficients in negative degrees. -/
theorem coeffElt_monomial_nonneg {j : ℕ} (a : U) {k : ℤ} (hk : k < 0) :
    coeffElt (SkewMonoidAlgebra.single (Multiplicative.ofAdd (j : ℤ)) a) k = 0 := by
  rw [coeffElt_single_monomial]
  have h : ¬ (Multiplicative.ofAdd k = Multiplicative.ofAdd (j : ℤ)) := by
    intro h
    have h2 : k = (j : ℤ) := congrArg Multiplicative.toAdd h
    omega
  simp [h]

/-- The coefficients of a constant. -/
theorem coeffElt_single_const (a : U) (k : ℤ) :
    coeffElt (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) a) k =
      (if k = 0 then a else 0) := by
  rw [coeffElt_single_monomial]
  by_cases h : k = 0
  · subst h; simp
  · have h' : ¬ (Multiplicative.ofAdd k = (1 : Multiplicative ℤ)) := by
      intro hc
      exact h (by simpa using congrArg Multiplicative.toAdd hc)
    simp [h, h']

theorem toeplitz_add' (N : ℕ) (p q : SkewL U) :
    toeplitz N (p + q) = toeplitz N p + toeplitz N q := by
  ext r s
  simp only [Matrix.add_apply, toeplitz_apply, coeffElt_add_skew, smul_add]

theorem toeplitz_zero' (N : ℕ) : toeplitz N (0 : SkewL U) = 0 := by
  ext r s
  rw [Matrix.zero_apply, toeplitz_apply]
  simp [coeffElt]

theorem toeplitz_one' (N : ℕ) : toeplitz N (1 : SkewL U) = 1 := by
  ext r s
  rw [Matrix.one_apply]
  rw [show (1 : SkewL U) = SkewMonoidAlgebra.single (1 : Multiplicative ℤ) (1 : U) from rfl]
  rw [toeplitz_apply, coeffElt_single_const]
  by_cases h : r = s
  · subst h; simp
  · have hk : ¬ (((s : ℕ) : ℤ) - ((r : ℕ) : ℤ) = 0) := by
      intro h0
      exact h (Fin.ext (by omega))
    simp [hk, h]

/-- The Toeplitz family is multiplicative on elements of nonnegative support. -/
theorem toeplitzFamily_mul_of_nonneg {p q : SkewL U}
    (hp : ∀ k : ℤ, k < 0 → coeffElt p k = 0) (hq : ∀ k : ℤ, k < 0 → coeffElt q k = 0) :
    toeplitzFamily p * toeplitzFamily q = toeplitzFamily (p * q) := by
  funext n
  exact (toeplitzMulNonneg (n+1) (p := p) (q := q) hp hq).symm

/-- The `n`-th power of `t` is a monomial. -/
theorem toeplitzSkewLaurentT_pow_eq_single (n : ℕ) :
    (skewLaurentT : SkewL U) ^ n =
      SkewMonoidAlgebra.single (Multiplicative.ofAdd (n : ℤ)) (1 : U) := by
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih =>
      rw [pow_succ, ih]
      have ht : (skewLaurentT : SkewL U) =
          SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) (1 : U) := rfl
      rw [ht, SkewMonoidAlgebra.single_mul_single]
      simp [Nat.cast_succ]

/-- Powers of `t` have nonnegative support. -/
theorem coeffElt_skewLaurentT_pow (n : ℕ) {k : ℤ} (hk : k < 0) :
    coeffElt ((skewLaurentT : SkewL U) ^ n) k = 0 := by
  rw [toeplitzSkewLaurentT_pow_eq_single]
  exact coeffElt_monomial_nonneg (j := n) 1 hk

/-- The Toeplitz family of a power of `t`. -/
theorem toeplitzFam_skewLaurentT_pow (n : ℕ) :
    (toeplitzFamily (skewLaurentT : SkewL U)) ^ n =
      toeplitzFamily ((skewLaurentT : SkewL U) ^ n) := by
  induction n with
  | zero =>
      funext k
      rw [pow_zero, pow_zero]
      exact (toeplitz_one' (k+1)).symm
  | succ n ih =>
      have h1 : ∀ k : ℤ, k < 0 → coeffElt ((skewLaurentT : SkewL U) ^ n) k = 0 :=
        fun k hk => coeffElt_skewLaurentT_pow n hk
      have h2 : ∀ k : ℤ, k < 0 → coeffElt (skewLaurentT : SkewL U) k = 0 :=
        fun k hk => coeffElt_monomial_nonneg (j := 1) (1 : U) hk
      rw [pow_succ, pow_succ, ih, toeplitzFamily_mul_of_nonneg h1 h2]

/-- The ring homomorphism `U → ∏_{n≥1} M_n(U)` sending `a` to the family of Toeplitz matrices
of the constant `a`. -/
noncomputable def toeplitzConstHom : U →+* W U where
  toFun a := fun n => toeplitz (n+1) (SkewMonoidAlgebra.single (1 : Multiplicative ℤ) a)
  map_one' := by
    funext n
    rw [Pi.one_apply]
    exact toeplitz_one' (n+1)
  map_mul' a b := by
    funext n
    rw [Pi.mul_apply]
    have hmul : SkewMonoidAlgebra.single (1 : Multiplicative ℤ) (a * b) =
        SkewMonoidAlgebra.single (1 : Multiplicative ℤ) a *
          SkewMonoidAlgebra.single (1 : Multiplicative ℤ) b := by
      rw [SkewMonoidAlgebra.single_mul_single]; simp
    rw [hmul]
    exact toeplitzMulNonneg (n+1) (fun k hk => coeffElt_monomial_nonneg (j := 0) a hk)
      (fun k hk => coeffElt_monomial_nonneg (j := 0) b hk)
  map_zero' := by
    funext n
    rw [Pi.zero_apply]
    have hz : SkewMonoidAlgebra.single (1 : Multiplicative ℤ) (0 : U) = 0 := by simp
    rw [hz, toeplitz_zero']
  map_add' a b := by
    funext n
    rw [Pi.add_apply]
    have hadd : SkewMonoidAlgebra.single (1 : Multiplicative ℤ) (a + b) =
        SkewMonoidAlgebra.single (1 : Multiplicative ℤ) a +
          SkewMonoidAlgebra.single (1 : Multiplicative ℤ) b :=
      SkewMonoidAlgebra.single_add _ _ _
    rw [hadd, toeplitz_add']

end Work.ORHughesFree.NaturalExtension
