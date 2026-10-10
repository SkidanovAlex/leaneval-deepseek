import Mathlib
import Submission.Work.MotAS.AsCoeff6Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Naturality of `asCoeff6` under a change of coefficient ring

`asCoeff6 R a b g j` is the `T^j`-coefficient of `R^AS_0(A + T·B)`, a polynomial in the
coordinates `X 0, …, X 4` of `c` with coefficients built out of `a, b, g`.

The target lemma `map_asCoeff6` says that this construction is natural in the coefficient ring:
mapping the coefficients along a ring homomorphism `φ : R →+* S` (i.e. `MvPolynomial.map φ`)
sends `asCoeff6 R a b g j` to `asCoeff6 S (φ a) (φ b) (φ g) j`.

The proof is a bookkeeping computation: every ingredient (`kleinQAS`, `kleinBilinAS`, `asTanQ`,
`asPolarP`, `kleinPAS_k`, `kleinRAS0`, `qAS_A`, `qAS_B`, `asCoeffPoly`) is a polynomial
expression with integer coefficients in the parameters and the coordinates, hence commutes with
every ring homomorphism.  We record this ingredientwise (`map6_*`) and then assemble.

The helper names are prefixed `map6_` to avoid clashing with the analogous lemmas that other
files of this directory prove for the other charts.
-/

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace Work.MotAS

open MvPolynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ## Pointwise addition of functions

`simp` normalises the pointwise sum of two functions `f + g` to `fun i => f i + g i`, but the
two forms are not syntactically equal, so we record the (definitional) identity as a rewrite
rule. -/

/-- Pointwise addition of functions, in `lambda` form (definitional). -/
lemma map6_add_fun_eq (f g : Fin 5 → S) : (f + g : Fin 5 → S) = fun i => f i + g i := rfl

/-! ## Naturality of the ingredients of the ruling data -/

/-- Naturality of the AS invariant quadric `kleinQAS`. -/
lemma map6_kleinQAS (φ : R →+* S) (a b : R) (y : Fin 5 → R) :
    φ (kleinQAS a b y) = kleinQAS (φ a) (φ b) (fun i => φ (y i)) := by
  simp only [kleinQAS, map_add, map_mul, map_pow, map_sub, map_neg, map_ofNat]

/-- Naturality of the polar form `kleinBilinAS` of `kleinQAS`. -/
lemma map6_kleinBilinAS (φ : R →+* S) (a b : R) (u v : Fin 5 → R) :
    φ (kleinBilinAS a b u v)
      = kleinBilinAS (φ a) (φ b) (fun i => φ (u i)) (fun i => φ (v i)) := by
  simp only [kleinBilinAS, map_sub, map6_kleinQAS, map6_add_fun_eq, map_add, map_mul]

/-- The standard basis vectors `kleinE k = Pi.single k 1` are fixed by every ring homomorphism. -/
lemma map6_kleinE (φ : R →+* S) (k i : Fin 5) :
    φ (Work.MotK.kleinE (R := R) k i) = Work.MotK.kleinE (R := S) k i := by
  simp only [Work.MotK.kleinE, Pi.single_apply]
  split <;> simp

/-- Naturality of the twisted Pfaffians `kleinPAS_k`. -/
lemma map6_kleinPAS0 (φ : R →+* S) (a b g : R) (y : Fin 5 → R) :
    φ (kleinPAS0 a b g y) = kleinPAS0 (φ a) (φ b) (φ g) (fun i => φ (y i)) := by
  simp only [kleinPAS0, map_add, map_mul, map_pow, map_sub, map_neg, map_ofNat]

lemma map6_kleinPAS1 (φ : R →+* S) (a b g : R) (y : Fin 5 → R) :
    φ (kleinPAS1 a b g y) = kleinPAS1 (φ a) (φ b) (φ g) (fun i => φ (y i)) := by
  simp only [kleinPAS1, map_add, map_mul, map_pow, map_sub, map_neg, map_ofNat]

lemma map6_kleinPAS2 (φ : R →+* S) (a b g : R) (y : Fin 5 → R) :
    φ (kleinPAS2 a b g y) = kleinPAS2 (φ a) (φ b) (φ g) (fun i => φ (y i)) := by
  simp only [kleinPAS2, map_add, map_mul, map_pow, map_sub, map_neg, map_ofNat]

lemma map6_kleinPAS3 (φ : R →+* S) (a b g : R) (y : Fin 5 → R) :
    φ (kleinPAS3 a b g y) = kleinPAS3 (φ a) (φ b) (φ g) (fun i => φ (y i)) := by
  simp only [kleinPAS3, map_add, map_mul, map_pow, map_sub, map_neg, map_ofNat]

lemma map6_kleinPAS4 (φ : R →+* S) (a b g : R) (y : Fin 5 → R) :
    φ (kleinPAS4 a b g y) = kleinPAS4 (φ a) (φ b) (φ g) (fun i => φ (y i)) := by
  simp only [kleinPAS4, map_add, map_mul, map_pow, map_sub, map_neg, map_ofNat]

/-- Naturality of the Pfaffian tuple `kleinPAS`, componentwise. -/
lemma map6_kleinPAS (φ : R →+* S) (a b g : R) (y : Fin 5 → R) (k : Fin 5) :
    φ (kleinPAS a b g y k) = kleinPAS (φ a) (φ b) (φ g) (fun i => φ (y i)) k := by
  fin_cases k <;>
  simp only [kleinPAS, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_fin_one,
    kleinPAS0, kleinPAS1, kleinPAS2, kleinPAS3, kleinPAS4,
    map_add, map_mul, map_pow, map_sub, map_neg, map_ofNat]

/-- Naturality of the tangent vectors `asTanQ` of the AS quadric `kleinQAS`. -/
lemma map6_asTanQ (φ : R →+* S) (a b : R) (c : Fin 5 → R) (k i : Fin 5) :
    φ (asTanQ a b c k i) = asTanQ (φ a) (φ b) (fun j => φ (c j)) k i := by
  simp only [asTanQ, map_sub, map_mul, map6_kleinBilinAS, map6_kleinE]

/-- Naturality of the polarisation `asPolarP` of the AS Pfaffian map `kleinPAS`. -/
lemma map6_asPolarP (φ : R →+* S) (a b g : R) (c u : Fin 5 → R) (i : Fin 5) :
    φ (asPolarP a b g c u i)
      = asPolarP (φ a) (φ b) (φ g) (fun j => φ (c j)) (fun j => φ (u j)) i := by
  simp only [asPolarP, map_sub, map6_kleinPAS, map6_add_fun_eq, map_add]

/-- Naturality of the first ruling vector `asRuleQA`. -/
lemma map6_asRuleQA (φ : R →+* S) (a b g : R) (c : Fin 5 → R) (k : Fin 5) :
    φ (asRuleQA a b g c k) = asRuleQA (φ a) (φ b) (φ g) (fun j => φ (c j)) k := by
  simp only [asRuleQA, map6_asPolarP, map6_asTanQ]

/-- Naturality of the second ruling vector `asRuleQB`. -/
lemma map6_asRuleQB (φ : R →+* S) (a b g : R) (c : Fin 5 → R) (k : Fin 5) :
    φ (asRuleQB a b g c k) = asRuleQB (φ a) (φ b) (φ g) (fun j => φ (c j)) k := by
  simp only [asRuleQB, map6_asPolarP, map6_asTanQ]

/-- Naturality of the first component `kleinRAS0` of the inverse quadro-cubic map. -/
lemma map6_kleinRAS0 (φ : R →+* S) (a b g : R) (z : Fin 5 → R) :
    φ (kleinRAS0 a b g z) = kleinRAS0 (φ a) (φ b) (φ g) (fun i => φ (z i)) := by
  simp only [kleinRAS0, map_add, map_mul, map_pow, map_sub, map_neg, map_ofNat]

/-! ## Naturality of the polynomial coefficient forms -/

/-- Naturality of the polynomial ruling vector `qAS_A`. -/
lemma map6_qAS_A (φ : R →+* S) (a b g : R) (k : Fin 5) :
    MvPolynomial.map φ (qAS_A R a b g k) = qAS_A S (φ a) (φ b) (φ g) k := by
  simp only [qAS_A, map6_asRuleQA, MvPolynomial.map_C, MvPolynomial.map_X]

/-- Naturality of the polynomial ruling vector `qAS_B`. -/
lemma map6_qAS_B (φ : R →+* S) (a b g : R) (k : Fin 5) :
    MvPolynomial.map φ (qAS_B R a b g k) = qAS_B S (φ a) (φ b) (φ g) k := by
  simp only [qAS_B, map6_asRuleQB, MvPolynomial.map_C, MvPolynomial.map_X]

/-- Naturality of the polynomial `asCoeffPoly R a b g = R^AS_0(A + T·B)` under a change of the
coefficient ring. -/
lemma map6_asCoeffPoly (φ : R →+* S) (a b g : R) :
    Polynomial.map (MvPolynomial.map φ) (asCoeffPoly R a b g)
      = asCoeffPoly S (φ a) (φ b) (φ g) := by
  have h := map6_kleinRAS0 (R := Polynomial (MvPolynomial (Fin 5) R))
    (S := Polynomial (MvPolynomial (Fin 5) S)) (Polynomial.mapRingHom (MvPolynomial.map φ))
    (Polynomial.C (MvPolynomial.C a)) (Polynomial.C (MvPolynomial.C b))
    (Polynomial.C (MvPolynomial.C g))
    (fun k => Polynomial.C (qAS_A R a b g k) + Polynomial.X * Polynomial.C (qAS_B R a b g k))
  have h2 : Polynomial.mapRingHom (MvPolynomial.map φ) (asCoeffPoly R a b g)
      = asCoeffPoly S (φ a) (φ b) (φ g) := by
    rw [asCoeffPoly, h, asCoeffPoly]
    simp only [Polynomial.coe_mapRingHom, map6_qAS_A, map6_qAS_B, Polynomial.map_C,
      Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, MvPolynomial.map_C]
  exact h2

/-! ## The target lemma -/

theorem map_asCoeff6 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b g : R) (j : ℕ) :
    MvPolynomial.map φ (Work.MotAS.asCoeff6 R a b g j)
      = Work.MotAS.asCoeff6 S (φ a) (φ b) (φ g) j := by
  simp only [asCoeff6_eq, ← Polynomial.coeff_map]
  rw [map6_asCoeffPoly]

end Work.MotAS
