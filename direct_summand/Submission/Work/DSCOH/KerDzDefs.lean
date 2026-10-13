/-
Area DSCOH — the "constant" degree-zero Čech cochain of the chart complex of the structure
sheaf, used to identify the kernel of the first Čech differential of the grading `shift 0`
(the standard grading of `A[X₀,…,X_{n-1}]`).

For a commutative ring `A` the module of global sections of `O_{ℙ^{n-1}}` in degree `0` is `A`,
so `H⁰` of the chart Čech complex of `shift 0` is `A`; this file contains the vocabulary for
that statement: `constElem S a`, the element of `degZero (shift 0) S` given by the constant `a`
on the chart `S`, and `constLin`, the resulting `A`-linear map `A → ∏_{S} degZero (shift 0) S`.
-/
import Mathlib
import Submission.Work.DSCOH.ShiftToolkit
import Submission.Work.DSCOH.Cech
import Submission.Work.DSCOH.shift_gradedSMul

open MvPolynomial

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ}

/-- The monomial attached to a singleton chart is the corresponding variable. -/
lemma monomial_singleton (i : Fin n) :
    monomial (A := A) ({i} : Finset (Fin n)) = (MvPolynomial.X i : Poly A n) := by
  simp [monomial, Var]

/-- Dividing the localization at `S` by the unit `den S 0 = 1` does nothing. -/
lemma divBy_one_apply (S : Finset (Fin n)) (x : locAt (A := A) (M := Poly A n) S) :
    LocalizedModule.divBy (1 : subS (A := A) S) x = x := by
  induction x using LocalizedModule.induction_on with
  | h m s => rw [LocalizedModule.divBy_apply, LocalizedModule.liftOn_mk, mul_one]

/-- Dividing by `X_S^0 = 1` does nothing. -/
lemma divPow_zero_apply (S : Finset (Fin n)) (x : locAt (A := A) (M := Poly A n) S) :
    divPow (A := A) (M := Poly A n) S 0 x = x := by
  have h : den (A := A) S 0 = 1 := Subtype.ext (by simp [den])
  change LocalizedModule.divBy (den (A := A) S 0) x = x
  rw [h]
  exact divBy_one_apply (A := A) (n := n) S x

/-- The image of the constant `a` in the degree-zero part of the localization at the chart `S`. -/
noncomputable def constElem (S : Finset (Fin n)) (a : A) :
    degZero (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) 0) S :=
  ⟨toLoc (A := A) (M := Poly A n) S (MvPolynomial.C a), by
    rw [← divPow_zero_apply (A := A) (n := n) S
      (toLoc (A := A) (M := Poly A n) S (MvPolynomial.C a))]
    refine divPow_toLoc_mem (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) 0) S 0 ?_
    rw [Nat.zero_mul, shift_of_le (Nat.zero_le 0)]
    exact (MvPolynomial.mem_homogeneousSubmodule 0 (MvPolynomial.C a)).mpr
      (MvPolynomial.isHomogeneous_C (Fin n) a)⟩

/-- The `A`-linear map `A → ∏_{|S|=1} degZero (shift 0) S` sending `a` to the constant family. -/
noncomputable def constLin : A →ₗ[A] CechTerm (A := A) (n := n) (M := Poly A n)
    (shift (A := A) (n := n) 0) 0 :=
  LinearMap.pi fun S =>
    ((toLoc (A := A) (M := Poly A n) S.1).comp (Algebra.linearMap A (Poly A n))).codRestrict
      (degZero (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) 0) S.1)
      (fun a => (constElem (A := A) (n := n) S.1 a).2)

/-- The value of `constLin` at a chart is the constant family. -/
lemma constLin_apply (a : A) (S : {S : Finset (Fin n) // S.card = 0 + 1}) :
    constLin (A := A) (n := n) a S = constElem (A := A) (n := n) S.1 a := rfl

/-- Naturality of the chart restriction maps on the images of the structure map: in every chart
which inverts more variables, the class of `m` is still the class of `m` with denominator `1`. -/
lemma resAt_toLoc (S T : Finset (Fin n)) (h : S ⊆ T) (m : Poly A n) :
    resAt (A := A) (M := Poly A n) h (toLoc (A := A) (M := Poly A n) S m) =
      toLoc (A := A) (M := Poly A n) T m := by
  rw [show toLoc (A := A) (M := Poly A n) S m = LocalizedModule.mk m 1 from rfl,
    resAt_mk (A := A) S T h m 1]
  rfl

end Work.DSCOH
