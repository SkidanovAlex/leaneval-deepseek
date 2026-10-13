/-
  WilG4a — bookkeeping for the polynomial format/degree bounds.

  The bounds in `FLem1`/`F1Affine1` are evaluations of polynomials in `ℕ`-coefficients.  When
  one construction is fed into another, the degree bound of the output must be re-expressed in
  terms of the *original* degree variable.  The two lemmas here perform the two substitutions
  that occur: replacing the first variable by another polynomial (composition), and shifting the
  second variable (used to pass from "order `j`" bounds to a uniform "order `r+1`" bound).
-/
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false
namespace Work.WilG4a


/-- Number of variables of the degree polynomials. -/
abbrev Sigma : Type := Fin 2

/-- **Composition of degree bounds**: `b.eval ![g.eval ![D,r], r]` is again the evaluation of a
polynomial at `![D, r]`. -/
theorem exists_eval_comp (b g : MvPolynomial Sigma ℕ) :
    ∃ d : MvPolynomial Sigma ℕ, ∀ D r : ℕ, b.eval ![g.eval ![D, r], r] = d.eval ![D, r] := by
  refine ⟨MvPolynomial.bind₁ (fun i : Sigma => if i = 0 then g else MvPolynomial.X i) b, ?_⟩
  intro D r
  have h := MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℕ) ![D, r]
    (fun i : Sigma => if i = 0 then g else MvPolynomial.X i) b
  have hfun : (fun i : Sigma => MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, r]
      (if i = 0 then g else MvPolynomial.X i)) = ![g.eval ![D, r], r] := by
    funext i
    fin_cases i <;> simp
  rw [hfun] at h
  change MvPolynomial.eval₂Hom (RingHom.id ℕ) ![g.eval ![D, r], r] b =
    MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, r]
      (MvPolynomial.bind₁ (fun i : Sigma => if i = 0 then g else MvPolynomial.X i) b)
  exact h.symm

/-- **Shifting the order variable**: a bound valid at `r + 1` is again the evaluation of a
polynomial at `r`. -/
theorem exists_eval_shift (b : MvPolynomial Sigma ℕ) :
    ∃ d : MvPolynomial Sigma ℕ, ∀ D r : ℕ, b.eval ![D, r + 1] = d.eval ![D, r] := by
  refine ⟨MvPolynomial.bind₁ (fun i : Sigma => if i = 0 then MvPolynomial.X i
    else MvPolynomial.X i + 1) b, ?_⟩
  intro D r
  have h := MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℕ) ![D, r]
    (fun i : Sigma => if i = 0 then MvPolynomial.X i else MvPolynomial.X i + 1) b
  have hfun : (fun i : Sigma => MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, r]
      (if i = 0 then MvPolynomial.X i else MvPolynomial.X i + 1)) = ![D, r + 1] := by
    funext i
    fin_cases i <;> simp
  rw [hfun] at h
  change MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, r + 1] b =
    MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, r]
      (MvPolynomial.bind₁ (fun i : Sigma => if i = 0 then MvPolynomial.X i
        else MvPolynomial.X i + 1) b)
  exact h.symm

end Work.WilG4a
