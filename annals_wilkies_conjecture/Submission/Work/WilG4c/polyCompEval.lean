import Mathlib

namespace Work.WilG4c

/-- **Composition of a degree bound with a univariate polynomial.**

For `b : ℕ[X₀,X₁]` and `c : ℕ[T]`, the function `D ↦ b.eval (c.eval D, 1)` is again the
evaluation at `(D, 0)` of some two-variable polynomial `B` with natural coefficients: one
substitutes `X₀ ↦ c(X₀)` and `X₁ ↦ 1` in `b`. -/
theorem polyCompEval (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ) :
    ∃ B : MvPolynomial (Fin 2) ℕ, ∀ D : ℕ,
      MvPolynomial.eval ![D, 0] B = MvPolynomial.eval ![(c.eval D), 1] b := by
  -- `p` is the polynomial `c` read as a polynomial in the first variable.
  let p : MvPolynomial (Fin 2) ℕ := Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) c
  refine ⟨MvPolynomial.bind₁ (fun i : Fin 2 => if i = 0 then p else MvPolynomial.C 1) b, ?_⟩
  intro D
  -- Evaluating `p` at `(D, 0)` recovers `c.eval D`.
  have hp : MvPolynomial.eval ![D, 0] p = c.eval D := by
    have hcomp : (MvPolynomial.eval (fun i : Fin 2 => ![D, 0] i)).comp
        (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)) =
        Polynomial.eval₂RingHom (RingHom.id ℕ) D := by
      refine Polynomial.ringHom_ext ?_ ?_
      · intro a
        simp [Polynomial.eval₂RingHom]
      · simp [Polynomial.eval₂RingHom]
    have := RingHom.congr_fun hcomp c
    change MvPolynomial.eval (fun i : Fin 2 => ![D, 0] i)
        (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) c) =
        Polynomial.eval₂ (RingHom.id ℕ) D c at this
    simpa [p] using this
  -- The substitution lemma computes the evaluation of `bind₁`.
  have h := MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℕ) ![D, 0]
    (fun i : Fin 2 => if i = 0 then p else MvPolynomial.C 1) b
  have hfun : (fun i : Fin 2 => MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, 0]
      (if i = 0 then p else MvPolynomial.C 1)) = ![(c.eval D), 1] := by
    funext i
    fin_cases i
    · simpa using hp
    · simp
  rw [hfun] at h
  exact h

end Work.WilG4c
