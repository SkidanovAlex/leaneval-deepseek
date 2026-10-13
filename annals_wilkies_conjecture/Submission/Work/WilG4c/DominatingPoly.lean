import Mathlib
import Submission.Work.WilG4c.polyCompEval

namespace Work.WilG4c

theorem DominatingPoly (b p : MvPolynomial (Fin 2) ℕ) :
    ∃ B : MvPolynomial (Fin 2) ℕ, ∀ D r : ℕ,
      MvPolynomial.eval ![MvPolynomial.eval ![D, r] p, 1] b ≤ MvPolynomial.eval ![D, r] B := by
  -- Substituting `X₀ ↦ p`, `X₁ ↦ 1` into `b` makes the two sides equal identically.
  refine ⟨(MvPolynomial.bind₁ (fun i : Fin 2 => if i = 0 then p else MvPolynomial.C 1)) b, ?_⟩
  intro D r
  have h := MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℕ) ![D, r]
    (fun i : Fin 2 => if i = 0 then p else MvPolynomial.C 1) b
  have hfun : (fun i : Fin 2 => MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, r]
      (if i = 0 then p else MvPolynomial.C 1)) = ![MvPolynomial.eval ![D, r] p, 1] := by
    funext i
    fin_cases i
    · simp
    · simp
  rw [hfun] at h
  exact le_of_eq h.symm

end Work.WilG4c
