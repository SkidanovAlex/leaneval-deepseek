import Mathlib

namespace Work.WilG4c.SectAux

theorem MvPolySubstVar (B : MvPolynomial (Fin 2) ℕ) (d : MvPolynomial (Fin 2) ℕ) :
    ∃ b' : MvPolynomial (Fin 2) ℕ, ∀ x y : ℕ,
      MvPolynomial.eval ![x, y] b'
        = MvPolynomial.eval ![MvPolynomial.eval ![x, y] d, y] B := by
  -- Substitute `X 0 ↦ d` and keep `X 1 ↦ X 1` in `B`.
  refine ⟨MvPolynomial.eval₂ MvPolynomial.C
    (fun i : Fin 2 => if i = 0 then d else MvPolynomial.X i) B, ?_⟩
  intro x y
  have hf : (⇑(MvPolynomial.eval fun i : Fin 2 => ![x, y] i) ∘
      fun i : Fin 2 => if i = 0 then d else MvPolynomial.X i)
      = ![MvPolynomial.eval ![x, y] d, y] := by
    funext i
    fin_cases i <;> simp
  rw [← MvPolynomial.eval_assoc (fun i : Fin 2 => if i = 0 then d else MvPolynomial.X i)
    (fun i : Fin 2 => ![x, y] i) B, hf]

end Work.WilG4c.SectAux
