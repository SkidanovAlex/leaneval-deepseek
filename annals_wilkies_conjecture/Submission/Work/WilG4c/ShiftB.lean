import Mathlib

namespace Work.WilG4c

/-- The polynomial shift lemma: given `b'`, there is a polynomial `b` whose value at
`(D, r)` equals the value of `b'` at `(D + 2, r)` plus `2`. We take
`b := b'` with `X 0` substituted by `X 0 + 2`, plus the constant `2`
(via `MvPolynomial.bind₁`). -/
theorem ShiftB (b' : MvPolynomial (Fin 2) ℕ) :
    ∃ b : MvPolynomial (Fin 2) ℕ, ∀ D r : ℕ,
      MvPolynomial.eval ![D, r] b = MvPolynomial.eval ![D + 2, r] b' + 2 := by
  refine ⟨MvPolynomial.bind₁ (![MvPolynomial.X 0 + 2, MvPolynomial.X 1] :
      Fin 2 → MvPolynomial (Fin 2) ℕ) b' + 2, ?_⟩
  intro D r
  simp only [MvPolynomial.eval]
  rw [map_add, MvPolynomial.eval₂Hom_bind₁]
  have hfun : (fun i : Fin 2 =>
        (MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, r])
          (![MvPolynomial.X 0 + 2, MvPolynomial.X 1] i)) = ![D + 2, r] := by
    funext i
    fin_cases i <;> simp
  rw [hfun]
  simp

end Work.WilG4c
