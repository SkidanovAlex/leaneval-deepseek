import Mathlib

namespace Work.HP.Sig2.RW

/-- The `3 × 3` linear system with matrix `[[a², b², (a+b)²], [ab, bc, (a+b)(b+c)], [b², c², (b+c)²]]` has a solution for every right-hand side whenever `a * c - b * b ≠ 0`: the determinant of the matrix is `-(a*c - b^2)^3`. -/
theorem three_solve (a b c A B C : ℝ) (h : a * c - b * b ≠ 0) :
    ∃ α β γ : ℝ,
      α * a ^ 2 + β * b ^ 2 + γ * (a + b) ^ 2 = A ∧
      α * a * b + β * b * c + γ * (a + b) * (b + c) = B ∧
      α * b ^ 2 + β * c ^ 2 + γ * (b + c) ^ 2 = C := by
  refine ⟨(c*(b+c)*A - (a*c + 2*b*c + b^2)*B + b*(a+b)*C)/(a*c-b*b)^2,
          (b*(b+c)*A - (a*c + 2*a*b + b^2)*B + a*(a+b)*C)/(a*c-b*b)^2,
          (-b*c*A + (b^2 + a*c)*B - a*b*C)/(a*c-b*b)^2, ?_, ?_, ?_⟩
  · set d : ℝ := a*c - b*b with hd
    have hdne : d ≠ 0 := h
    field_simp [hdne]
    rw [hd]
    ring
  · set d : ℝ := a*c - b*b with hd
    have hdne : d ≠ 0 := h
    field_simp [hdne]
    rw [hd]
    ring
  · set d : ℝ := a*c - b*b with hd
    have hdne : d ≠ 0 := h
    field_simp [hdne]
    rw [hd]
    ring

end Work.HP.Sig2.RW
