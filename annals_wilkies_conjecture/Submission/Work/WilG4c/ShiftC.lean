import Mathlib

namespace Work.WilG4c

open MvPolynomial

/-- The affine polynomial substitution
`(x₀, x₁, x₂, x₃) ↦ (x₀ + 2, x₁, x₂, x₃ + log 2)`, as a map of variables. -/
noncomputable def shiftSubst : Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![(X 0 : MvPolynomial (Fin 4) ℝ) + C 2, X 1, X 2, X 3 + C (Real.log 2)]

/-- Substituting the variables as in `shiftSubst` and then evaluating at `x` is the same as
evaluating the original polynomial at the shifted point
`(x₀ + 2, x₁, x₂, x₃ + log 2)`. -/
lemma eval_aeval_shiftSubst (c' : MvPolynomial (Fin 4) ℝ) (x : Fin 4 → ℝ) :
    MvPolynomial.eval x (MvPolynomial.aeval shiftSubst c')
      = MvPolynomial.eval ![x 0 + 2, x 1, x 2, x 3 + Real.log 2] c' := by
  rw [← MvPolynomial.aeval_eq_eval]
  rw [← AlgHom.comp_apply]
  rw [MvPolynomial.comp_aeval]
  have hF : (fun i => (MvPolynomial.aeval x) (shiftSubst i))
      = ![x 0 + 2, x 1, x 2, x 3 + Real.log 2] := by
    funext i
    fin_cases i <;> simp [shiftSubst]
  rw [hF, MvPolynomial.aeval_eq_eval]

/-- Specialised form of `eval_aeval_shiftSubst` in coordinates. -/
lemma eval_aeval_shiftSubst' (c' : MvPolynomial (Fin 4) ℝ) (D r k u : ℝ) :
    MvPolynomial.eval ![D, r, k, u] (MvPolynomial.aeval shiftSubst c')
      = MvPolynomial.eval ![D + 2, r, k, u + Real.log 2] c' := by
  simpa using eval_aeval_shiftSubst c' ![D, r, k, u]

/-- **Shift lemma C.**  For every polynomial `c'` and every `T : ℕ` there is a polynomial `c`
such that, for all `D r k : ℕ` and `ε ∈ (0,1)`,
`T · c'(D+2, r, k, -log(ε/2)) ≤ c(D, r, k, -log ε)`.

The polynomial is obtained by the affine substitution `x₀ ↦ x₀ + 2`, `x₃ ↦ x₃ + log 2`
(together with the scalar `T`); the identity `-log(ε/2) = -log ε + log 2` matches the two
arguments, so the inequality is in fact an equality. -/
theorem ShiftC (c' : MvPolynomial (Fin 4) ℝ) (T : ℕ) :
    ∃ c : MvPolynomial (Fin 4) ℝ, ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
      (T : ℝ) * MvPolynomial.eval ![((D + 2 : ℕ) : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] c'
        ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c := by
  refine ⟨C (T : ℝ) * MvPolynomial.aeval shiftSubst c', ?_⟩
  intro D r k ε hε0 hε1
  have hlog : -Real.log (ε / 2) = -Real.log ε + Real.log 2 := by
    rw [Real.log_div (ne_of_gt hε0) (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hpt : ![((D + 2 : ℕ) : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)]
      = ![((D : ℝ) + 2), (r : ℝ), (k : ℝ), -Real.log ε + Real.log 2] := by
    funext i
    fin_cases i <;> simp [hlog, Nat.cast_add]
  rw [hpt]
  have key : MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε]
        (C (T : ℝ) * MvPolynomial.aeval shiftSubst c')
      = (T : ℝ) * MvPolynomial.eval ![((D : ℝ) + 2), (r : ℝ), (k : ℝ),
          -Real.log ε + Real.log 2] c' := by
    rw [map_mul, MvPolynomial.eval_C, eval_aeval_shiftSubst]
    simp
  rw [key]

end Work.WilG4c
