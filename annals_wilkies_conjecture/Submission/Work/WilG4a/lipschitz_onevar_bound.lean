import Mathlib
import Submission.Work.WilG4a.LipChartsDefs

set_option autoImplicit false

namespace Work.WilG4a

/-- Evaluation of an `aeval`-substitution: substituting the variables by polynomials `f`
and then evaluating at a point `x` is the same as evaluating `c` at the point obtained
by evaluating each `f i` at `x`. -/
lemma eval_aeval_fin3 (c : MvPolynomial (Fin 3) ℝ) (f : Fin 3 → MvPolynomial (Fin 3) ℝ)
    (x : Fin 3 → ℝ) :
    MvPolynomial.eval x (MvPolynomial.aeval f c) =
      MvPolynomial.eval (fun i => MvPolynomial.eval x (f i)) c := by
  induction c using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
      simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X, hp]

/-- The dominating polynomial built from `c`.  Writing `x, y, z` for the three variables
and `c(x,y,z)` for `c`, it is

`c(x,1,z) + (x-1)^2 * ((c(1,1,z) - c(0,1,z))^2 + z + 1)`.

For `D ≥ 1` the factor `(x-1)^2` is non-negative, and for `D = 0` one has
`x = 0`, so the correction term is `(c(1,1,k) - c(0,1,k))^2 + k + 1`, which
dominates the deficit `c(1,1,k) - c(0,1,k)` because
`s^2 + k + 1 - s = (s - 1/2)^2 + k + 3/4 ≥ 0`. -/
noncomputable def lipBound (c : MvPolynomial (Fin 3) ℝ) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.aeval
      (fun i => ![MvPolynomial.X 0, (1 : MvPolynomial (Fin 3) ℝ), MvPolynomial.X 2] i) c
    + (MvPolynomial.X 0 - 1) ^ 2 *
      ((MvPolynomial.aeval
            (fun i => ![(1 : MvPolynomial (Fin 3) ℝ), 1, MvPolynomial.X 2] i) c
          - MvPolynomial.aeval
            (fun i => ![(0 : MvPolynomial (Fin 3) ℝ), 1, MvPolynomial.X 2] i) c) ^ 2
        + MvPolynomial.X 2 + 1)

theorem lipschitz_onevar_bound (c : MvPolynomial (Fin 3) ℝ) :
    ∃ c' : MvPolynomial (Fin 3) ℝ, ∀ D k : ℕ,
      MvPolynomial.eval ![(max D 1 : ℝ), (1 : ℝ), (k : ℝ)] c ≤
        MvPolynomial.eval ![(D : ℝ), (1 : ℝ), (k : ℝ)] c' := by
  refine ⟨lipBound c, fun D k => ?_⟩
  -- The value of the constructed polynomial at the point `(D, 1, k)`.
  have key : MvPolynomial.eval ![(D : ℝ), 1, (k : ℝ)] (lipBound c)
      = MvPolynomial.eval ![(D : ℝ), 1, (k : ℝ)] c
        + ((D : ℝ) - 1) ^ 2 *
          ((MvPolynomial.eval ![(1 : ℝ), 1, (k : ℝ)] c
              - MvPolynomial.eval ![(0 : ℝ), 1, (k : ℝ)] c) ^ 2 + (k : ℝ) + 1) := by
    rw [lipBound]
    simp only [map_add, map_mul, map_pow, map_sub, map_one, MvPolynomial.eval_X]
    rw [eval_aeval_fin3, eval_aeval_fin3, eval_aeval_fin3]
    have h1 : (fun i => MvPolynomial.eval ![(D : ℝ), 1, (k : ℝ)]
        (![MvPolynomial.X 0, (1 : MvPolynomial (Fin 3) ℝ), MvPolynomial.X 2] i))
        = ![(D : ℝ), 1, (k : ℝ)] := by
      funext i; fin_cases i <;> simp
    have h0 : (fun i => MvPolynomial.eval ![(D : ℝ), 1, (k : ℝ)]
        (![(0 : MvPolynomial (Fin 3) ℝ), 1, MvPolynomial.X 2] i))
        = ![(0 : ℝ), 1, (k : ℝ)] := by
      funext i; fin_cases i <;> simp
    have h2 : (fun i => MvPolynomial.eval ![(D : ℝ), 1, (k : ℝ)]
        (![(1 : MvPolynomial (Fin 3) ℝ), 1, MvPolynomial.X 2] i))
        = ![(1 : ℝ), 1, (k : ℝ)] := by
      funext i; fin_cases i <;> simp
    rw [h1, h0, h2]
    simp
  rcases Nat.eq_zero_or_pos D with hD | hD
  · -- `D = 0`: the left point is `1` and the correction supplies the deficit.
    subst hD
    rw [key]
    simp only [Nat.cast_zero]
    have hmax : (max (0 : ℝ) 1) = 1 := by norm_num
    rw [hmax]
    nlinarith [sq_nonneg (MvPolynomial.eval ![(1 : ℝ), 1, (k : ℝ)] c
        - MvPolynomial.eval ![(0 : ℝ), 1, (k : ℝ)] c - 1 / 2),
      (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
  · -- `D ≥ 1`: the left point is `D` and the correction is non-negative.
    have hmax : (max D 1 : ℝ) = (D : ℝ) := by
      have hle : (1 : ℝ) ≤ (D : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hD)
      rw [max_eq_left hle]
    rw [key, hmax]
    have hnn : (0 : ℝ) ≤ ((MvPolynomial.eval ![(1 : ℝ), 1, (k : ℝ)] c
        - MvPolynomial.eval ![(0 : ℝ), 1, (k : ℝ)] c) ^ 2 + (k : ℝ) + 1) := by positivity
    nlinarith [mul_nonneg (sq_nonneg ((D : ℝ) - 1)) hnn]

end Work.WilG4a
