import Mathlib

namespace Work.WilG4c

/-- **Evaluation of a substituted polynomial.**

If we replace `X i` by `f i` in `p` and then evaluate the result at a point `σ`,
this is the same as evaluating the original `p` directly at the point whose `i`-th
coordinate is the value `f i` takes at `σ`.

This is the two-variable, `ℕ`-coefficient form of `MvPolynomial.comp_aeval`. -/
lemma eval_aeval_eq (f : Fin 2 → MvPolynomial (Fin 2) ℕ) (σ : Fin 2 → ℕ)
    (p : MvPolynomial (Fin 2) ℕ) :
    MvPolynomial.eval σ (MvPolynomial.aeval f p)
      = MvPolynomial.eval (fun i => MvPolynomial.eval σ (f i)) p := by
  have h := MvPolynomial.comp_aeval f (MvPolynomial.aeval σ)
  have key := congrArg (fun (φ : MvPolynomial (Fin 2) ℕ →ₐ[ℕ] ℕ) => φ p) h
  simpa only [AlgHom.comp_apply, MvPolynomial.aeval_eq_eval] using key

/-- **Substituting a polynomial into the first variable.**

For any `q b : ℕ[X₀,X₁]` there is `b' : ℕ[X₀,X₁]` such that for all natural numbers
`D`, `r`, evaluating `b'` at `(D,r)` equals evaluating `b` at the point
`(q(D,r), r)`.  Concretely one takes `b'` to be the polynomial obtained from `b` by
substituting `X₀ ↦ q` and leaving `X₁` fixed. -/
theorem PolySubstFirst (q b : MvPolynomial (Fin 2) ℕ) :
    ∃ b' : MvPolynomial (Fin 2) ℕ, ∀ D r : ℕ,
      MvPolynomial.eval ![D, r] b' = MvPolynomial.eval ![MvPolynomial.eval ![D, r] q, r] b := by
  refine ⟨MvPolynomial.aeval ![q, MvPolynomial.X 1] b, fun D r => ?_⟩
  rw [eval_aeval_eq]
  have hfun : (fun i => MvPolynomial.eval ![D, r] (![q, MvPolynomial.X 1] i))
      = ![(MvPolynomial.eval ![D, r]) q, r] := by
    funext i
    fin_cases i <;> simp
  rw [hfun]

end Work.WilG4c
