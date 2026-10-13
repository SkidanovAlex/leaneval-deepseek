import Mathlib
import Submission.Work.WilG4c.polyCompEval

namespace Work.WilG4c

open MvPolynomial

/-- Evaluation of a substitution (composition) of multivariate polynomials:
substituting the variables of `p` by the polynomials `φ i` and then evaluating at a point `x`
is the same as evaluating `p` at the point `i ↦ eval x (φ i)`. -/
lemma eval_bind₁ (φ : Fin 4 → MvPolynomial (Fin 4) ℝ) (p : MvPolynomial (Fin 4) ℝ)
    (x : Fin 4 → ℝ) :
    MvPolynomial.eval x (MvPolynomial.bind₁ φ p)
      = MvPolynomial.eval (fun i => MvPolynomial.eval x (φ i)) p :=
  MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℝ) x φ p

theorem polyCountEval_comp4 (B : MvPolynomial (Fin 2) ℕ) (K : ℕ) (c : MvPolynomial (Fin 4) ℝ) :
    ∃ c' : MvPolynomial (Fin 4) ℝ, ∀ (D r k : ℕ) (L : ℝ),
      MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), L] c' =
        MvPolynomial.eval ![((MvPolynomial.eval ![D, r] B : ℕ) : ℝ) + (K : ℝ), (r : ℝ), (k : ℝ),
          L + Real.log 2] c := by
  -- The inclusion of the two variables `D, r` into the four variables `D, r, k, L`.
  set e : Fin 2 → Fin 4 := fun i => Fin.castLE (by norm_num : 2 ≤ 4) i with he
  -- `B` read as a real polynomial in the first two of the four variables.
  set Bℝ : MvPolynomial (Fin 4) ℝ :=
    MvPolynomial.rename e (MvPolynomial.map (Nat.castRingHom ℝ) B) with hBdef
  -- Evaluating `Bℝ` at a natural point recovers the (cast) evaluation of `B`.
  have hBev : ∀ (D r k : ℕ) (L : ℝ),
      MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), L] Bℝ
        = ((MvPolynomial.eval ![D, r] B : ℕ) : ℝ) := by
    intro D r k L
    have hcomp : (![(D : ℝ), (r : ℝ), (k : ℝ), L] ∘ e) = ![(D : ℝ), (r : ℝ)] := by
      funext i; fin_cases i <;> simp [he, Fin.castLE]
    rw [hBdef, MvPolynomial.eval_rename, hcomp, MvPolynomial.eval_map]
    have hpt : ![(D : ℝ), (r : ℝ)] = ⇑(Nat.castRingHom ℝ) ∘ ![D, r] := by
      funext i; fin_cases i <;> simp
    rw [hpt]
    exact (MvPolynomial.eval₂_comp (Nat.castRingHom ℝ) ![D, r] B).symm
  -- The substitution: `X₀ ↦ Bℝ + K`, `X₁ ↦ X₁`, `X₂ ↦ X₂`, `X₃ ↦ X₃ + log 2`.
  set φ : Fin 4 → MvPolynomial (Fin 4) ℝ := ![
      Bℝ + MvPolynomial.C (K : ℝ),
      MvPolynomial.X (1 : Fin 4),
      MvPolynomial.X (2 : Fin 4),
      MvPolynomial.X (3 : Fin 4) + MvPolynomial.C (Real.log 2)] with hφ
  refine ⟨MvPolynomial.bind₁ φ c, ?_⟩
  intro D r k L
  rw [eval_bind₁ φ c ![(D : ℝ), (r : ℝ), (k : ℝ), L]]
  have hfun : (fun i : Fin 4 => MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), L] (φ i))
      = ![((MvPolynomial.eval ![D, r] B : ℕ) : ℝ) + (K : ℝ), (r : ℝ), (k : ℝ),
          L + Real.log 2] := by
    funext i
    fin_cases i <;> simp [hφ, hBev, MvPolynomial.eval_add, MvPolynomial.eval_C,
      MvPolynomial.eval_X]
  rw [hfun]

end Work.WilG4c
