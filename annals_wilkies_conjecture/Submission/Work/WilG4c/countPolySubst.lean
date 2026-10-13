import Mathlib
import Submission.Work.WilG4c.polyCountEval_comp4
import Submission.Work.WilG4c.YbddAux

namespace Work.WilG4c

/-- **The count polynomial of the `StepStage` assembly.**  Substituting into a `Fin 4`-variable
polynomial `c₀` the values `D ↦ eval ![D,r] Bt`, `r ↦ r+1`, `k ↦ k · ((r+1)^(n+1) · (n + (r+1)^n))`
and `L ↦ L + log 2` is again the evaluation (at `![D,r,k,L]`) of a `Fin 4`-variable polynomial.
This is the count-bookkeeping step of BNZ §5.4: `c₀` is the count polynomial returned by
`F1Affine` for the padded tuple (`k` there is `tupleSizeBig k n r`, `r` there is `r+1`,
`L` there is `-log(ε/2) = -log ε + log 2`, and the degree fed in is the padded tuple's graph
degree `eval ![D,r] Bt`), and `c₁` is the count polynomial of the stage. -/
theorem countPolySubst (n : ℕ) (Bt : MvPolynomial (Fin 2) ℕ) (c₀ : MvPolynomial (Fin 4) ℝ) :
    ∃ c₁ : MvPolynomial (Fin 4) ℝ, ∀ (D r k : ℕ) (L : ℝ),
      MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), L] c₁ =
        MvPolynomial.eval ![((MvPolynomial.eval ![D, r] Bt : ℕ) : ℝ), ((r + 1 : ℕ) : ℝ),
          ((k * ((r + 1) ^ (n + 1) * (n + (r + 1) ^ n)) : ℕ) : ℝ), L + Real.log 2] c₀ := by
  -- The inclusion of the two variables `D, r` into the four variables `D, r, k, L`.
  set e : Fin 2 → Fin 4 := fun i => Fin.castLE (by norm_num : 2 ≤ 4) i with he
  -- `Bt` read as a real polynomial in the first two of the four variables.
  set Bℝ : MvPolynomial (Fin 4) ℝ :=
    MvPolynomial.rename e (MvPolynomial.map (Nat.castRingHom ℝ) Bt) with hBdef
  -- Evaluating `Bℝ` at a natural point recovers the (cast) evaluation of `Bt`.
  have hBev : ∀ (D r k : ℕ) (L : ℝ),
      MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), L] Bℝ
        = ((MvPolynomial.eval ![D, r] Bt : ℕ) : ℝ) := by
    intro D r k L
    have hcomp : (![(D : ℝ), (r : ℝ), (k : ℝ), L] ∘ e) = ![(D : ℝ), (r : ℝ)] := by
      funext i; fin_cases i <;> simp [he, Fin.castLE]
    rw [hBdef, MvPolynomial.eval_rename, hcomp, MvPolynomial.eval_map]
    have hpt : ![(D : ℝ), (r : ℝ)] = ⇑(Nat.castRingHom ℝ) ∘ ![D, r] := by
      funext i; fin_cases i <;> simp
    rw [hpt]
    exact (MvPolynomial.eval₂_comp (Nat.castRingHom ℝ) ![D, r] Bt).symm
  -- The polynomial `r + 1`, as a polynomial in the four variables.
  set R : MvPolynomial (Fin 4) ℝ := MvPolynomial.X (1 : Fin 4) + MvPolynomial.C (1 : ℝ) with hR
  -- The substitution of the four variables defining the `StepStage` assembly.
  set φ : Fin 4 → MvPolynomial (Fin 4) ℝ := ![
      Bℝ,
      R,
      MvPolynomial.X (2 : Fin 4) * (R ^ (n + 1) * (MvPolynomial.C (n : ℝ) + R ^ n)),
      MvPolynomial.X (3 : Fin 4) + MvPolynomial.C (Real.log 2)] with hφ
  refine ⟨MvPolynomial.bind₁ φ c₀, ?_⟩
  intro D r k L
  rw [eval_bind₁ φ c₀ ![(D : ℝ), (r : ℝ), (k : ℝ), L]]
  -- The substituted point is exactly the one in the statement.
  have hfun : (fun i : Fin 4 => MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), L] (φ i))
      = ![((MvPolynomial.eval ![D, r] Bt : ℕ) : ℝ), ((r + 1 : ℕ) : ℝ),
          ((k * ((r + 1) ^ (n + 1) * (n + (r + 1) ^ n)) : ℕ) : ℝ), L + Real.log 2] := by
    funext i
    fin_cases i <;> simp [hφ, hR, hBev]
  rw [hfun]

end Work.WilG4c
