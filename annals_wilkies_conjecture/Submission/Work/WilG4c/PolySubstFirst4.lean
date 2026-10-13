import Mathlib
import Submission.Work.WilG4c.polyCompEval

namespace Work.WilG4c

/-- **Substituting a natural polynomial into the first variable of a real polynomial.**

Given `q : ℕ[X₀,X₁]` and `c : ℝ[X₀,X₁,X₂,X₃]`, there is a real polynomial `c'` in the four
variables `(X₀,X₁,X₂,X₃)` whose value at `(D, r, k, u)` is the value of `c` at the point whose
first coordinate is `q(D, r)`.  Concretely one substitutes `X₀ ↦ q` (read as a real polynomial
in the first two of the four variables) and fixes the remaining variables. -/
theorem PolySubstFirst4 (q : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ) :
    ∃ c' : MvPolynomial (Fin 4) ℝ, ∀ (D r k : ℕ) (u : ℝ),
      MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), u] c' =
        MvPolynomial.eval ![((MvPolynomial.eval ![D, r] q : ℕ) : ℝ), (r : ℝ), (k : ℝ), u] c := by
  -- The inclusion of the two variables `D, r` into the four variables `D, r, k, u`.
  set e : Fin 2 → Fin 4 := fun i => Fin.castLE (by norm_num : 2 ≤ 4) i with he
  -- `q` read as a real polynomial in the first two of the four variables.
  set qℝ : MvPolynomial (Fin 4) ℝ :=
    MvPolynomial.rename e (MvPolynomial.map (Nat.castRingHom ℝ) q) with hqdef
  -- Evaluating `qℝ` at a natural point recovers the (cast) evaluation of `q`.
  have hqev : ∀ (D r k : ℕ) (u : ℝ),
      MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), u] qℝ
        = ((MvPolynomial.eval ![D, r] q : ℕ) : ℝ) := by
    intro D r k u
    have hcomp : (![(D : ℝ), (r : ℝ), (k : ℝ), u] ∘ e) = ![(D : ℝ), (r : ℝ)] := by
      funext i; fin_cases i <;> simp [he, Fin.castLE]
    rw [hqdef, MvPolynomial.eval_rename, hcomp, MvPolynomial.eval_map]
    have hpt : ![(D : ℝ), (r : ℝ)] = ⇑(Nat.castRingHom ℝ) ∘ ![D, r] := by
      funext i; fin_cases i <;> simp
    rw [hpt]
    exact (MvPolynomial.eval₂_comp (Nat.castRingHom ℝ) ![D, r] q).symm
  -- The substitution: `X₀ ↦ qℝ` and the other three variables fixed.
  set φ : Fin 4 → MvPolynomial (Fin 4) ℝ :=
    ![qℝ, MvPolynomial.X (1 : Fin 4), MvPolynomial.X (2 : Fin 4),
      MvPolynomial.X (3 : Fin 4)] with hφ
  refine ⟨MvPolynomial.bind₁ φ c, ?_⟩
  intro D r k u
  have hfun : (fun i : Fin 4 => MvPolynomial.eval₂Hom (RingHom.id ℝ)
      ![(D : ℝ), (r : ℝ), (k : ℝ), u] (φ i))
      = ![((MvPolynomial.eval ![D, r] q : ℕ) : ℝ), (r : ℝ), (k : ℝ), u] := by
    funext i
    fin_cases i
    · exact hqev D r k u
    · simp [hφ]
    · simp [hφ]
    · simp [hφ]
  -- `MvPolynomial.eval` is by definition `eval₂Hom (RingHom.id ℝ)`, so we may rewrite with the
  -- substitution lemma for `eval₂Hom`.
  change MvPolynomial.eval₂Hom (RingHom.id ℝ) ![(D : ℝ), (r : ℝ), (k : ℝ), u]
      (MvPolynomial.bind₁ φ c)
    = MvPolynomial.eval₂Hom (RingHom.id ℝ)
        ![((MvPolynomial.eval ![D, r] q : ℕ) : ℝ), (r : ℝ), (k : ℝ), u] c
  rw [MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℝ) ![(D : ℝ), (r : ℝ), (k : ℝ), u] φ c, hfun]

end Work.WilG4c
