import Mathlib

namespace Work.WilG4c.SectAux

/-- **Substituting a natural two-variable polynomial into the first variable of a real
four-variable polynomial.**

Given `d : ℕ[X₀,X₁]` and `C : ℝ[X₀,X₁,X₂,X₃]` there is a real polynomial `c` in the four
variables `(X₀,X₁,X₂,X₃)` whose value at `(x, y, z, w)` (with `x y : ℕ`, `z w : ℝ`) equals
the value of `C` at the point whose first coordinate is `d(x, y)` (cast to `ℝ`).  Concretely
one substitutes `X₀ ↦ d` (read as a real polynomial in the first two of the four variables)
and fixes the remaining variables. -/
theorem MvPolySubstVar4 (C : MvPolynomial (Fin 4) ℝ) (d : MvPolynomial (Fin 2) ℕ) :
    ∃ c : MvPolynomial (Fin 4) ℝ, ∀ (x y : ℕ) (z w : ℝ),
      MvPolynomial.eval ![(x : ℝ), (y : ℝ), z, w] c
        = MvPolynomial.eval ![((MvPolynomial.eval ![x, y] d : ℕ) : ℝ), (y : ℝ), z, w] C := by
  -- The inclusion of the two variables `x, y` into the four variables `x, y, z, w`.
  set e : Fin 2 → Fin 4 := fun i => Fin.castLE (by norm_num : 2 ≤ 4) i with he
  -- `d` read as a real polynomial in the first two of the four variables.
  set dℝ : MvPolynomial (Fin 4) ℝ :=
    MvPolynomial.rename e (MvPolynomial.map (Nat.castRingHom ℝ) d) with hddef
  -- Evaluating `dℝ` at a natural point recovers the (cast) evaluation of `d`.
  have hdev : ∀ (x y : ℕ) (z w : ℝ),
      MvPolynomial.eval ![(x : ℝ), (y : ℝ), z, w] dℝ
        = ((MvPolynomial.eval ![x, y] d : ℕ) : ℝ) := by
    intro x y z w
    have hcomp : (![(x : ℝ), (y : ℝ), z, w] ∘ e) = ![(x : ℝ), (y : ℝ)] := by
      funext i; fin_cases i <;> simp [he, Fin.castLE]
    rw [hddef, MvPolynomial.eval_rename, hcomp, MvPolynomial.eval_map]
    have hpt : ![(x : ℝ), (y : ℝ)] = ⇑(Nat.castRingHom ℝ) ∘ ![x, y] := by
      funext i; fin_cases i <;> simp
    rw [hpt]
    exact (MvPolynomial.eval₂_comp (Nat.castRingHom ℝ) ![x, y] d).symm
  -- The substitution: `X₀ ↦ dℝ` and the other three variables fixed.
  set φ : Fin 4 → MvPolynomial (Fin 4) ℝ :=
    ![dℝ, MvPolynomial.X (1 : Fin 4), MvPolynomial.X (2 : Fin 4),
      MvPolynomial.X (3 : Fin 4)] with hφ
  refine ⟨MvPolynomial.bind₁ φ C, ?_⟩
  intro x y z w
  have hfun : (fun i : Fin 4 => MvPolynomial.eval₂Hom (RingHom.id ℝ)
      ![(x : ℝ), (y : ℝ), z, w] (φ i))
      = ![((MvPolynomial.eval ![x, y] d : ℕ) : ℝ), (y : ℝ), z, w] := by
    funext i
    fin_cases i
    · exact hdev x y z w
    · simp [hφ]
    · simp [hφ]
    · simp [hφ]
  -- `MvPolynomial.eval` is by definition `eval₂Hom (RingHom.id ℝ)`, so we may rewrite with the
  -- substitution lemma for `eval₂Hom`.
  change MvPolynomial.eval₂Hom (RingHom.id ℝ) ![(x : ℝ), (y : ℝ), z, w]
      (MvPolynomial.bind₁ φ C)
    = MvPolynomial.eval₂Hom (RingHom.id ℝ)
        ![((MvPolynomial.eval ![x, y] d : ℕ) : ℝ), (y : ℝ), z, w] C
  rw [MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℝ) ![(x : ℝ), (y : ℝ), z, w] φ C, hfun]

end Work.WilG4c.SectAux
