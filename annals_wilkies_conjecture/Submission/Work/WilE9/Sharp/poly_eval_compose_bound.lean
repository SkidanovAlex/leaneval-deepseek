import Mathlib
import Submission.Work.WilE9.Defs

namespace Work.WilE9.Sharp

theorem poly_eval_compose_bound (bD : MvPolynomial (Fin 4) ℕ) (bE : MvPolynomial (Fin 3) ℕ)
    (p₀ b₁ : Polynomial ℕ) (a₀ : ℕ) :
    ∃ b : MvPolynomial (Fin 2) ℕ, ∀ D k : ℕ,
      MvPolynomial.eval ![p₀.eval D, b₁.eval D, k, a₀] bD +
        MvPolynomial.eval ![b₁.eval D, k, a₀] bE ≤ MvPolynomial.eval ![D, k] b := by
  -- We exhibit the dominating polynomial explicitly, by substituting into `bD`, `bE` the
  -- polynomials (in the two variables `D`, `k`) that `p₀.eval D`, `b₁.eval D`, `k` and `a₀`
  -- represent.  Then the inequality is in fact an equality of `ℕ`-polynomial evaluations.
  let Q₀ : MvPolynomial (Fin 2) ℕ := p₀.toMvPolynomial (0 : Fin 2)
  let Q₁ : MvPolynomial (Fin 2) ℕ := b₁.toMvPolynomial (0 : Fin 2)
  let gD : Fin 4 → MvPolynomial (Fin 2) ℕ := ![Q₀, Q₁, MvPolynomial.X 1, MvPolynomial.C a₀]
  let gE : Fin 3 → MvPolynomial (Fin 2) ℕ := ![Q₁, MvPolynomial.X 1, MvPolynomial.C a₀]
  refine ⟨MvPolynomial.eval₂ MvPolynomial.C gD bD + MvPolynomial.eval₂ MvPolynomial.C gE bE, ?_⟩
  intro D k
  have hfunD : (MvPolynomial.eval ![D, k]) ∘ gD = ![p₀.eval D, b₁.eval D, k, a₀] := by
    funext i
    fin_cases i <;> simp [gD, Q₀, Q₁]
  have hfunE : (MvPolynomial.eval ![D, k]) ∘ gE = ![b₁.eval D, k, a₀] := by
    funext i
    fin_cases i <;> simp [gE, Q₁]
  have hD : MvPolynomial.eval ![D, k] (MvPolynomial.eval₂ MvPolynomial.C gD bD)
      = MvPolynomial.eval ![p₀.eval D, b₁.eval D, k, a₀] bD := by
    rw [← MvPolynomial.eval_assoc gD ![D, k] bD, hfunD]
  have hE : MvPolynomial.eval ![D, k] (MvPolynomial.eval₂ MvPolynomial.C gE bE)
      = MvPolynomial.eval ![b₁.eval D, k, a₀] bE := by
    rw [← MvPolynomial.eval_assoc gE ![D, k] bE, hfunE]
  rw [MvPolynomial.eval_add, hD, hE]

end Work.WilE9.Sharp
