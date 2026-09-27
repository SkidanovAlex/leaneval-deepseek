import Mathlib
import Submission.Work.Drive.Whitney.glAuxCoreDefs

/-!
# The key identity `Θ = ⟪χ, χ⟫` for the `glAuxCore` construction

In the notation of `glAuxCoreDefs` (at a fixed point `p`), writing

* `Am = gAm φ u p`,  `a = gAl φ u w p`,  `n = gNn φ u w p`,  `c = gC φ u w p`,
* `α = a + c`,  `χ = gChi φ u w ψ p = α • ψ p - (⟪ψ p, n⟫ / Am) • n`,

the scalar `Θ = gTheta φ u w ψ p` is by definition

  `Θ = α ⟪ψ p, χ⟫ - ⟪ψ p, n⟫ ⟪χ, n⟫ / Am`,

and the point of the lemma `gTheta_eq_inner_gChi` is that this equals `⟪χ, χ⟫ ≥ 0`.  In
particular `1 + Θ = 1 + ⟪χ, χ⟫ > 0`, which is what makes `gLam = (1 - α)/(1 + Θ)` a globally
regular smooth function (`∀ p, gThetaA φ φ₂ u w ψ p ≠ 0`), the hypothesis `hTh` of
`glAuxCoreDefs`.

The statement is a pure algebraic identity in an arbitrary real inner product space: with
`β = ⟪ψ, n⟫ / Am` the two defining equations are `χ = α • ψ - β • n` and
`Θ = α ⟪ψ, χ⟫ - β ⟪χ, n⟫`, and expanding both sides with bilinearity, symmetry of the real inner
product and `(x * y) / Am = (x / Am) * y` gives the result.
-/

namespace Work.Drive.Whitney

/-- Expansion of `⟪χ, χ⟫` for `χ = α • ψ - β • n`: the right-hand side is the expression that
defines `gTheta` once `β = ⟪ψ, n⟫ / Am` and `χ` is the corresponding `gChi`. -/
lemma inner_chi_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ψ n : E) (α β : ℝ) :
    inner ℝ (α • ψ - β • n) (α • ψ - β • n)
      = α * inner ℝ ψ (α • ψ - β • n) - β * inner ℝ (α • ψ - β • n) n := by
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm ψ n]
  ring

/-- The identity `gTheta = ⟪χ, χ⟫` in the abstract coordinates `ψ`, `n`, `α = a + c`, `Am`:
with `χ = α • ψ - (⟪ψ, n⟫ / Am) • n` one has
`α ⟪ψ, χ⟫ - ⟪ψ, n⟫ ⟪χ, n⟫ / Am = ⟪χ, χ⟫`. -/
lemma gTheta_form_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ψ n : E) (α A : ℝ) :
    α * inner ℝ ψ (α • ψ - (inner ℝ ψ n / A) • n)
      - inner ℝ ψ n * inner ℝ (α • ψ - (inner ℝ ψ n / A) • n) n / A
    = inner ℝ (α • ψ - (inner ℝ ψ n / A) • n) (α • ψ - (inner ℝ ψ n / A) • n) := by
  rw [mul_comm (inner ℝ ψ n), ← div_mul_eq_mul_div,
    inner_chi_self ψ n α (inner ℝ ψ n / A)]
  ring

theorem gTheta_eq_inner_gChi {m : ℕ} (u w ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (h : Work.Drive.Whitney.gAm φ u p ≠ 0) :
    Work.Drive.Whitney.gTheta φ u w ψ p =
      inner ℝ (Work.Drive.Whitney.gChi φ u w ψ p) (Work.Drive.Whitney.gChi φ u w ψ p) := by
  have hAm : gAm φ u p ≠ 0 := h
  have key := gTheta_form_eq (ψ p) (gNn φ u w p) (gAl φ u w p + gC φ u w p) (gAm φ u p)
  unfold gTheta gChi
  exact key

end Work.Drive.Whitney
