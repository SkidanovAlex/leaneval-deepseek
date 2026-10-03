import Mathlib
import Submission.Work.Peluse.Ulower.iterDefs

namespace Work.Peluse.Ulower

/-- **Multiplicativity of `iterDelta'` over pointwise products, with translations.**
For a pointwise product of a translate of `f₀` and a translate of `f₁`, the iterated
`Δ'`-difference splits as the product of the two iterated differences, evaluated at the
correspondingly translated points.

This is the algebraic heart of `dualFn_iterDelta_pieces`: `Δ'` is a product of `2 ^ t` factors
each of which is a value of `F` or of its conjugate at some shifted point, so it is multiplicative
over pointwise products (complex multiplication is commutative), and it commutes with translations
in the evident way. -/
lemma iterDelta'_mul_shift : ∀ (t : ℕ) (sh : Fin t → ℤ × ℤ) (f₀ f₁ : ℤ → ℂ) (c d e : ℤ) (x : ℤ),
    iterDelta' t sh (fun w => f₀ (w - c) * f₁ (w + d - e)) x
      = iterDelta' t sh f₀ (x - c) * iterDelta' t sh f₁ (x + d - e) := by
  intro t
  induction t with
  | zero => intro sh f₀ f₁ c d e x; rfl
  | succ t ih =>
      intro sh f₀ f₁ c d e x
      simp only [iterDelta']
      simp only [ih]
      have h1 : x + (sh 0).1 - c = (x - c) + (sh 0).1 := by ring
      have h2 : x + (sh 0).1 + d - e = (x + d - e) + (sh 0).1 := by ring
      have h3 : x + (sh 0).2 - c = (x - c) + (sh 0).2 := by ring
      have h4 : x + (sh 0).2 + d - e = (x + d - e) + (sh 0).2 := by ring
      rw [h1, h2, h3, h4, star_mul]
      ring

theorem dualFn_iterDelta_pieces (s : ℕ) (M : ℕ) (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ)
    (sh : Fin s → ℤ × ℤ) (x : ℤ) :
    Work.Peluse.dualFn M P (Work.Peluse.Ulower.iterDelta' s sh f₀)
        (Work.Peluse.Ulower.iterDelta' s sh f₁) x
      = ((M : ℂ))⁻¹ * ∑ y ∈ Finset.Icc 1 M,
          Work.Peluse.Ulower.iterDelta' s sh (fun w : ℤ => f₀ (w - P.eval ((y : ℕ) : ℤ)) *
            f₁ (w + ((y : ℕ) : ℤ) - P.eval ((y : ℕ) : ℤ))) x := by
  rw [Work.Peluse.dualFn]
  refine congrArg (fun z => ((M : ℂ))⁻¹ * z) ?_
  refine Finset.sum_congr rfl (fun y _ => ?_)
  exact (iterDelta'_mul_shift s sh f₀ f₁ (P.eval ((y : ℕ) : ℤ)) ((y : ℕ) : ℤ)
    (P.eval ((y : ℕ) : ℤ)) x).symm

end Work.Peluse.Ulower
