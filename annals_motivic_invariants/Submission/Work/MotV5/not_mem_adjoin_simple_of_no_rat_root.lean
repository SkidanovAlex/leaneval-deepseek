import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

theorem not_mem_adjoin_simple_of_no_rat_root {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    (x y : Ω) (b₁ b₂ b₃ b₄ b₆ : F) (hx : Transcendental F x)
    (hW : y ^ 2 + (algebraMap F Ω b₁ * x + algebraMap F Ω b₃) * y
        = x ^ 3 + algebraMap F Ω b₂ * x ^ 2 + algebraMap F Ω b₄ * x + algebraMap F Ω b₆)
    (hno : ∀ r s : Polynomial F, s ≠ 0 →
        r ^ 2 + (Polynomial.C b₁ * Polynomial.X + Polynomial.C b₃) * r * s
          - (Polynomial.X ^ 3 + Polynomial.C b₂ * Polynomial.X ^ 2
              + Polynomial.C b₄ * Polynomial.X + Polynomial.C b₆) * s ^ 2 ≠ 0) :
    y ∉ (IntermediateField.adjoin F ({x} : Set Ω) : Set Ω) := by
  -- Suppose `y` lay in `F⟮x⟯`; then `y = r(x)/s(x)` for polynomials `r, s` with `s ≠ 0`.
  intro hy
  -- Transcendence of `x` is exactly injectivity of the evaluation map `aeval x`.
  have hx' : ∀ p : Polynomial F, Polynomial.aeval x p = 0 → p = 0 :=
    transcendental_iff.mp hx
  obtain ⟨r, s, hs, hyrep⟩ :
      ∃ r s : Polynomial F, s ≠ 0 ∧ y = Polynomial.aeval x r / Polynomial.aeval x s := by
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff (F := F) (α := x) y).mp hy
    by_cases hs : s = 0
    · subst hs
      exact ⟨0, 1, one_ne_zero, by rw [hrs]; simp⟩
    · exact ⟨r, s, hs, hrs⟩
  -- Hence `y * s(x) = r(x)`.
  have hsne : Polynomial.aeval x s ≠ 0 := fun h => hs (hx' s h)
  have hys : y * Polynomial.aeval x s = Polynomial.aeval x r := by
    rw [hyrep, div_mul_cancel₀ _ hsne]
  -- Multiplying the Weierstrass relation by `s(x)²` and substituting gives a polynomial
  -- relation in `x`.
  have key : (Polynomial.aeval x r) ^ 2
        + (algebraMap F Ω b₁ * x + algebraMap F Ω b₃) * Polynomial.aeval x r * Polynomial.aeval x s
      - (x ^ 3 + algebraMap F Ω b₂ * x ^ 2 + algebraMap F Ω b₄ * x + algebraMap F Ω b₆)
          * (Polynomial.aeval x s) ^ 2 = 0 := by
    have h1 : (y * Polynomial.aeval x s) ^ 2
          + (algebraMap F Ω b₁ * x + algebraMap F Ω b₃) * (y * Polynomial.aeval x s)
              * Polynomial.aeval x s
        - (x ^ 3 + algebraMap F Ω b₂ * x ^ 2 + algebraMap F Ω b₄ * x + algebraMap F Ω b₆)
            * (Polynomial.aeval x s) ^ 2
        = (y ^ 2 + (algebraMap F Ω b₁ * x + algebraMap F Ω b₃) * y
            - (x ^ 3 + algebraMap F Ω b₂ * x ^ 2 + algebraMap F Ω b₄ * x
                + algebraMap F Ω b₆)) * (Polynomial.aeval x s) ^ 2 := by
      first | refl_ring1 | ring
    rw [← hys, h1, sub_eq_zero.mpr hW, zero_mul]
  let P : Polynomial F := r ^ 2 + (Polynomial.C b₁ * Polynomial.X + Polynomial.C b₃) * r * s
      - (Polynomial.X ^ 3 + Polynomial.C b₂ * Polynomial.X ^ 2 + Polynomial.C b₄ * Polynomial.X
          + Polynomial.C b₆) * s ^ 2
  have hPne : P ≠ 0 := hno r s hs
  have hP0 : Polynomial.aeval x P = 0 := by
    have hmap : Polynomial.aeval x P
        = (Polynomial.aeval x r) ^ 2
            + (algebraMap F Ω b₁ * x + algebraMap F Ω b₃) * Polynomial.aeval x r
                * Polynomial.aeval x s
          - (x ^ 3 + algebraMap F Ω b₂ * x ^ 2 + algebraMap F Ω b₄ * x + algebraMap F Ω b₆)
              * (Polynomial.aeval x s) ^ 2 := by
      simp only [P, map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [hmap, key]
  exact hPne (hx' P hP0)

end Work.MotV5
