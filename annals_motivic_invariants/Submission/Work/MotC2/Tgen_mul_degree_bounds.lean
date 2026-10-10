import Mathlib
import Submission.Work.MotC2.PoleTgen

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

theorem Tgen_mul_degree_bounds (L : Type*) [Field L] (E : WeierstrassCurve L)
    (P₁ Q₁ P₁' Q₁' P₂ Q₂ P₂' Q₂' : Polynomial L)
    (d₁ : P₁.degree ≤ Q₁.degree) (d₁' : P₁'.degree ≤ Q₁'.degree)
    (d₂ : P₂.degree ≤ Q₂.degree) (d₂' : P₂'.degree ≤ Q₂'.degree) :
    (P₁ * P₂ * (Q₁' * Q₂' * Polynomial.X ^ 4) +
        P₁' * P₂' * Work.MotC2.cubicPoly E * (Q₁ * Q₂)).degree ≤
      (Q₁ * Q₂ * (Q₁' * Q₂' * Polynomial.X ^ 4)).degree ∧
    (P₁ * P₂' * (Q₂ * Q₁' * Polynomial.X ^ 2) +
        P₂ * P₁' * (Q₁ * Q₂' * Polynomial.X ^ 2) -
        P₁' * P₂' * Work.MotC2.linPoly E * (Q₁ * Q₂)).degree ≤
      (Q₁ * Q₂ * (Q₁' * Q₂' * Polynomial.X ^ 2)).degree := by
  -- `cubicPoly E` has degree `3 ≤ 4` and `linPoly E` has degree `≤ 1 ≤ 2`.
  have hc : (Work.MotC2.cubicPoly E).degree ≤ (Polynomial.X ^ 4 : Polynomial L).degree := by
    rw [Work.MotC2.cubicPoly_degree, Polynomial.degree_X_pow]; norm_num
  have hl : (Work.MotC2.linPoly E).degree ≤ (Polynomial.X ^ 2 : Polynomial L).degree := by
    refine le_trans (Work.MotC2.linPoly_degree_le E) ?_
    rw [Polynomial.degree_X_pow]; norm_num
  constructor
  · -- `deg(P₁P₂) ≤ deg(Q₁Q₂)`, the numerator of the second summand has degree at most that of
    -- `Q₁'Q₂'X⁴` (via `deg cubicPoly ≤ 3 ≤ 4`).
    refine le_trans (Polynomial.degree_add_le _ _) (max_le ?_ ?_)
    · exact Work.MotC2.degree_mul_le_mul (Work.MotC2.degree_mul_le_mul d₁ d₂) le_rfl
    · rw [mul_comm (P₁' * P₂' * Work.MotC2.cubicPoly E) (Q₁ * Q₂)]
      refine Work.MotC2.degree_mul_le_mul le_rfl ?_
      exact le_trans (Work.MotC2.degree_mul_le_mul (Work.MotC2.degree_mul_le_mul d₁' d₂') hc)
        le_rfl
  · -- Reorder every summand as `(numerator) * (denominator)` matching
    -- `(Q₁ * Q₂) * (Q₂' * Q₁' * X²)`, then compare degrees factor by factor.
    rw [show Q₁ * Q₂ * (Q₁' * Q₂' * Polynomial.X ^ 2) =
          (Q₁ * Q₂) * (Q₂' * Q₁' * Polynomial.X ^ 2) by ring,
        show P₁ * P₂' * (Q₂ * Q₁' * Polynomial.X ^ 2) =
          (P₁ * Q₂) * (P₂' * Q₁' * Polynomial.X ^ 2) by ring,
        show P₂ * P₁' * (Q₁ * Q₂' * Polynomial.X ^ 2) =
          (Q₁ * P₂) * (P₁' * Q₂' * Polynomial.X ^ 2) by ring,
        show P₁' * P₂' * Work.MotC2.linPoly E * (Q₁ * Q₂) =
          (Q₁ * Q₂) * (P₁' * P₂' * Work.MotC2.linPoly E) by ring]
    refine le_trans (Polynomial.degree_sub_le _ _)
      (max_le (le_trans (Polynomial.degree_add_le _ _) (max_le ?_ ?_)) ?_)
    · exact Work.MotC2.degree_mul_le_mul (Work.MotC2.degree_mul_le_mul d₁ le_rfl)
        (Work.MotC2.degree_mul_le_mul (Work.MotC2.degree_mul_le_mul d₂' le_rfl) le_rfl)
    · refine Work.MotC2.degree_mul_le_mul (Work.MotC2.degree_mul_le_mul le_rfl d₂) ?_
      rw [show P₁' * Q₂' * Polynomial.X ^ 2 = Q₂' * P₁' * Polynomial.X ^ 2 by ring]
      exact Work.MotC2.degree_mul_le_mul (Work.MotC2.degree_mul_le_mul le_rfl d₁') le_rfl
    · refine Work.MotC2.degree_mul_le_mul le_rfl ?_
      rw [show Q₂' * Q₁' * Polynomial.X ^ 2 = Q₁' * Q₂' * Polynomial.X ^ 2 by ring]
      exact le_trans (Work.MotC2.degree_mul_le_mul (Work.MotC2.degree_mul_le_mul d₁' d₂') hl)
        le_rfl

end Work.MotC2
