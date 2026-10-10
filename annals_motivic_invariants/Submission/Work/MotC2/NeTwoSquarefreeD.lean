import Mathlib
import Submission.Work.MotC2.NeTwoSquarefreeCubic
import Submission.Work.MotC2.Negation
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.EllipticCharTwoNonsingular
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

open Polynomial

variable {L : Type*} [Field L]

/-! ## Degrees of the two coefficient polynomials

`cubCoef E = X³ + a₂X² + a₄X + a₆` is a cubic, and `linCoef E = a₁X + a₃` has degree `≤ 1`; hence
`linCoef E ^ 2` has degree `≤ 2` and `4 * cubCoef E` is a cubic with leading coefficient
`4 ≠ 0` as soon as `(2 : L) ≠ 0`. -/

/-- The coefficient polynomial `cubCoef E = X³ + a₂X² + a₄X + a₆` is a cubic. -/
lemma NeTwoSquarefreeD_cubCoef_natDegree (E : WeierstrassCurve L) :
    (cubCoef E).natDegree = 3 := by
  refine le_antisymm ?_ ?_
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    have hm3 : ¬ (m = 3) := by omega
    have hm2 : ¬ (m = 2) := by omega
    have hm1 : ¬ (m = 1) := by omega
    have hm0 : ¬ (m = 0) := by omega
    simp only [cubCoef, Polynomial.coeff_add, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
    rw [ite_eq_right hm3, ite_eq_right hm2, ite_eq_right hm1, ite_eq_right hm0]
    simp
  · refine Polynomial.le_natDegree_of_ne_zero ?_
    simp [cubCoef]

/-- The coefficient polynomial `linCoef E = a₁X + a₃` has degree `≤ 1`. -/
lemma NeTwoSquarefreeD_linCoef_natDegree_le (E : WeierstrassCurve L) :
    (linCoef E).natDegree ≤ 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  have hm1 : ¬ (m = 1) := by omega
  have hm0 : ¬ (m = 0) := by omega
  simp only [linCoef, Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
  rw [ite_eq_right hm1, ite_eq_right hm0]
  simp

/-- `linCoef E ^ 2` has degree `≤ 2`. -/
lemma NeTwoSquarefreeD_linCoef_sq_natDegree_le (E : WeierstrassCurve L) :
    (linCoef E ^ 2 : L[X]).natDegree ≤ 2 := by
  rw [Polynomial.natDegree_pow]
  have := NeTwoSquarefreeD_linCoef_natDegree_le E
  omega

/-- `4 * cubCoef E` is a cubic: its leading coefficient `4` is nonzero as soon as `(2 : L) ≠ 0`. -/
lemma NeTwoSquarefreeD_four_mul_cubCoef_natDegree (E : WeierstrassCurve L) (h2 : (2 : L) ≠ 0) :
    (4 * cubCoef E : L[X]).natDegree = 3 := by
  have h4 : (4 : L) ≠ 0 := by
    have : (4 : L) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hC4 : (4 : L[X]) = Polynomial.C (4 : L) :=
    (Polynomial.C_eq_natCast (R := L) 4).symm
  rw [hC4, Polynomial.natDegree_C_mul h4, NeTwoSquarefreeD_cubCoef_natDegree E]

/-- `D = linCoef E ^ 2 + 4 * cubCoef E` is a cubic when `(2 : L) ≠ 0`. -/
lemma NeTwoSquarefreeD_natDegree (E : WeierstrassCurve L) (h2 : (2 : L) ≠ 0) :
    (linCoef E ^ 2 + 4 * cubCoef E).natDegree = 3 := by
  have hlin := NeTwoSquarefreeD_linCoef_sq_natDegree_le E
  have h4cub := NeTwoSquarefreeD_four_mul_cubCoef_natDegree E h2
  rw [add_comm, Polynomial.natDegree_add_eq_left_of_natDegree_lt (by omega)]
  exact h4cub

/-! ## `D` has no double root

Since `D = (a₁X + a₃)² + 4(X³ + a₂X² + a₄X + a₆)`, a double root `α` of `D` would give a point
`(α, β)` with `β := -(a₁α + a₃)/2` solving the Weierstrass equation while both affine partial
derivatives vanish there, contradicting the nonsingularity of the elliptic curve `E`. -/

/-- `D = linCoef E ^ 2 + 4 * cubCoef E` has no double root when `E` is elliptic and
`(2 : L) ≠ 0`. -/
lemma NeTwoSquarefreeD_noDoubleRoot (E : WeierstrassCurve L) [E.IsElliptic] (h2 : (2 : L) ≠ 0)
    (α : L) :
    ¬ ((linCoef E ^ 2 + 4 * cubCoef E).eval α = 0 ∧
      (linCoef E ^ 2 + 4 * cubCoef E).derivative.eval α = 0) := by
  rintro ⟨h0, h1⟩
  -- `4 ≠ 0`
  have h4 : (4 : L) ≠ 0 := by
    have : (4 : L) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  -- `D.eval α = 0` unfolded
  have h0' : (E.a₁ * α + E.a₃) ^ 2 + 4 * (α ^ 3 + E.a₂ * α ^ 2 + E.a₄ * α + E.a₆) = 0 := by
    have := h0
    simp only [linCoef, cubCoef, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_ofNat] at this
    ring_nf at this ⊢
    exact this
  -- `D.derivative.eval α = 0` unfolded
  have h1' : 2 * (E.a₁ * α + E.a₃) * E.a₁ + 4 * (3 * α ^ 2 + 2 * E.a₂ * α + E.a₄) = 0 := by
    have := h1
    simp only [linCoef, cubCoef, Polynomial.derivative_add, Polynomial.derivative_mul,
      Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X,
      Polynomial.derivative_ofNat, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_ofNat, Polynomial.eval_zero,
      Polynomial.eval_one] at this
    ring_nf at this ⊢
    exact this
  -- the would-be `y`-coordinate of a double point
  set β : L := -(E.a₁ * α + E.a₃) / 2 with hβ
  have hβ2β : 2 * β + (E.a₁ * α + E.a₃) = 0 := by
    rw [hβ]; field_simp; ring
  -- the `X`-partial `a₁β - (3α² + 2a₂α + a₄)` vanishes
  have haβ : E.a₁ * β = 3 * α ^ 2 + 2 * E.a₂ * α + E.a₄ := by
    have key : 4 * (E.a₁ * β - (3 * α ^ 2 + 2 * E.a₂ * α + E.a₄)) = 0 := by
      linear_combination (norm := first | refl_ring1 | ring1) (2 * E.a₁) * hβ2β - h1'
    have hz : E.a₁ * β - (3 * α ^ 2 + 2 * E.a₂ * α + E.a₄) = 0 := by
      rcases mul_eq_zero.mp key with h | h
      · exact absurd h h4
      · exact h
    linear_combination (norm := first | refl_ring1 | ring1) hz
  -- and `(α, β)` satisfies the Weierstrass equation
  have heq : WeierstrassCurve.Affine.Equation E α β := by
    rw [WeierstrassCurve.Affine.equation_iff]
    have key : 4 * (β ^ 2 + E.a₁ * α * β + E.a₃ * β -
        (α ^ 3 + E.a₂ * α ^ 2 + E.a₄ * α + E.a₆)) = 0 := by
      linear_combination (norm := first | refl_ring1 | ring1) -h0' + (2 * β + (E.a₁ * α + E.a₃)) * hβ2β
    have hz : β ^ 2 + E.a₁ * α * β + E.a₃ * β -
        (α ^ 3 + E.a₂ * α ^ 2 + E.a₄ * α + E.a₆) = 0 := by
      rcases mul_eq_zero.mp key with h | h
      · exact absurd h h4
      · exact h
    linear_combination (norm := first | refl_ring1 | ring1) hz
  -- so `(α, β)` would be a singular point of the elliptic curve
  have hns := (WeierstrassCurve.Affine.equation_iff_nonsingular).mp heq
  rw [WeierstrassCurve.Affine.nonsingular_iff] at hns
  rcases hns with ⟨-, h | h⟩
  · exact h haβ
  · exact h (by linear_combination hβ2β)

/-- **The 2-torsion cubic is squarefree when `E` is elliptic and `2 ≠ 0`.**  Here
`D := Work.MotC2.linCoef E ^ 2 + 4 * Work.MotC2.cubCoef E` with `linCoef E = a₁X + a₃` and
`cubCoef E = X³ + a₂X² + a₄X + a₆` (definitions in `Submission.Work.MotC2.Negation`); `D` has
leading coefficient `4 ≠ 0`, so `natDegree D = 3` because `(2 : L) ≠ 0`.  Route: use
`Work.MotC2.NeTwoSquarefreeCubic` (module `Submission.Work.MotC2.NeTwoSquarefreeCubic`); it remains
to show `natDegree D = 3` (since `linCoef E ^ 2` has degree `≤ 2`, `Polynomial.natDegree_add_eq_left_of_natDegree_lt`)
and that `D` has no double root: if `D.eval α = 0` and `D.derivative.eval α = 0`, set
`β := -(E.a₁ * α + E.a₃) / 2`; then `WeierstrassCurve.Affine.Equation E α β` holds (this is
`D.eval α = 0` rewritten) while `E.polynomialY` and `E.polynomialX` both vanish at `(α, β)` (the
second is `D.derivative.eval α = 0` rewritten), contradicting
`WeierstrassCurve.Affine.equation_iff_nonsingular` for `E.IsElliptic`.  The file
`Submission.Work.MotC2.EllipticCharTwoNonsingular` is the exact char-2 analogue of this last step
and can be imitated.  Do not import `Submission.Work.MotC2.NeTwoNoDoubleRoot`: it is still a
`sorry`. -/
theorem NeTwoSquarefreeD (L : Type*) [Field L] (E : WeierstrassCurve L) [E.IsElliptic]
    (h2 : (2 : L) ≠ 0) : Squarefree (Work.MotC2.linCoef E ^ 2 + 4 * Work.MotC2.cubCoef E) := by
  exact NeTwoSquarefreeCubic (Work.MotC2.linCoef E ^ 2 + 4 * Work.MotC2.cubCoef E)
    (NeTwoSquarefreeD_natDegree E h2) (NeTwoSquarefreeD_noDoubleRoot E h2)

end Work.MotC2
