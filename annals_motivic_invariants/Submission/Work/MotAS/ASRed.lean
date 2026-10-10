import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The reduction algebra `𝔽₅[w]/(w⁵ - w - g)` on five coefficient vectors

Part of the subproject `Submission/Work/MotAS` (`Work.MotAS`).  In the Artin–Schreier Galois
coordinates `x_i = Σ_j y_j (w+i)^j` of `MOTIVIC_KDATA_LEAD.md` §6, the *reduced* (i.e. `w`-free)
form of a polynomial in `w` is obtained by writing it in the basis `1, w, w², w³, w⁴` of
`R[w]/(w⁵ - w - g)`.

`redMul g P Q` is the multiplication in that algebra, written on coefficient vectors of length `5`:
it is the *explicit* formula for `(Σ_l P_l w^l)(Σ_m Q_m w^m)` reduced with `w⁵ = w + g`.  The key
identity is `redMul_spec`, which makes it possible to reduce a product of `w`-polynomials one
factor at a time — this is what keeps the Lean computation of the transported secant quintics
(`asTransportS`, `asTransportSD`) small: expanding the substitution `x_i = Σ_j y_j (w+i)^j`
directly explodes, whereas the staged reduction never leaves degree `≤ 4` in `w`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotAS

variable {R : Type*} [CommRing R]

/-- The coefficient vector of `1` in the basis `1, w, w², w³, w⁴`. -/
def oneVec : Fin 5 → R := ![1, 0, 0, 0, 0]

/-- **Multiplication in `R[w]/(w⁵ - w - g)` on coefficient vectors.**  The `l`-th entry of
`redMul g P Q` is the coefficient of `w^l` in `(Σ_l P_l w^l)·(Σ_m Q_m w^m)` after the reduction
`w⁵ = w + g` (and hence `w⁶ = w² + gw`, `w⁷ = w³ + gw²`, `w⁸ = w⁴ + gw³`). -/
def redMul (g : R) (P Q : Fin 5 → R) : Fin 5 → R :=
  ![ P 0*Q 0 + g*(P 1*Q 4 + P 2*Q 3 + P 3*Q 2 + P 4*Q 1),
     P 0*Q 1 + P 1*Q 0 + (P 1*Q 4 + P 2*Q 3 + P 3*Q 2 + P 4*Q 1) + g*(P 2*Q 4 + P 3*Q 3 + P 4*Q 2),
     P 0*Q 2 + P 1*Q 1 + P 2*Q 0 + (P 2*Q 4 + P 3*Q 3 + P 4*Q 2) + g*(P 3*Q 4 + P 4*Q 3),
     P 0*Q 3 + P 1*Q 2 + P 2*Q 1 + P 3*Q 0 + (P 3*Q 4 + P 4*Q 3) + g*(P 4*Q 4),
     P 0*Q 4 + P 1*Q 3 + P 2*Q 2 + P 3*Q 1 + P 4*Q 0 + P 4*Q 4 ]

/-- **The reduction identity.**  `redMul g P Q` computes the product of `Σ_l P_l w^l` and
`Σ_m Q_m w^m` in `R[w]/(w⁵ - w - g)`. -/
theorem redMul_spec (g w : R) (hw : w ^ 5 = w + g) (P Q : Fin 5 → R) :
    (∑ l, P l * w ^ (l : ℕ)) * (∑ l, Q l * w ^ (l : ℕ)) =
      ∑ l, redMul g P Q l * w ^ (l : ℕ) := by
  have h1 : (∑ l : Fin 5, P l * w ^ (l : ℕ))
      = P 0 * w ^ 0 + P 1 * w ^ 1 + P 2 * w ^ 2 + P 3 * w ^ 3 + P 4 * w ^ 4 := by
    simp [Fin.sum_univ_five]
  have h2 : (∑ l : Fin 5, Q l * w ^ (l : ℕ))
      = Q 0 * w ^ 0 + Q 1 * w ^ 1 + Q 2 * w ^ 2 + Q 3 * w ^ 3 + Q 4 * w ^ 4 := by
    simp [Fin.sum_univ_five]
  have h3 : (∑ l : Fin 5, redMul g P Q l * w ^ (l : ℕ))
      = redMul g P Q 0 * w ^ 0 + redMul g P Q 1 * w ^ 1 + redMul g P Q 2 * w ^ 2
        + redMul g P Q 3 * w ^ 3 + redMul g P Q 4 * w ^ 4 := by
    simp [Fin.sum_univ_five]
  rw [h1, h2, h3]
  simp only [redMul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  have h6 : w ^ 6 = w ^ 2 + g * w := by
    have h : w ^ 6 = w ^ 5 * w := by ring
    rw [h, hw]; ring
  have h7 : w ^ 7 = w ^ 3 + g * w ^ 2 := by
    have h : w ^ 7 = w ^ 6 * w := by ring
    rw [h, h6]; ring
  have h8 : w ^ 8 = w ^ 4 + g * w ^ 3 := by
    have h : w ^ 8 = w ^ 7 * w := by ring
    rw [h, h7]; ring
  conv_lhs => ring_nf
  rw [hw, h6, h7, h8]
  first | refl_ring1 | ring

end Work.MotAS
