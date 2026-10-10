import Mathlib
import Submission.Work.MotTDG.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# TDG, the two ring leaves (**TDG-b**, **TDG-c**)

Both are pure commutative-algebra identities, stated for an arbitrary commutative ring `R`
(hence valid in every `𝕜`-algebra by specialisation).  They are the algebraic core of the
reduction of a Pfaffian along a matrix to the five Veronese--Weierstrass quadrics:

* `kleinP_mulVec_expand` (**TDG-b**): expanding the quadratic form `v ↦ p_k (c·v)` gives the
  diagonal part `∑_m colP k m * v_m²` and the polar part `∑_{m<n} colB k m n * v_m v_n`.
* `quad_reduce` (**TDG-c**): any such quadratic form is the sum of a combination of the five
  `vwQuad` and a combination of the ten `goodMon`.

The `μ`-coefficients that multiply the `vwQuad` are `muVW`; the remainder coefficients are `rhoVW`.
Node **TDG-d** shows that `rhoVW = 0` for a genuine Klein datum.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotTDG
noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine

/-- **TDG-b**: expansion of a Pfaffian along a matrix: `p_k (c · v)` is the quadratic form with
diagonal coefficients `colP` and polar coefficients `colB`. -/
theorem kleinP_mulVec_expand {R : Type*} [CommRing R] (a b : R) (c : Fin 5 → Fin 5 → R)
    (v : Fin 5 → R) (k : Fin 5) :
    Work.MotK.kleinP a b (fun i => ∑ m, c i m * v m) k =
      ∑ m, colP a b c k m * v m ^ 2 +
        ∑ m, ∑ n, (if m < n then colB a b c k m n * v m * v n else 0) := by
  simp only [colP, colB, kleinPolar, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp (config := {decide := true}) only [Fin.lt_iff_val_lt_val, Fin.val_succ, Fin.val_zero,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  norm_num
  fin_cases k <;>
    simp [Work.MotK.kleinP, Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2,
      Work.MotK.kleinP3, Work.MotK.kleinP4, Fin.sum_univ_succ] <;> ring

/-- **TDG-c**: the reduction identity.  The generic quadratic form `quadForm P B` is a combination
of the five Veronese--Weierstrass quadrics `vwQuad` and the ten good monomials `goodMon`. -/
theorem quad_reduce {R : Type*} [CommRing R] (a₁ a₂ a₃ a₄ a₆ : R) (P : Fin 5 → R)
    (B : Fin 5 → Fin 5 → R) (v : Fin 5 → R) :
    quadForm P B v =
      ∑ j, muVW a₁ P B j * vwQuad a₁ a₂ a₃ a₄ a₆ v j +
        ∑ t, rhoVW a₁ a₂ a₃ a₄ a₆ P B t * goodMon v t := by
  simp only [quadForm, Fin.sum_univ_succ, Fin.sum_univ_zero, muVW, rhoVW, vwQuad, goodMon]
  simp (config := {decide := true}) only [Fin.lt_iff_val_lt_val, Fin.val_succ, Fin.val_zero,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, Matrix.head_cons]
  norm_num
  first | refl_ring1 | ring

end

end Work.MotTDG
