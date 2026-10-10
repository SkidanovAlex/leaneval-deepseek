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
# TDG-a, auxiliary: the normal form of the ten monomials

This file holds the two polynomials in which the ten monomials `1, x, y, x², xy, x³, x²y, x⁴, x³y,
x²y²` are written, using the Weierstrass relation `y² = x³ + a₂x² + a₄x + a₆ − (a₁x + a₃)y` to
reduce the last monomial `x²y²`:

* `tenP a₂ a₄ a₆ c` is the `x`-part,
* `tenQ a₁ a₃ c` is the `y`-part,

so that `∑ᵢ cᵢ · (ten monomials)ᵢ = P(x) + Q(x)·y` for *any* `x, y` satisfying the Weierstrass
relation (`tenMon_expansion`).  The names match `Submission/Work/MotTDG/tenMon_linearIndependent`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Work.MotTDG
noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine

/-- The `x`-part `c₀ + c₁X + c₃X² + c₅X³ + c₇X⁴ + c₉(X⁵ + a₂X⁴ + a₄X³ + a₆X²)` of the normal
form of `∑ᵢ cᵢ · (ten monomials)ᵢ`. -/
def tenP {L : Type*} [Field L] (a₂ a₄ a₆ : L) (c : Fin 10 → L) : Polynomial L :=
  Polynomial.C (c 0) + Polynomial.C (c 1) * Polynomial.X + Polynomial.C (c 3) * Polynomial.X ^ 2
    + Polynomial.C (c 5) * Polynomial.X ^ 3 + Polynomial.C (c 7) * Polynomial.X ^ 4
    + Polynomial.C (c 9) * (Polynomial.X ^ 5 + Polynomial.C a₂ * Polynomial.X ^ 4
        + Polynomial.C a₄ * Polynomial.X ^ 3 + Polynomial.C a₆ * Polynomial.X ^ 2)

/-- The `y`-part `c₂ + c₄X + c₆X² + c₈X³ − c₉(a₁X³ + a₃X²)` of the normal form of
`∑ᵢ cᵢ · (ten monomials)ᵢ`. -/
def tenQ {L : Type*} [Field L] (a₁ a₃ : L) (c : Fin 10 → L) : Polynomial L :=
  Polynomial.C (c 2) + Polynomial.C (c 4) * Polynomial.X + Polynomial.C (c 6) * Polynomial.X ^ 2
    + Polynomial.C (c 8) * Polynomial.X ^ 3
    - Polynomial.C (c 9) * (Polynomial.C a₁ * Polynomial.X ^ 3 + Polynomial.C a₃ * Polynomial.X ^ 2)

/-- **The normal form of the ten monomials.**  For any `x, y` satisfying the Weierstrass relation
in an `L`-algebra `R`, the linear combination `∑ᵢ cᵢ · (1, x, y, x², xy, x³, x²y, x⁴, x³y, x²y²)ᵢ`
equals `P(x) + Q(x)·y` with `P = tenP …`, `Q = tenQ …`.  The only relation used is
`x²y² = x²(x³ + a₂x² + a₄x + a₆) − x²(a₁x + a₃)y`. -/
theorem tenMon_expansion {L : Type*} [Field L] {R : Type*} [CommRing R] [Algebra L R]
    (a₁ a₂ a₃ a₄ a₆ : L) (x y : R) (c : Fin 10 → L)
    (h : y ^ 2 + algebraMap L R a₁ * x * y + algebraMap L R a₃ * y =
        x ^ 3 + algebraMap L R a₂ * x ^ 2 + algebraMap L R a₄ * x + algebraMap L R a₆) :
    (∑ i : Fin 10, c i • goodMon ![1, x, y, x ^ 2, x * y] i) =
      Polynomial.aeval x (tenP a₂ a₄ a₆ c) + Polynomial.aeval x (tenQ a₁ a₃ c) * y := by
  unfold tenP tenQ
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, goodMon, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_succ, Matrix.cons_val]
  norm_num
  simp only [Algebra.smul_def]
  ring_nf
  linear_combination (norm := first | refl_ring1 | ring1) (algebraMap L R (c 9) * x ^ 2) * h

/-- `goodMon` commutes with any ring homomorphism. -/
theorem map_goodMon {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (v : Fin 5 → R)
    (i : Fin 10) : f (goodMon v i) = goodMon (fun m => f (v m)) i := by
  fin_cases i <;> simp [goodMon]

end

end Work.MotTDG
