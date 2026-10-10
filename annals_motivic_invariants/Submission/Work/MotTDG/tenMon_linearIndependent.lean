import Mathlib
import Submission.Work.MotTDG.Defs
import Submission.Work.MotTDG.TenAux
import Submission.Work.MotTDG.decomp_unique
import Submission.Work.MotTDG.tenP_coeff_eq_zero
import Submission.Work.MotTDG.tenQ_coeff_eq_zero

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotTDG

/-!
**TDG-a**: the ten monomials `1, x, y, x², xy, x³, x²y, x⁴, x³y, x²y²` of `L(10·O)` are
`L`-independent.

`Work.MotTDG.tenMon E = goodMon (basE E)` is the family
`(1, x, y, x², xy, x³, x²y, x⁴, x³y, x²y²)` in `FunctionField E = L(E)`, where
`x = Work.MotV.genX E` and `y = Work.MotV.genY E`.  This is the only input of the whole TDG node:
it is used to prove that the reduction remainders `rhoVW` of `quad_reduce` vanish (node TDG-d,
`Submission/Work/MotTDG/Rho`) and, through TDG-d, that the multiplier matrix `muMat` is invertible
(node TDG-e, `Submission/Work/MotTDG/Mu`).  No hypothesis on `E` is needed: the Weierstrass
polynomial `Y² + (a₁X+a₃)Y - (X³+a₂X²+a₄X+a₆)` is irreducible over `L[X]` for *every* Weierstrass
curve (its `X`-degree is odd), so `L[E]` is a domain and `1, y` is an `L[X]`-basis.

PROOF ROUTE (`Submission/Work/MotTDG/Defs.lean` holds the vocabulary, the `@[simp]` results
`tenMon_zero` … `tenMon_nine`, and `Work.MotTDG.genXY_relation`):

* Step 1.  Work in `A = WeierstrassCurve.Affine.CoordinateRing E` with
  `xA = CoordinateRing.mk E (Polynomial.C Polynomial.X)` (`Work.MotC2.coordX_eq_mk` identifies it
  with `Work.MotC2.coordX E`) and `yA = CoordinateRing.mk E Polynomial.X` (= `coordY E`).  The ten
  elements of `A` are `tenMonA = (1, xA, yA, xA², xA·yA, xA³, xA²yA, xA⁴, xA³yA, xA²yA²)`.  Since
  `algebraMap A (FunctionField E) (tenMonA i) = Work.MotTDG.tenMon E i` and `algebraMap` is
  injective (`IsFractionRing.injective`; `CoordinateRing E` is a domain by the instance
  `WeierstrassCurve.Affine.CoordinateRing.instIsDomainCoordinateRing` in
  `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`), it suffices to prove the independence
  in `A`.
* Step 2.  Every element of `A` is `p(xA) + q(xA)·yA` with `p, q ∈ L[X]`
  (`CoordinateRing.exists_smul_basis_eq` plus `CoordinateRing.smul`); conversely
  `CoordinateRing.smul_basis_eq_zero` says: `p(xA) + q(xA)·yA = 0` implies `p = q = 0`.
* Step 3.  Apply Step 2 to `∑ i, c i • tenMonA i = 0`.  The `x`-parts of the ten elements are
  `1, X, 0, X², 0, X³, 0, X⁴, 0, X⁵+a₂X⁴+a₄X³+a₆X²` and the `y`-parts are
  `0, 0, 1, 0, X, 0, X², 0, X³, -(a₁X³+a₃X²)`; the last one uses the relation in `A`
  `yA² = xA³ + a₂xA² + a₄xA + a₆ - (a₁xA + a₃)yA` (`Work.MotC2.coord_relation`), multiplied by
  `xA²`, to rewrite `xA²yA²`.  (`CoordinateRing.smul_basis_mul_C` and
  `CoordinateRing.smul_basis_mul_Y` are the relevant rewriting API.)
* Step 4.  Comparing coefficients in the two polynomial identities
  `∑ c i · (x-part i) = 0` and `∑ c i · (y-part i) = 0` (Mathlib: `Polynomial.funext`,
  `Polynomial.coeff_X_pow`, `Finset.sum_eq_single`) yields, in the order `c 0, c 1, c 9, c 3,
  c 5, c 7` from the `x`-parts (the `X⁵`-coefficient is `c 9`) and then `c 2, c 4, c 6, c 8` from
  the `y`-parts, that every `c i = 0`.
* Step 5.  Conclude with `Fintype.linearIndependent_iff`.

A legal alternative to Steps 3–4 is to prove the statement on the ten specific elements of `L(E)`
directly, by induction on the pole order at the point at infinity.
-/

theorem tenMon_linearIndependent {L : Type*} [Field L] (E : WeierstrassCurve L) :
    LinearIndependent L (tenMon E) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- Normal form of the linear combination, using `y² = x³ + a₂x² + a₄x + a₆ - (a₁x + a₃)y`.
  have hexp := tenMon_expansion (L := L) (R := WeierstrassCurve.Affine.FunctionField E)
    E.a₁ E.a₂ E.a₃ E.a₄ E.a₆ (Work.MotV.genX E) (Work.MotV.genY E) c (genXY_relation E)
  have hzero : Polynomial.aeval (Work.MotV.genX E) (tenP E.a₂ E.a₄ E.a₆ c)
      + Polynomial.aeval (Work.MotV.genX E) (tenQ E.a₁ E.a₃ c) * Work.MotV.genY E = 0 := by
    rw [← hexp]
    simpa only [tenMon, basE] using hc
  -- `1, y` are linearly independent over `L[x]`, so both parts vanish.
  obtain ⟨hP, hQ⟩ := decomp_unique E hzero
  -- Coefficient extraction.
  obtain ⟨h0, h1, h3, h5, h7, h9⟩ := tenP_coeff_eq_zero E.a₂ E.a₄ E.a₆ c hP
  obtain ⟨h2, h4, h6, h8⟩ := tenQ_coeff_eq_zero E.a₁ E.a₃ c hQ
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · simpa [h9] using h6
  · exact h7
  · simpa [h9] using h8
  · exact h9

end Work.MotTDG
