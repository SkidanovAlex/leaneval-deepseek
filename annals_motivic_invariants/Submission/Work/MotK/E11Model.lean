import Mathlib
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.E11Model`

The explicit Klein (Fisher) model `D = kleinDataCandidate 𝕜` of the Tate normal form
`E₁₁ : y² - 10xy - 11y = x³ - 11x²` (`b = 11`), together with its integral Klein coordinate
matrix `kleinCoordInt`.

**The data (verified symbolically over ℚ; valid in every characteristic `≠ 2, 3, 5, 11`):**

* `E : y² - 10·x·y - 11·y = x³ - 11·x²` — the Tate normal form `E_b` with `b = 11`
  (`a₁ = -10`, `a₂ = a₃ = -11`, `a₄ = a₆ = 0`), whose point `T = (0,0)` has order `5`.
  `j = -2^12·31^3/11^5 = -122023936/161051 ≠ 0, 1728`; the discriminant is `-11^5`
  (`Δ = b⁵(b²-11b-1)` with `b = 11`), so the curve is smooth exactly when `char ≠ 11`.
* Klein parameters `(a, b) = (1, 1)`.
* `coord` (rows = `κ_0,…,κ_4` in the basis `1, x, y, x², xy`):

  ```
  κ_0 =               121 + 55x        +  5x²
  κ_1 =      -55x + 11y  -  6x² + xy
  κ_2 = -121 - 33x       -  7x² + xy
  κ_3 = -121 - 22x       +  3x² - xy
  κ_4 =  121 + 66x - 11y +  4x² - xy
  ```

  with `det coord = 11^5 = 161051`.

**The `5`-torsion point of `T_diag`.**  For a primitive `5`-th root of unity `ζ` in a field `L`
of characteristic `≠ 5`, the point

  `Q(ζ) = ( 11·(ζ² + ζ³ - 2)/5 ,  (77ζ³ + 66ζ² + 33ζ - 66)/5 )`

is a `5`-torsion point of `E₁₁(L)` (it is the point of the χ-line `H = ⟨Q⟩` whose eigenvalues on
the Klein coordinates `κ_i/κ_0` are `ζ^i`), and

  `τ_{Q(ζ)}^*(κ_i/κ_0) = ζ^i · (κ_i/κ_0)`

where `τ_Q^*` is the translation automorphism `Work.MotC2.transAlgEquiv`.  This is verified as a
polynomial identity modulo `Φ₅(ζ) = ζ⁴+ζ³+ζ²+ζ+1` and the Weierstrass relation
`W = y² - (10x+11)y - x³ + 11x²` with coefficients having denominators `5` only; hence it holds in
every characteristic `≠ 5`.  (See `Submission/Work/MotK/TDiagE11.lean`.)
-/

namespace Work.MotK

/-- The Weierstrass curve `E₁₁ : y² - 10xy - 11y = x³ - 11x²` (Tate normal form `E_b` with
`b = 11`), whose point `(0,0)` has order `5`. -/
def E11 (𝕜 : Type) [CommRing 𝕜] : WeierstrassCurve 𝕜 where
  a₁ := -10
  a₂ := -11
  a₃ := -11
  a₄ := 0
  a₆ := 0

/-- The Klein coordinate matrix for `E₁₁` (rows `κ_0,…,κ_4` in the basis `1, x, y, x², xy`),
given here over `ℤ`; its determinant is `11^5`. -/
def kleinCoordInt : Fin 5 → Fin 5 → ℤ :=
  !![121, 55, 0, 5, 0;
     0, -55, 11, -6, 1;
     -121, -33, 0, -7, 1;
     -121, -22, 0, 3, -1;
     121, 66, -11, 4, -1]

/-- The explicit candidate `Work.MotV.KleinData 𝕜` (valid in every characteristic `∉ {2,3,5,11}`). -/
def kleinDataCandidate (𝕜 : Type) [Field 𝕜] : Work.MotV.KleinData 𝕜 where
  a := 1
  b := 1
  E := E11 𝕜
  coord := fun i j => (kleinCoordInt i j : 𝕜)

end Work.MotK
