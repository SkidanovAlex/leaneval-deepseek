import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotK.KleinData
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.TranslationDefs
import Submission.Work.MotV5.adjoin_genX_genY
import Submission.Work.MotV5.transcendental_of_isAlgebraic_adjoin_simple
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Klein data in characteristic 5, at the Klein parameter `(u : 1) = (1 : 1)`

We exhibit, over every field `𝕜` of characteristic `5`, explicit Klein data
(`Work.MotV.KleinData`) satisfying the nondegeneracy conditions of the Artin–Schreier
branch (`Work.MotV5.KleinData.ASGood`).

The curve is `E : y² - y = x³ - x²` (the Tate normal form with parameter `1`, i.e. `11a3`,
which is isomorphic to the Klein quintic `C_{1,1} ⊂ ℙ⁴`), and the five Klein coordinates are
the explicit linear forms in the basis `1, x, y, x², xy` of `L(5·O)` listed in `C11`.

The data were found by a finite computation with the coordinate ring `𝔽₅[x,y]/(y²-y-x³+x²)`;
the identities used below are elementary polynomial identities over `ℤ` together with the
single fact `5 = 0`.

## Contents

* `E11`, `C11`, `C11inv`, `C11invE`, `D11` — the data (`D11` is an `abbrev` so that its field
  projection `(D11 𝕜).E` unfolds definitionally to `E11 𝕜`);
* `q0_id` … `q4_id`, `rel_id`, `bas_id`, `x_bas_id`, `y_bas_id` — the polynomial identities over
  `ℤ`, proved by `ring`;
* `kleinCoord_zero` … `kleinCoord_four`, `spans11` — the Klein coordinates as explicit elements;
* `generates11` — the Klein ratios generate the function field (via `adjoin_genX_genY`);
* `transcendental_kappa4` — `κ₄/κ₀` is transcendental (via the explicit relation and
  `transcendental_of_isAlgebraic_adjoin_simple`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotV5

open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

/-! ## §1 The data -/

/-- The elliptic curve `y² - y = x³ - x²` over `𝕜` (Tate normal form, parameter `1`). -/
def E11 (𝕜 : Type) [CommRing 𝕜] : WeierstrassCurve 𝕜 where
  a₁ := 0
  a₂ := 4
  a₃ := 4
  a₄ := 0
  a₆ := 0

/-- The Klein coordinates `κ_i` of `E_{1,1}` in the basis `1, x, y, x², xy`. -/
def C11 (𝕜 : Type) [CommRing 𝕜] : Fin 5 → Fin 5 → 𝕜 :=
  ![![1, 0, 0, 0, 0], ![1, 1, 4, 4, 4], ![4, 3, 0, 3, 4], ![4, 2, 0, 3, 1],
    ![0, 0, 1, 4, 1]]

/-- The inverse of `C11`. -/
def C11inv (𝕜 : Type) [CommRing 𝕜] : Fin 5 → Fin 5 → 𝕜 :=
  ![![1, 0, 0, 0, 0], ![3, 1, 2, 2, 1], ![3, 2, 3, 2, 3], ![2, 0, 1, 1, 0],
    ![4, 3, 3, 4, 3]]

/-- The integer error table of `C11inv * C11 = 1 + 5 * C11invE`. -/
def C11invE : Fin 5 → Fin 5 → ℕ :=
  ![![0, 0, 0, 0, 0], ![4, 2, 1, 4, 3], ![5, 3, 2, 7, 5], ![2, 1, 0, 1, 1], ![7, 4, 3, 9, 6]]

/-- The explicit Klein data over `𝕜` with Klein parameters `a = b = 1`.  It is an `abbrev` so
that the projection `(D11 𝕜).E` unfolds definitionally (and hence also during type class
synthesis) to `E11 𝕜`. -/
abbrev D11 (𝕜 : Type) [Field 𝕜] : Work.MotV.KleinData 𝕜 :=
  { a := 1, b := 1, E := E11 𝕜, coord := C11 𝕜 }

/-! ## §2 The five Pfaffian identities and the relation, over `ℤ` -/

/-- `κ_0 = 1` as a polynomial. -/
def kp0 {R : Type*} [CommRing R] (x y : R) : R := (1)

/-- `κ_1 = 1 + 4y + x + 4xy + 4x²` as a polynomial. -/
def kp1 {R : Type*} [CommRing R] (x y : R) : R := (1 + 4 * y + x + 4 * x * y + 4 * x ^ 2)

/-- `κ_2 = 4 + 3x + 4xy + 3x²` as a polynomial. -/
def kp2 {R : Type*} [CommRing R] (x y : R) : R := (4 + 3 * x + 4 * x * y + 3 * x ^ 2)

/-- `κ_3 = 4 + 2x + xy + 3x²` as a polynomial. -/
def kp3 {R : Type*} [CommRing R] (x y : R) : R := (4 + 2 * x + x * y + 3 * x ^ 2)

/-- `κ_4 = y + xy + 4x²` as a polynomial. -/
def kp4 {R : Type*} [CommRing R] (x y : R) : R := (y + x * y + 4 * x ^ 2)

/-- The Weierstrass polynomial `y² - y - x³ + x²`. -/
def Wp {R : Type*} [CommRing R] (x y : R) : R := (y ^ 2 - y - x ^ 3 + x ^ 2)

/-- The first Pfaffian of `κ`. -/
def q0 {R : Type*} [CommRing R] (x y : R) : R :=
  -(kp0 x y) ^ 2 + (kp2 x y) * (kp3 x y) - (kp1 x y) * (kp4 x y)

/-- The second Pfaffian of `κ`. -/
def q1 {R : Type*} [CommRing R] (x y : R) : R :=
  -(kp2 x y) ^ 2 + (kp0 x y) * (kp4 x y) - (kp1 x y) * (kp3 x y)

/-- The third Pfaffian of `κ`. -/
def q2 {R : Type*} [CommRing R] (x y : R) : R :=
  -(kp4 x y) ^ 2 + (kp1 x y) * (kp2 x y) - (kp0 x y) * (kp3 x y)

/-- The fourth Pfaffian of `κ`. -/
def q3 {R : Type*} [CommRing R] (x y : R) : R :=
  -(kp1 x y) ^ 2 + (kp3 x y) * (kp4 x y) - (kp0 x y) * (kp2 x y)

/-- The fifth Pfaffian of `κ`. -/
def q4 {R : Type*} [CommRing R] (x y : R) : R :=
  -(kp3 x y) ^ 2 + (kp0 x y) * (kp1 x y) - (kp2 x y) * (kp4 x y)

/-- Cofactor of the first Pfaffian. -/
def h0 {R : Type*} [CommRing R] (x y : R) : R := ((-4) + (-8) * x)

/-- Error term of the first Pfaffian. -/
def e0 {R : Type*} [CommRing R] (x y : R) : R :=
  (3 + (-1) * y + 4 * x + 2 * x * y + 6 * x ^ 2 + (-2) * x ^ 2 * y + 3 * x ^ 3 + (-1) * x ^ 3 * y +
    (-3) * x ^ 4)

/-- `p₀(κ) = h₀ · W + 5 e₀`. -/
theorem q0_id {R : Type*} [CommRing R] (x y : R) :
    q0 x y = h0 x y * Wp x y + 5 * e0 x y := by
  unfold q0 h0 Wp e0 kp0 kp1 kp2 kp3 kp4
  refl_ring1

/-- Cofactor of the second Pfaffian. -/
def h1 {R : Type*} [CommRing R] (x y : R) : R := ((-4) * x + (-20) * x ^ 2)

/-- Error term of the second Pfaffian. -/
def e1 {R : Type*} [CommRing R] (x y : R) : R :=
  ((-4) + (-3) * y + (-6) * x + (-12) * x * y + (-10) * x ^ 2 + (-13) * x ^ 2 * y + (-5) * x ^ 3 +
    (-8) * x ^ 3 * y + (-1) * x ^ 4 + (-4) * x ^ 5)

/-- `p₁(κ) = h₁ · W + 5 e₁`. -/
theorem q1_id {R : Type*} [CommRing R] (x y : R) :
    q1 x y = h1 x y * Wp x y + 5 * e1 x y := by
  unfold q1 h1 Wp e1 kp0 kp1 kp2 kp3 kp4
  refl_ring1

/-- Cofactor of the third Pfaffian. -/
def h2 {R : Type*} [CommRing R] (x y : R) : R := ((-1) + 14 * x + 15 * x ^ 2)

/-- Error term of the third Pfaffian. -/
def e2 {R : Type*} [CommRing R] (x y : R) : R :=
  (3 * y + x + 9 * x * y + 4 * x ^ 2 + 7 * x ^ 2 * y + 4 * x ^ 3 * y + (-1) * x ^ 4 + 3 * x ^ 5)

/-- `p₂(κ) = h₂ · W + 5 e₂`. -/
theorem q2_id {R : Type*} [CommRing R] (x y : R) :
    q2 x y = h2 x y * Wp x y + 5 * e2 x y := by
  unfold q2 h2 Wp e2 kp0 kp1 kp2 kp3 kp4
  refl_ring1

/-- Cofactor of the fourth Pfaffian. -/
def h3 {R : Type*} [CommRing R] (x y : R) : R := ((-16) + (-31) * x + (-15) * x ^ 2)

/-- Error term of the fourth Pfaffian. -/
def e3 {R : Type*} [CommRing R] (x y : R) : R :=
  ((-1) + (-4) * y + (-1) * x + (-9) * x * y + 4 * x ^ 2 + (-10) * x ^ 2 * y + 3 * x ^ 3 +
    (-5) * x ^ 3 * y + (-4) * x ^ 4 + (-3) * x ^ 5)

/-- `p₃(κ) = h₃ · W + 5 e₃`. -/
theorem q3_id {R : Type*} [CommRing R] (x y : R) :
    q3 x y = h3 x y * Wp x y + 5 * e3 x y := by
  unfold q3 h3 Wp e3 kp0 kp1 kp2 kp3 kp4
  refl_ring1

/-- Cofactor of the fifth Pfaffian. -/
def h4 {R : Type*} [CommRing R] (x y : R) : R := ((-4) * x + (-5) * x ^ 2)

/-- Error term of the fifth Pfaffian. -/
def e4 {R : Type*} [CommRing R] (x y : R) : R :=
  ((-3) + (-3) * x + (-3) * x * y + (-8) * x ^ 2 + (-3) * x ^ 2 * y + (-4) * x ^ 3 + (-5) * x ^ 3 * y
    + (-4) * x ^ 4 + (-1) * x ^ 5)

/-- `p₄(κ) = h₄ · W + 5 e₄`. -/
theorem q4_id {R : Type*} [CommRing R] (x y : R) :
    q4 x y = h4 x y * Wp x y + 5 * e4 x y := by
  unfold q4 h4 Wp e4 kp0 kp1 kp2 kp3 kp4
  refl_ring1

/-- Cofactor of the `κ₄`-relation. -/
def hrel {R : Type*} [CommRing R] (x y : R) : R := ((-1) + (-2) * x + (-1) * x ^ 2)

/-- Error term of the `κ₄`-relation. -/
def erel {R : Type*} [CommRing R] (x y : R) : R := (x ^ 2 + x ^ 3 + 3 * x ^ 4)

/-- The relation `x⁵ + 8κ₄x² + κ₄x + κ₄ - κ₄² = hrel·W + 5·erel`. -/
theorem rel_id {R : Type*} [CommRing R] (x y : R) :
    (x ^ 5 + 8 * (kp4 x y) * x ^ 2 + (kp4 x y) * x + (kp4 x y) - (kp4 x y) ^ 2) =
      hrel x y * Wp x y + 5 * erel x y := by
  unfold kp4 Wp hrel erel
  refl_ring1

/-- The matrix identity `C11inv · C11 = 1 + 5 · C11invE`, equivalently
`bas = ∑ᵢ (C11inv)ₘᵢ κᵢ - 5 · (C11invE)ₘ · bas`. -/
theorem bas_id {R : Type} [CommRing R] (x y : R) (m : Fin 5) :
    ![1, x, y, x ^ 2, x * y] m =
      (∑ i : Fin 5, C11inv R m i * ![kp0 x y, kp1 x y, kp2 x y, kp3 x y, kp4 x y] i) -
        5 * ∑ j : Fin 5, (C11invE m j : R) * ![1, x, y, x ^ 2, x * y] j := by
  fin_cases m <;>
  · rw [Fin.sum_univ_five, Fin.sum_univ_five]
    simp only [C11inv, C11invE, kp0, kp1, kp2, kp3, kp4, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_zero',
      Matrix.cons_val_succ, Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons]
    first | refl_ring1 | ring

/-- The `x`-coordinate from the inverse matrix, over `ℤ`. -/
theorem x_bas_id {R : Type*} [CommRing R] (x y : R) :
    x + 5 * (4 + 2 * x + y + 4 * x ^ 2 + 3 * (x * y)) =
      3 * kp0 x y + kp1 x y + 2 * kp2 x y + 2 * kp3 x y + kp4 x y := by
  unfold kp0 kp1 kp2 kp3 kp4
  refl_ring1

/-- The `y`-coordinate from the inverse matrix, over `ℤ`. -/
theorem y_bas_id {R : Type*} [CommRing R] (x y : R) :
    y + 5 * (5 + 3 * x + 2 * y + 7 * x ^ 2 + 5 * (x * y)) =
      3 * kp0 x y + 2 * kp1 x y + 3 * kp2 x y + 2 * kp3 x y + 3 * kp4 x y := by
  unfold kp0 kp1 kp2 kp3 kp4
  refl_ring1

/-! ## §3 The function field of `E11` -/

/-- The function field of `E11` over `L`. -/
abbrev F11 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] : Type :=
  Affine.FunctionField ((E11 𝕜).baseChange L)

/-- The `x`-coordinate of the generic point of `E11` over `L`. -/
abbrev x11 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] : F11 𝕜 L :=
  Work.MotV.genX ((E11 𝕜).baseChange L)

/-- The `y`-coordinate of the generic point of `E11` over `L`. -/
abbrev y11 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] : F11 𝕜 L :=
  Work.MotV.genY ((E11 𝕜).baseChange L)

/-- The function field of `E11` over `L` has characteristic `5`. -/
theorem charP_F11 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] :
    CharP (F11 𝕜 L) 5 :=
  charP_of_injective_algebraMap (algebraMap 𝕜 (F11 𝕜 L)).injective 5

/-- `5 = 0` in the function field. -/
theorem five_F11 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] :
    (5 : F11 𝕜 L) = 0 := by
  haveI : CharP (F11 𝕜 L) 5 := charP_F11 𝕜 L
  exact CharP.cast_eq_zero (F11 𝕜 L) 5

/-! ## §4 Arithmetic of the curve `E11` -/

/-- The discriminant of `E11` is `4` in characteristic `5`. -/
theorem E11_Δ (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] : (E11 𝕜).Δ = 4 := by
  have h : (E11 𝕜).Δ = 4 + 5 * (-4660 : 𝕜) := by
    simp only [E11, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    refl_ring1
  rw [h, show (5 : 𝕜) = 0 from CharP.cast_eq_zero 𝕜 5, zero_mul, add_zero]

/-- The `c₄`-invariant of `E11` is `1` in characteristic `5`. -/
theorem E11_c₄ (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] : (E11 𝕜).c₄ = 1 := by
  have h : (E11 𝕜).c₄ = 1 + 5 * (51 : 𝕜) := by
    simp only [E11, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    refl_ring1
  rw [h, show (5 : 𝕜) = 0 from CharP.cast_eq_zero 𝕜 5, zero_mul, add_zero]

/-- `E11` is an elliptic curve. -/
theorem E11_isElliptic (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] : (E11 𝕜).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by
    rw [E11_Δ 𝕜]
    intro h0
    exact absurd ((CharP.cast_eq_zero_iff 𝕜 5 4).mp h0) (by norm_num))⟩

instance instIsEllipticE11 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] : (E11 𝕜).IsElliptic :=
  E11_isElliptic 𝕜

/-- The `j`-invariant of `E11` is `4` in characteristic `5`. -/
theorem E11_j (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] : (E11 𝕜).j = 4 := by
  have hΔ : (E11 𝕜).Δ = 4 := E11_Δ 𝕜
  have hΔ0 : (E11 𝕜).Δ ≠ 0 := by
    rw [hΔ]
    intro h0
    exact absurd ((CharP.cast_eq_zero_iff 𝕜 5 4).mp h0) (by norm_num)
  have hc : (E11 𝕜).c₄ ^ 3 = 4 * (E11 𝕜).Δ := by
    have h : (E11 𝕜).c₄ ^ 3 = 4 * (E11 𝕜).Δ + 5 * (3374080 : 𝕜) := by
      simp only [E11, WeierstrassCurve.c₄, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
        WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      refl_ring1
    rw [h, show (5 : 𝕜) = 0 from CharP.cast_eq_zero 𝕜 5, zero_mul, add_zero]
  rw [WeierstrassCurve.j_eq, hc]
  field_simp

/-- The `j`-invariant of `E11` is nonzero. -/
theorem E11_j_ne_zero (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] : (E11 𝕜).j ≠ 0 := by
  have h4 : (4 : 𝕜) = -1 := by
    rw [show (4 : 𝕜) = -1 + 5 * (1 : 𝕜) by ring,
      show (5 : 𝕜) = 0 from CharP.cast_eq_zero 𝕜 5, mul_one, add_zero]
  rw [E11_j 𝕜, h4]
  exact neg_ne_zero.mpr one_ne_zero

/-- The `j`-invariant of `E11` is not `1728` in characteristic `5`. -/
theorem E11_j_ne (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] : (E11 𝕜).j ≠ 1728 := by
  have h1728 : (1728 : 𝕜) = 3 := by
    rw [show (1728 : 𝕜) = 3 + 5 * (345 : 𝕜) by ring,
      show (5 : 𝕜) = 0 from CharP.cast_eq_zero 𝕜 5, zero_mul, add_zero]
  rw [E11_j 𝕜, h1728]
  intro h
  have h1 : (4 : 𝕜) - 3 = (1 : 𝕜) := by ring
  have h0 : (4 : 𝕜) - 3 = 0 := by rw [h, sub_self]
  rw [h1] at h0
  exact one_ne_zero h0

/-- The smoothness parameter `a² - ab - b²` of `D11` is `-1 ≠ 0`. -/
theorem D11_smooth (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] :
    (D11 𝕜).a ^ 2 - (D11 𝕜).a * (D11 𝕜).b - (D11 𝕜).b ^ 2 ≠ 0 := by
  show (1 : 𝕜) ^ 2 - (1 : 𝕜) * 1 - (1 : 𝕜) ^ 2 ≠ 0
  intro h
  have h1 : (1 : 𝕜) ^ 2 - (1 : 𝕜) * 1 - (1 : 𝕜) ^ 2 = -(1 : 𝕜) := by ring
  rw [h1] at h
  exact neg_ne_zero.mpr one_ne_zero h

/-- The Weierstrass relation in the function field: `y² - y = x³ - x²`. -/
theorem W11_rel (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] :
    (y11 𝕜 L) ^ 2 - y11 𝕜 L = (x11 𝕜 L) ^ 3 - (x11 𝕜 L) ^ 2 := by
  have ha1 : ((E11 𝕜).baseChange L).a₁ = 0 := by
    rw [show ((E11 𝕜).baseChange L).a₁ = algebraMap 𝕜 L ((E11 𝕜).a₁) from rfl, E11, map_zero]
  have ha2 : ((E11 𝕜).baseChange L).a₂ = 4 := by
    rw [show ((E11 𝕜).baseChange L).a₂ = algebraMap 𝕜 L ((E11 𝕜).a₂) from rfl, E11, map_ofNat]
  have ha3 : ((E11 𝕜).baseChange L).a₃ = 4 := by
    rw [show ((E11 𝕜).baseChange L).a₃ = algebraMap 𝕜 L ((E11 𝕜).a₃) from rfl, E11, map_ofNat]
  have ha4 : ((E11 𝕜).baseChange L).a₄ = 0 := by
    rw [show ((E11 𝕜).baseChange L).a₄ = algebraMap 𝕜 L ((E11 𝕜).a₄) from rfl, E11, map_zero]
  have ha6 : ((E11 𝕜).baseChange L).a₆ = 0 := by
    rw [show ((E11 𝕜).baseChange L).a₆ = algebraMap 𝕜 L ((E11 𝕜).a₆) from rfl, E11, map_zero]
  have h := Work.MotC2.genY_sq_relation ((E11 𝕜).baseChange L)
  rw [ha1, ha2, ha3, ha4, ha6] at h
  simp only [map_zero, map_ofNat, zero_mul, zero_add, mul_one] at h
  rw [show Work.MotC2.genX ((E11 𝕜).baseChange L) = x11 𝕜 L from rfl,
    show Work.MotC2.genY ((E11 𝕜).baseChange L) = y11 𝕜 L from rfl] at h
  have h4 : (4 : F11 𝕜 L) = -1 := by
    rw [show (4 : F11 𝕜 L) = -1 + 5 * 1 by ring,
      show (5 : F11 𝕜 L) = 0 from five_F11 𝕜 L, mul_one, add_zero]
  rw [h4] at h
  linear_combination (norm := refl_ring1) h

/-- The Weierstrass polynomial vanishes at the generic point. -/
theorem W11_Wp (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] :
    Wp (x11 𝕜 L) (y11 𝕜 L) = 0 := by
  rw [Wp,
    show (y11 𝕜 L) ^ 2 - y11 𝕜 L - (x11 𝕜 L) ^ 3 + (x11 𝕜 L) ^ 2 =
      ((y11 𝕜 L) ^ 2 - y11 𝕜 L) - ((x11 𝕜 L) ^ 3 - (x11 𝕜 L) ^ 2) by ring,
    W11_rel 𝕜 L, sub_self]

/-! ## §5 The Klein coordinates, expanded -/

/-- The coordinate matrix of `D11`, unfolded. -/
theorem D11_coord (𝕜 : Type) [Field 𝕜] : (D11 𝕜).coord = C11 𝕜 := rfl

/-- The base curve of `D11`, unfolded. -/
theorem D11_E (𝕜 : Type) [Field 𝕜] : (D11 𝕜).E = E11 𝕜 := rfl

/-- The Klein basis of `D11`, unfolded. -/
theorem D11_kleinBas (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L]
    (m : Fin 5) :
    Work.MotV.kleinBas (D11 𝕜) L m =
      ![1, x11 𝕜 L, y11 𝕜 L, (x11 𝕜 L) ^ 2, x11 𝕜 L * y11 𝕜 L] m := rfl

/-- `κ_0 = 1`. -/
theorem kleinCoord_zero (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] :
    Work.MotV.kleinCoord (D11 𝕜) L 0 = kp0 (x11 𝕜 L) (y11 𝕜 L) := by
  simp only [Work.MotV.kleinCoord]
  rw [Fin.sum_univ_five]
  simp only [D11_coord, C11, kp0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_zero', Matrix.cons_val_succ,
    Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons]
  simp only [map_ofNat, map_one, map_zero]
  refl_ring1

/-- `κ_1 = 1 + 4y + x + 4xy + 4x²`. -/
theorem kleinCoord_one (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] :
    Work.MotV.kleinCoord (D11 𝕜) L 1 = kp1 (x11 𝕜 L) (y11 𝕜 L) := by
  simp only [Work.MotV.kleinCoord]
  rw [Fin.sum_univ_five]
  simp only [D11_coord, C11, kp1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_zero', Matrix.cons_val_succ,
    Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons]
  simp only [map_ofNat, map_one, map_zero]
  refl_ring1

/-- `κ_2 = 4 + 3x + 4xy + 3x²`. -/
theorem kleinCoord_two (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] :
    Work.MotV.kleinCoord (D11 𝕜) L 2 = kp2 (x11 𝕜 L) (y11 𝕜 L) := by
  simp only [Work.MotV.kleinCoord]
  rw [Fin.sum_univ_five]
  simp only [D11_coord, C11, kp2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_zero', Matrix.cons_val_succ,
    Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons]
  simp only [map_ofNat, map_one, map_zero]
  refl_ring1

/-- `κ_3 = 4 + 2x + xy + 3x²`. -/
theorem kleinCoord_three (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] :
    Work.MotV.kleinCoord (D11 𝕜) L 3 = kp3 (x11 𝕜 L) (y11 𝕜 L) := by
  simp only [Work.MotV.kleinCoord]
  rw [Fin.sum_univ_five]
  simp only [D11_coord, C11, kp3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_zero', Matrix.cons_val_succ,
    Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons]
  simp only [map_ofNat, map_one, map_zero]
  refl_ring1

/-- `κ_4 = y + xy + 4x²`. -/
theorem kleinCoord_four (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] :
    Work.MotV.kleinCoord (D11 𝕜) L 4 = kp4 (x11 𝕜 L) (y11 𝕜 L) := by
  simp only [Work.MotV.kleinCoord]
  rw [Fin.sum_univ_five]
  simp only [D11_coord, C11, kp4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_zero', Matrix.cons_val_succ,
    Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons]
  simp only [map_ofNat, map_one, map_zero]
  refl_ring1

/-! ## §6 The Klein conditions -/

/-- The Pfaffian `p₀` of the Klein tuple `kp₀, …, kp₄` is `q0`. -/
theorem kleinP0_kp {R : Type*} [CommRing R] (x y : R) :
    Work.MotK.kleinP0 1 1 ![kp0 x y, kp1 x y, kp2 x y, kp3 x y, kp4 x y] = q0 x y := by
  simp only [Work.MotK.kleinP0, q0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_zero', Matrix.cons_val_succ,
    Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons, one_mul, mul_one, one_pow]
  refl_ring1

/-- The Pfaffian `p₁` of the Klein tuple `kp₀, …, kp₄` is `q1`. -/
theorem kleinP1_kp {R : Type*} [CommRing R] (x y : R) :
    Work.MotK.kleinP1 1 1 ![kp0 x y, kp1 x y, kp2 x y, kp3 x y, kp4 x y] = q1 x y := by
  simp only [Work.MotK.kleinP1, q1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_zero', Matrix.cons_val_succ,
    Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons, one_mul, mul_one, one_pow]
  refl_ring1

/-- The Pfaffian `p₂` of the Klein tuple `kp₀, …, kp₄` is `q2`. -/
theorem kleinP2_kp {R : Type*} [CommRing R] (x y : R) :
    Work.MotK.kleinP2 1 1 ![kp0 x y, kp1 x y, kp2 x y, kp3 x y, kp4 x y] = q2 x y := by
  simp only [Work.MotK.kleinP2, q2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_zero', Matrix.cons_val_succ,
    Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons, one_mul, mul_one, one_pow]
  refl_ring1

/-- The Pfaffian `p₃` of the Klein tuple `kp₀, …, kp₄` is `q3`. -/
theorem kleinP3_kp {R : Type*} [CommRing R] (x y : R) :
    Work.MotK.kleinP3 1 1 ![kp0 x y, kp1 x y, kp2 x y, kp3 x y, kp4 x y] = q3 x y := by
  simp only [Work.MotK.kleinP3, q3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_zero', Matrix.cons_val_succ,
    Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons, one_mul, mul_one, one_pow]
  refl_ring1

/-- The Pfaffian `p₄` of the Klein tuple `kp₀, …, kp₄` is `q4`. -/
theorem kleinP4_kp {R : Type*} [CommRing R] (x y : R) :
    Work.MotK.kleinP4 1 1 ![kp0 x y, kp1 x y, kp2 x y, kp3 x y, kp4 x y] = q4 x y := by
  simp only [Work.MotK.kleinP4, q4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_zero', Matrix.cons_val_succ,
    Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons, one_mul, mul_one, one_pow]
  refl_ring1

/-- The Klein coordinates as the explicit tuple of polynomials in `x` and `y`. -/
theorem kleinCoord_eq_fun (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] :
    Work.MotV.kleinCoord (D11 𝕜) L =
      ![kp0 (x11 𝕜 L) (y11 𝕜 L), kp1 (x11 𝕜 L) (y11 𝕜 L), kp2 (x11 𝕜 L) (y11 𝕜 L),
        kp3 (x11 𝕜 L) (y11 𝕜 L), kp4 (x11 𝕜 L) (y11 𝕜 L)] := by
  funext i
  fin_cases i
  · simp only [Matrix.cons_val_zero, Fin.zero_eta, Fin.isValue]
    exact kleinCoord_zero 𝕜 L
  · simp only [Matrix.cons_val_one, Matrix.head_cons, Fin.isValue]
    exact kleinCoord_one 𝕜 L
  · simp only [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    exact kleinCoord_two 𝕜 L
  · simp only [Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    exact kleinCoord_three 𝕜 L
  · simp only [Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    exact kleinCoord_four 𝕜 L

/-- The five Pfaffian quadrics vanish on `κ` in the function field of `E11`. -/
theorem klein_eq11 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] :
    ∀ k : Fin 5,
      Work.MotK.kleinP (algebraMap 𝕜 (F11 𝕜 L) (D11 𝕜).a)
        (algebraMap 𝕜 (F11 𝕜 L) (D11 𝕜).b)
        (Work.MotV.kleinCoord (D11 𝕜) L) k = 0 := by
  have ha : (D11 𝕜).a = (1 : 𝕜) := rfl
  have hb : (D11 𝕜).b = (1 : 𝕜) := rfl
  rw [ha, hb, map_one]
  intro k
  have h5 : (5 : F11 𝕜 L) = 0 := five_F11 𝕜 L
  have hW : Wp (x11 𝕜 L) (y11 𝕜 L) = 0 := W11_Wp 𝕜 L
  rw [kleinCoord_eq_fun 𝕜 L]
  fin_cases k
  · rw [Work.MotK.kleinP_zero', kleinP0_kp, q0_id, hW, mul_zero, zero_add, h5, zero_mul]
  · rw [Work.MotK.kleinP_one', kleinP1_kp, q1_id, hW, mul_zero, zero_add, h5, zero_mul]
  · rw [Work.MotK.kleinP_two', kleinP2_kp, q2_id, hW, mul_zero, zero_add, h5, zero_mul]
  · rw [Work.MotK.kleinP_three', kleinP3_kp, q3_id, hW, mul_zero, zero_add, h5, zero_mul]
  · rw [Work.MotK.kleinP_four', kleinP4_kp, q4_id, hW, mul_zero, zero_add, h5, zero_mul]

/-- `κ_0` does not vanish. -/
theorem coord0_ne11 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] :
    Work.MotV.kleinCoord (D11 𝕜) L 0 ≠ 0 := by
  rw [kleinCoord_zero 𝕜 L]
  simp only [kp0]
  exact one_ne_zero

/-! ## §7 `spans`, `x`, `y` and the generation of the function field -/

/-- The Klein coordinates span the basis `1, x, y, x², xy`: the field `Good.spans`. -/
theorem spans11 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] (m : Fin 5) :
    Work.MotV.kleinBas (D11 𝕜) L m =
      ∑ i : Fin 5,
        algebraMap L (F11 𝕜 L) (algebraMap 𝕜 L (C11inv 𝕜 m i)) *
          Work.MotV.kleinCoord (D11 𝕜) L i := by
  have h := bas_id (x11 𝕜 L) (y11 𝕜 L) m
  rw [show (5 : F11 𝕜 L) = 0 from five_F11 𝕜 L, zero_mul, sub_zero] at h
  rw [D11_kleinBas 𝕜 L m, h, Fin.sum_univ_five, Fin.sum_univ_five]
  fin_cases m <;>
  · simp only [C11inv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_zero', Matrix.cons_val_succ,
      Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons, kp0, kp1, kp2, kp3, kp4,
      kleinCoord_zero 𝕜 L, kleinCoord_one 𝕜 L, kleinCoord_two 𝕜 L, kleinCoord_three 𝕜 L,
      kleinCoord_four 𝕜 L, IsScalarTower.algebraMap_apply, map_ofNat, map_one, map_zero]

/-- `x` as a `𝕜`-linear combination of the Klein coordinates. -/
theorem x11_eq (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] :
    x11 𝕜 L = 3 * Work.MotV.kleinCoord (D11 𝕜) L 0 + Work.MotV.kleinCoord (D11 𝕜) L 1 +
      2 * Work.MotV.kleinCoord (D11 𝕜) L 2 + 2 * Work.MotV.kleinCoord (D11 𝕜) L 3 +
      Work.MotV.kleinCoord (D11 𝕜) L 4 := by
  have h := x_bas_id (x11 𝕜 L) (y11 𝕜 L)
  rw [show (5 : F11 𝕜 L) = 0 from five_F11 𝕜 L, zero_mul, add_zero] at h
  rw [kleinCoord_zero 𝕜 L, kleinCoord_one 𝕜 L, kleinCoord_two 𝕜 L, kleinCoord_three 𝕜 L,
    kleinCoord_four 𝕜 L]
  exact h

/-- `y` as a `𝕜`-linear combination of the Klein coordinates. -/
theorem y11_eq (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] :
    y11 𝕜 L = 3 * Work.MotV.kleinCoord (D11 𝕜) L 0 + 2 * Work.MotV.kleinCoord (D11 𝕜) L 1 +
      3 * Work.MotV.kleinCoord (D11 𝕜) L 2 + 2 * Work.MotV.kleinCoord (D11 𝕜) L 3 +
      3 * Work.MotV.kleinCoord (D11 𝕜) L 4 := by
  have h := y_bas_id (x11 𝕜 L) (y11 𝕜 L)
  rw [show (5 : F11 𝕜 L) = 0 from five_F11 𝕜 L, zero_mul, add_zero] at h
  rw [kleinCoord_zero 𝕜 L, kleinCoord_one 𝕜 L, kleinCoord_two 𝕜 L, kleinCoord_three 𝕜 L,
    kleinCoord_four 𝕜 L]
  exact h

/-- `x` lies in the field generated by the Klein coordinates. -/
theorem x11_mem_adjoin (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] :
    x11 𝕜 L ∈ IntermediateField.adjoin L
      (Set.range fun i : Fin 5 => Work.MotV.kleinCoord (D11 𝕜) L i) := by
  rw [x11_eq 𝕜 L]
  have h3 : (3 : F11 𝕜 L) = algebraMap L (F11 𝕜 L) (algebraMap 𝕜 L (3 : 𝕜)) := by
    simp only [IsScalarTower.algebraMap_apply, map_ofNat]
  have h2 : (2 : F11 𝕜 L) = algebraMap L (F11 𝕜 L) (algebraMap 𝕜 L (2 : 𝕜)) := by
    simp only [IsScalarTower.algebraMap_apply, map_ofNat]
  rw [h3, h2]
  refine add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · exact mul_mem ((IntermediateField.adjoin L _).algebraMap_mem (algebraMap 𝕜 L (3 : 𝕜)))
      (IntermediateField.subset_adjoin L _ (Set.mem_range_self 0))
  · exact IntermediateField.subset_adjoin L _ (Set.mem_range_self 1)
  · exact mul_mem ((IntermediateField.adjoin L _).algebraMap_mem (algebraMap 𝕜 L (2 : 𝕜)))
      (IntermediateField.subset_adjoin L _ (Set.mem_range_self 2))
  · exact mul_mem ((IntermediateField.adjoin L _).algebraMap_mem (algebraMap 𝕜 L (2 : 𝕜)))
      (IntermediateField.subset_adjoin L _ (Set.mem_range_self 3))
  · exact IntermediateField.subset_adjoin L _ (Set.mem_range_self 4)

/-- `y` lies in the field generated by the Klein coordinates. -/
theorem y11_mem_adjoin (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] :
    y11 𝕜 L ∈ IntermediateField.adjoin L
      (Set.range fun i : Fin 5 => Work.MotV.kleinCoord (D11 𝕜) L i) := by
  rw [y11_eq 𝕜 L]
  have h3 : (3 : F11 𝕜 L) = algebraMap L (F11 𝕜 L) (algebraMap 𝕜 L (3 : 𝕜)) := by
    simp only [IsScalarTower.algebraMap_apply, map_ofNat]
  have h2 : (2 : F11 𝕜 L) = algebraMap L (F11 𝕜 L) (algebraMap 𝕜 L (2 : 𝕜)) := by
    simp only [IsScalarTower.algebraMap_apply, map_ofNat]
  rw [h3, h2]
  refine add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_) ?_
  · exact mul_mem ((IntermediateField.adjoin L _).algebraMap_mem (algebraMap 𝕜 L (3 : 𝕜)))
      (IntermediateField.subset_adjoin L _ (Set.mem_range_self 0))
  · exact mul_mem ((IntermediateField.adjoin L _).algebraMap_mem (algebraMap 𝕜 L (2 : 𝕜)))
      (IntermediateField.subset_adjoin L _ (Set.mem_range_self 1))
  · exact mul_mem ((IntermediateField.adjoin L _).algebraMap_mem (algebraMap 𝕜 L (3 : 𝕜)))
      (IntermediateField.subset_adjoin L _ (Set.mem_range_self 2))
  · exact mul_mem ((IntermediateField.adjoin L _).algebraMap_mem (algebraMap 𝕜 L (2 : 𝕜)))
      (IntermediateField.subset_adjoin L _ (Set.mem_range_self 3))
  · exact mul_mem ((IntermediateField.adjoin L _).algebraMap_mem (algebraMap 𝕜 L (3 : 𝕜)))
      (IntermediateField.subset_adjoin L _ (Set.mem_range_self 4))

/-- The Klein ratios generate the function field: `KleinData.Generates`. -/
theorem generates11 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] : KleinData.Generates (D11 𝕜) := by
  intro L _ _
  have hset : (Set.range fun i : Fin 5 =>
        Work.MotV.kleinCoord (D11 𝕜) L i / Work.MotV.kleinCoord (D11 𝕜) L 0) =
      Set.range fun i : Fin 5 => Work.MotV.kleinCoord (D11 𝕜) L i := by
    ext z
    simp only [Set.mem_range]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, by rw [kleinCoord_zero 𝕜 L, kp0, div_one]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, by rw [kleinCoord_zero 𝕜 L, kp0, div_one]⟩
  rw [hset, eq_top_iff, ← Work.MotV5.adjoin_genX_genY L ((D11 𝕜).E.baseChange L)]
  exact IntermediateField.adjoin_le_iff.mpr (by
    intro z hz
    rcases hz with rfl | rfl
    · exact x11_mem_adjoin 𝕜 L
    · exact y11_mem_adjoin 𝕜 L)

/-! ## §8 `T_diag` is vacuous in characteristic `5` -/

/-- `T_diag` is vacuous in characteristic `5`: there is no primitive fifth root of unity. -/
theorem T_diag11 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] (ζ : L)
    (hζ : IsPrimitiveRoot ζ 5) :
    ∃ σ : F11 𝕜 L ≃ₐ[L] F11 𝕜 L,
      ∀ i, σ (Work.MotV.kleinCoord (D11 𝕜) L i / Work.MotV.kleinCoord (D11 𝕜) L 0) =
        algebraMap L (F11 𝕜 L) ζ ^ (i : ℕ) *
          (Work.MotV.kleinCoord (D11 𝕜) L i / Work.MotV.kleinCoord (D11 𝕜) L 0) := by
  exfalso
  haveI : CharP L 5 := charP_of_injective_algebraMap (algebraMap 𝕜 L).injective 5
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hpow : ζ ^ 5 = 1 := hζ.pow_eq_one
  have hsub : (ζ - 1) ^ 5 = 0 := by
    rw [sub_pow_char (R := L) (p := 5) (x := ζ) (y := 1)]
    simp [hpow]
  have hz : ζ - 1 = 0 := by
    by_contra h
    exact pow_ne_zero 5 h hsub
  exact hζ.ne_one (by norm_num) (sub_eq_zero.mp hz)

/-! ## §9 The non-constancy of `κ₄` -/

/-- The relation `x⁵ + 8·κ₄·x² + κ₄·x + κ₄ - κ₄² = 0` in the function field. -/
theorem relation_kappa4_F (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] :
    (x11 𝕜 L) ^ 5 + 8 * (Work.MotV.kleinCoord (D11 𝕜) L 4) * (x11 𝕜 L) ^ 2 +
        (Work.MotV.kleinCoord (D11 𝕜) L 4) * (x11 𝕜 L) +
        (Work.MotV.kleinCoord (D11 𝕜) L 4) - (Work.MotV.kleinCoord (D11 𝕜) L 4) ^ 2 = 0 := by
  have h5 : (5 : F11 𝕜 L) = 0 := five_F11 𝕜 L
  have hW : Wp (x11 𝕜 L) (y11 𝕜 L) = 0 := W11_Wp 𝕜 L
  rw [kleinCoord_four 𝕜 L]
  rw [rel_id (x11 𝕜 L) (y11 𝕜 L), hW, mul_zero, zero_add, h5, zero_mul]

/-- The relation in the associated form used for `aeval`. -/
theorem relation_kappa4_assoc (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L]
    [Algebra 𝕜 L] :
    (x11 𝕜 L) ^ 5 + (8 * (Work.MotV.kleinCoord (D11 𝕜) L 4) * (x11 𝕜 L) ^ 2 +
        ((Work.MotV.kleinCoord (D11 𝕜) L 4) * (x11 𝕜 L) +
          ((Work.MotV.kleinCoord (D11 𝕜) L 4) - (Work.MotV.kleinCoord (D11 𝕜) L 4) ^ 2))) = 0 := by
  linear_combination (norm := refl_ring1) relation_kappa4_F 𝕜 L

/-- The field `𝕜⟮κ₄⟯`. -/
abbrev K4 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] :
    IntermediateField 𝕜 (F11 𝕜 L) :=
  IntermediateField.adjoin 𝕜 ({Work.MotV.kleinCoord (D11 𝕜) L 4} : Set (F11 𝕜 L))

/-- The element `κ₄`. -/
abbrev k4 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] : F11 𝕜 L :=
  Work.MotV.kleinCoord (D11 𝕜) L 4

/-- `x` is algebraic over `𝕜⟮κ₄⟯` (it is a root of the explicit quintic). -/
theorem isAlgebraic_kappa4 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L] [Algebra 𝕜 L] :
    IsAlgebraic ↥(K4 𝕜 L) (x11 𝕜 L) := by
  have hgen : k4 𝕜 L ∈ K4 𝕜 L :=
    IntermediateField.subset_adjoin 𝕜 _ (Set.mem_singleton _)
  have hcoef1 : (8 : F11 𝕜 L) * k4 𝕜 L ∈ K4 𝕜 L := by
    have h8 : (8 : F11 𝕜 L) = algebraMap 𝕜 (F11 𝕜 L) (8 : 𝕜) := (map_ofNat _ 8).symm
    rw [h8]
    exact mul_mem ((K4 𝕜 L).algebraMap_mem (8 : 𝕜)) hgen
  have hcoef3 : k4 𝕜 L - (k4 𝕜 L) ^ 2 ∈ K4 𝕜 L := sub_mem hgen (pow_mem hgen 2)
  refine ⟨Polynomial.X ^ 5 + (Polynomial.C (⟨(8 : F11 𝕜 L) * k4 𝕜 L, hcoef1⟩ : ↥(K4 𝕜 L)) *
        Polynomial.X ^ 2 + (Polynomial.C (⟨k4 𝕜 L, hgen⟩ : ↥(K4 𝕜 L)) * Polynomial.X +
          Polynomial.C (⟨k4 𝕜 L - (k4 𝕜 L) ^ 2, hcoef3⟩ : ↥(K4 𝕜 L)))), ?_, ?_⟩
  · refine (Polynomial.monic_X_pow_add ?_).ne_zero
    compute_degree!
  · have haev : Polynomial.aeval (x11 𝕜 L)
        (Polynomial.X ^ 5 + (Polynomial.C (⟨(8 : F11 𝕜 L) * k4 𝕜 L, hcoef1⟩ : ↥(K4 𝕜 L)) *
            Polynomial.X ^ 2 + (Polynomial.C (⟨k4 𝕜 L, hgen⟩ : ↥(K4 𝕜 L)) * Polynomial.X +
              Polynomial.C (⟨k4 𝕜 L - (k4 𝕜 L) ^ 2, hcoef3⟩ : ↥(K4 𝕜 L))))) =
        (x11 𝕜 L) ^ 5 + (8 * k4 𝕜 L * (x11 𝕜 L) ^ 2 +
          (k4 𝕜 L * (x11 𝕜 L) + (k4 𝕜 L - (k4 𝕜 L) ^ 2))) := by
      simp only [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_X_pow,
        Polynomial.aeval_X, Polynomial.aeval_C] <;> rfl
    rw [haev, relation_kappa4_assoc 𝕜 L]

/-- `κ₄/κ₀` is transcendental over `𝕜`. -/
theorem transcendental_kappa4 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (L : Type) [Field L]
    [Algebra 𝕜 L] :
    Transcendental 𝕜 (Work.MotV.kleinCoord (D11 𝕜) L 4 / Work.MotV.kleinCoord (D11 𝕜) L 0) := by
  have hdiv : Work.MotV.kleinCoord (D11 𝕜) L 4 / Work.MotV.kleinCoord (D11 𝕜) L 0 = k4 𝕜 L := by
    rw [kleinCoord_zero 𝕜 L]
    simp only [kp0, div_one]
  rw [hdiv]
  exact Work.MotV5.transcendental_of_isAlgebraic_adjoin_simple
    (Transcendental.restrictScalars (algebraMap 𝕜 L).injective
      (Work.MotC2.transcendental_genX ((E11 𝕜).baseChange L)))
    (isAlgebraic_kappa4 𝕜 L)

/-- `D11` is a genuine curve: `KleinData.Nonconstant`. -/
theorem nonconstant11 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] : KleinData.Nonconstant (D11 𝕜) :=
  ⟨4, fun L _ _ => transcendental_kappa4 𝕜 L⟩

/-! ## §10 The assembly -/

/-- `D11` is good Klein data. -/
theorem good11 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] : (D11 𝕜).Good :=
  { elliptic := E11_isElliptic 𝕜
    ab_ne := by
      show (1 : 𝕜) * 1 ≠ 0
      rw [one_mul]
      exact one_ne_zero
    j_ne_zero := E11_j_ne_zero 𝕜
    j_ne := E11_j_ne 𝕜
    klein_eq := fun L _ _ => klein_eq11 𝕜 L
    coord0_ne := fun L _ _ => coord0_ne11 𝕜 L
    T_diag := fun L _ _ ζ hζ => T_diag11 𝕜 L ζ hζ
    spans := ⟨C11inv 𝕜, fun L _ _ m => spans11 𝕜 L m⟩ }

/-- **The main theorem:** there is Klein data over every field of characteristic `5` satisfying the
Artin–Schreier nondegeneracy conditions. -/
theorem exists_kleinData_ASGood (𝕜 : Type) [Field 𝕜] [Infinite 𝕜] [CharP 𝕜 5] :
    ∃ D : Work.MotV.KleinData 𝕜, Work.MotV5.KleinData.ASGood D :=
  ⟨D11 𝕜, good11 𝕜, nonconstant11 𝕜, generates11 𝕜, D11_smooth 𝕜⟩

end

end Work.MotV5
