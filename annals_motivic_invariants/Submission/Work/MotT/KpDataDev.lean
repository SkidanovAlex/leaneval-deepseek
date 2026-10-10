import Mathlib
import Submission.Work.MotT.KleinParamData
import Submission.Work.MotC2.TranslationDefs
import Submission.Work.MotT.exists_kleinPoint

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Helper definitions and computations for `Work.MotT.kpData_klein_eq`.

The Klein quadrics of the parametric Klein datum `(a,b) = (u,1)` vanish on its Klein
coordinates.  The proof is a polynomial identity; this module isolates the pieces:

* `kpFF K u L` — the function field of the base-changed model `(kpData K u).E` over `L`;
* `kpUF`, `kpWF`, `kpDF` — the images of `u`, `w = 2u⁵-1`, `Δ = u¹⁰-11u⁵-1`;
* `kpX`, `kpY` — the coordinates `x`, `y`;
* `kpChatF` — the *cleared* coefficient matrix `w²·kpCoord` (no denominators), as polynomials
  in `kpUF`, `kpWF`, `kpDF`;
* `kpKappaHat` — the scaled Klein coordinates `w²·κ_i`, written in the basis `kpBas`;
* `kpWhatF` — `Λ · W` where `Λ = 5⁹u¹²w³` clears the denominators of the Weierstrass
  coefficients (so `kpWhatF` has polynomial coefficients and vanishes);
* `kpQ0F`, `kpQ1F` — the quotient `w · Q_k`, so that
  `5⁹u¹² · kleinP u 1 (w²κ) k = (kpQ0F k + kpQ1F k · x) · (Λ·W)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotT
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section

/-- The function field of the base-changed parametric Weierstrass model `(kpData K u).E`. -/
abbrev kpFF (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : Type :=
  Affine.FunctionField ((kpData K u).E.baseChange L)

/-- The `x`-coordinate in the function field. -/
def kpX (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  Work.MotV.genX ((kpData K u).E.baseChange L)

/-- The `y`-coordinate in the function field. -/
def kpY (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  Work.MotV.genY ((kpData K u).E.baseChange L)

/-- The image of `u` in the function field. -/
def kpUF (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  algebraMap K (kpFF K u L) u

/-- The image of `w = 2u⁵ - 1` in the function field. -/
def kpWF (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  2 * (kpUF K u L) ^(5:ℕ) - 1

/-- The image of `Δ = u¹⁰ - 11u⁵ - 1` in the function field. -/
def kpDF (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  (kpUF K u L) ^(10:ℕ) - 11 * (kpUF K u L) ^(5:ℕ) - 1

/-- The basis `1, x, y, x², x·y` of `L(5·O)`. -/
def kpBas (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : Fin 5 → kpFF K u L :=
  ![1, kpX K u L, kpY K u L, (kpX K u L) ^(2:ℕ), kpX K u L * kpY K u L]

/-- The Klein coordinates `κ_i` of the parametric datum, in the basis `kpBas`. -/
def kpKap (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : Fin 5 → kpFF K u L :=
  fun i => ∑ m : Fin 5, algebraMap K (kpFF K u L) (kpCoord K u i m) * kpBas K u L m

/-- The Klein coordinates of the parametric datum, in the basis `kpBas`. -/
lemma kleinCoord_eq_kpKap (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] :
    Work.MotV.kleinCoord (kpData K u) L = kpKap K u L := by
  funext i
  simp only [Work.MotV.kleinCoord, kpKap, kpBas, kpX, kpY]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← IsScalarTower.algebraMap_apply K L (kpFF K u L), Work.MotT.kpData_coord]

/-- The scaled Klein coordinate `w²·κ_0`. -/
def kpK0 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  -((kpUF K u L) ^(17:ℕ) * (kpDF K u L) ^(3:ℕ) * 390625)
    + (kpUF K u L) ^(21:ℕ) * (kpWF K u L) * (4 * (kpUF K u L) ^(5:ℕ) + 3) * (kpDF K u L)
        * (kpX K u L) * 48828125
    + (kpUF K u L) ^(25:ℕ) * (kpWF K u L) ^(2:ℕ) * (kpX K u L) ^(2:ℕ) * 6103515625

/-- The scaled Klein coordinate `w²·κ_1`. -/
def kpK1 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  (kpUF K u L) ^(15:ℕ) * (3 * (kpUF K u L) ^(5:ℕ) + 1) * (kpDF K u L) ^(3:ℕ) * 78125
    + (kpUF K u L) ^(19:ℕ) * (kpWF K u L) * (kpDF K u L) ^(2:ℕ) * (kpX K u L) * 19531250
    - (kpUF K u L) ^(21:ℕ) * (kpWF K u L) * (3 * (kpUF K u L) ^(5:ℕ) - 4) * (kpDF K u L)
        * (kpY K u L) * 48828125
    - (kpUF K u L) ^(23:ℕ) * ((kpUF K u L) ^(5:ℕ) + 2) * (kpWF K u L) ^(2:ℕ) * (kpX K u L) ^(2:ℕ)
        * 1220703125
    + (kpUF K u L) ^(25:ℕ) * (kpWF K u L) ^(2:ℕ) * (kpX K u L) * (kpY K u L) * 6103515625

/-- The scaled Klein coordinate `w²·κ_2`. -/
def kpK2 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  (kpUF K u L) ^(19:ℕ) * (kpDF K u L) ^(3:ℕ) * 390625
    - (kpUF K u L) ^(18:ℕ) * (kpWF K u L) * (6 * (kpUF K u L) ^(10:ℕ) + 24 * (kpUF K u L) ^(5:ℕ) - 1)
        * (kpDF K u L) * (kpX K u L) * 9765625
    + (kpUF K u L) ^(20:ℕ) * (kpWF K u L) * (7 * (kpUF K u L) ^(5:ℕ) - 1) * (kpDF K u L)
        * (kpY K u L) * 48828125
    - (kpUF K u L) ^(22:ℕ) * (kpWF K u L) ^(2:ℕ) * (3 * (kpUF K u L) ^(5:ℕ) + 1) * (kpX K u L) ^(2:ℕ)
        * 1220703125
    + (kpUF K u L) ^(24:ℕ) * (kpWF K u L) ^(2:ℕ) * (kpX K u L) * (kpY K u L) * 6103515625

/-- The scaled Klein coordinate `w²·κ_3`. -/
def kpK3 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  -((kpUF K u L) ^(14:ℕ) * (kpWF K u L) * (kpDF K u L) ^(3:ℕ) * 78125)
    + (kpUF K u L) ^(18:ℕ) * (kpWF K u L) ^(2:ℕ) * (7 * (kpUF K u L) ^(5:ℕ) - 1) * (kpDF K u L)
        * (kpX K u L) * 9765625
    - (kpUF K u L) ^(20:ℕ) * (kpWF K u L) * (7 * (kpUF K u L) ^(5:ℕ) - 1) * (kpDF K u L)
        * (kpY K u L) * 48828125
    - (kpUF K u L) ^(24:ℕ) * (kpWF K u L) ^(2:ℕ) * (kpX K u L) * (kpY K u L) * 6103515625

/-- The scaled Klein coordinate `w²·κ_4`. -/
def kpK4 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  (kpUF K u L) ^(15:ℕ) * (kpWF K u L) * (kpDF K u L) ^(3:ℕ) * 234375
    - (kpUF K u L) ^(19:ℕ) * (kpWF K u L) ^(2:ℕ) * (4 * (kpUF K u L) ^(5:ℕ) + 3) * (kpDF K u L)
        * (kpX K u L) * 9765625
    + (kpUF K u L) ^(21:ℕ) * (kpWF K u L) * (3 * (kpUF K u L) ^(5:ℕ) - 4) * (kpDF K u L)
        * (kpY K u L) * 48828125
    + (kpUF K u L) ^(23:ℕ) * (kpWF K u L) ^(3:ℕ) * (kpX K u L) ^(2:ℕ) * 1220703125
    - (kpUF K u L) ^(25:ℕ) * (kpWF K u L) ^(2:ℕ) * (kpX K u L) * (kpY K u L) * 6103515625

/-- The scaled Klein coordinates `w²·κ_i`, as a tuple. -/
def kpKappaHat (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] :
    Fin 5 → kpFF K u L :=
  fun i => if i = 0 then kpK0 K u L else
    if i = 1 then kpK1 K u L else
    if i = 2 then kpK2 K u L else
    if i = 3 then kpK3 K u L else kpK4 K u L

/-- The cleared coefficient matrix `w²·kpCoord`, as polynomials in `u`, `w`, `Δ`. -/
def kpChat (K : Type) [Field K] (u : K) : Fin 5 → Fin 5 → K :=
  ![![ -390625 * u ^(17:ℕ) * (kpDelta K u) ^(3:ℕ),
       48828125 * u ^(21:ℕ) * (kpW K u) * (4 * u ^(5:ℕ) + 3) * kpDelta K u,
       0,
       6103515625 * u ^(25:ℕ) * (kpW K u) ^(2:ℕ),
       0],
    ![ 78125 * u ^(15:ℕ) * (3 * u ^(5:ℕ) + 1) * (kpDelta K u) ^(3:ℕ),
       19531250 * u ^(19:ℕ) * (kpW K u) * (kpDelta K u) ^(2:ℕ),
       -48828125 * u ^(21:ℕ) * (kpW K u) * (3 * u ^(5:ℕ) - 4) * kpDelta K u,
       -1220703125 * u ^(23:ℕ) * (u ^(5:ℕ) + 2) * (kpW K u) ^(2:ℕ),
       6103515625 * u ^(25:ℕ) * (kpW K u) ^(2:ℕ)],
    ![ 390625 * u ^(19:ℕ) * (kpDelta K u) ^(3:ℕ),
       -9765625 * u ^(18:ℕ) * (kpW K u) * (6 * u ^(10:ℕ) + 24 * u ^(5:ℕ) - 1) * kpDelta K u,
       48828125 * u ^(20:ℕ) * (kpW K u) * (7 * u ^(5:ℕ) - 1) * kpDelta K u,
       -1220703125 * u ^(22:ℕ) * (kpW K u) ^(2:ℕ) * (3 * u ^(5:ℕ) + 1),
       6103515625 * u ^(24:ℕ) * (kpW K u) ^(2:ℕ)],
    ![ -78125 * u ^(14:ℕ) * (kpW K u) * (kpDelta K u) ^(3:ℕ),
       9765625 * u ^(18:ℕ) * (kpW K u) ^(2:ℕ) * (7 * u ^(5:ℕ) - 1) * kpDelta K u,
       -48828125 * u ^(20:ℕ) * (kpW K u) * (7 * u ^(5:ℕ) - 1) * kpDelta K u,
       0,
       -6103515625 * u ^(24:ℕ) * (kpW K u) ^(2:ℕ)],
    ![ 234375 * u ^(15:ℕ) * (kpW K u) * (kpDelta K u) ^(3:ℕ),
       -9765625 * u ^(19:ℕ) * (kpW K u) ^(2:ℕ) * (4 * u ^(5:ℕ) + 3) * kpDelta K u,
       48828125 * u ^(21:ℕ) * (kpW K u) * (3 * u ^(5:ℕ) - 4) * kpDelta K u,
       1220703125 * u ^(23:ℕ) * (kpW K u) ^(3:ℕ),
       -6103515625 * u ^(25:ℕ) * (kpW K u) ^(2:ℕ)]]

/-- `w²·kpCoord` is `kpChat`. -/
lemma kpChat_spec (K : Type) [Field K] (u : K) (hw : kpW K u ≠ 0) (i m : Fin 5) :
    kpChat K u i m = kpW K u ^(2:ℕ) * kpCoord K u i m := by
  fin_cases i <;> fin_cases m <;>
  · simp only [kpChat, kpCoord, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
      Matrix.cons_val_zero', Matrix.cons_val_succ']
    try field_simp
    try ring

/-- `Λ = 5⁹u¹²w³`, clearing the denominators of the Weierstrass coefficients. -/
def kpLambdaF (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  5 ^(9:ℕ) * (kpUF K u L) ^(12:ℕ) * (kpWF K u L) ^(3:ℕ)

/-- `Λ·a₁`. -/
def kpAhat1F (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  -(5 ^(8:ℕ)) * (kpUF K u L) ^(10:ℕ) * (kpWF K u L) ^(3:ℕ) * (3 * (kpUF K u L) ^(5:ℕ) + 1)

/-- `Λ·a₂`. -/
def kpAhat2F (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  -(5 ^(6:ℕ)) * (kpUF K u L) ^(8:ℕ) * (kpWF K u L) ^(2:ℕ) *
    (29 * (kpUF K u L) ^(15:ℕ) + 59 * (kpUF K u L) ^(10:ℕ) + 63 * (kpUF K u L) ^(5:ℕ) - 3)

/-- `Λ·a₃`. -/
def kpAhat3F (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  5 ^(5:ℕ) * (kpUF K u L) ^(6:ℕ) * (kpWF K u L) ^(2:ℕ) * (kpDF K u L) ^(2:ℕ)

/-- `Λ·a₄`. -/
def kpAhat4F (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  5 ^(3:ℕ) * (kpUF K u L) ^(4:ℕ) * (kpWF K u L) * (kpDF K u L) ^(2:ℕ) *
    (27 * (kpUF K u L) ^(10:ℕ) + 28 * (kpUF K u L) ^(5:ℕ) - 2)

/-- `Λ·a₆`. -/
def kpAhat6F (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  -(7 * (kpUF K u L) ^(5:ℕ) - 1) * (kpDF K u L) ^(4:ℕ)

/-- `Λ·W`, the cleared Weierstrass relation. -/
def kpWhatF (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  kpLambdaF K u L * (kpY K u L) ^(2:ℕ) + kpAhat1F K u L * kpX K u L * kpY K u L
    + kpAhat3F K u L * kpY K u L
    - (kpLambdaF K u L * (kpX K u L) ^(3:ℕ) + kpAhat2F K u L * (kpX K u L) ^(2:ℕ)
        + kpAhat4F K u L * kpX K u L + kpAhat6F K u L)

/-- The left hand side of the Weierstrass relation of the parametric model, in the function
field. -/
def kpWrel (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  (kpY K u L) ^(2:ℕ) + algebraMap K (kpFF K u L) (kpA1 K u) * kpX K u L * kpY K u L
    + algebraMap K (kpFF K u L) (kpA3 K u) * kpY K u L
    - ((kpX K u L) ^(3:ℕ) + algebraMap K (kpFF K u L) (kpA2 K u) * (kpX K u L) ^(2:ℕ)
        + algebraMap K (kpFF K u L) (kpA4 K u) * kpX K u L
        + algebraMap K (kpFF K u L) (kpA6 K u))

/-- The Weierstrass relation of the parametric model in the function field (equality form). -/
lemma kpRel (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] :
    (kpY K u L) ^(2:ℕ) + algebraMap K (kpFF K u L) (kpA1 K u) * kpX K u L * kpY K u L
      + algebraMap K (kpFF K u L) (kpA3 K u) * kpY K u L
      = (kpX K u L) ^(3:ℕ) + algebraMap K (kpFF K u L) (kpA2 K u) * (kpX K u L) ^(2:ℕ)
      + algebraMap K (kpFF K u L) (kpA4 K u) * kpX K u L
      + algebraMap K (kpFF K u L) (kpA6 K u) := by
  have h := Work.MotC2.genX_genY_relation ((kpData K u).E.baseChange L)
  rw [WeierstrassCurve.Affine.baseChange_a₁, WeierstrassCurve.Affine.baseChange_a₂,
    WeierstrassCurve.Affine.baseChange_a₃, WeierstrassCurve.Affine.baseChange_a₄,
    WeierstrassCurve.Affine.baseChange_a₆] at h
  rw [show (kpData K u).E.a₁ = kpA1 K u from rfl,
    show (kpData K u).E.a₂ = kpA2 K u from rfl,
    show (kpData K u).E.a₃ = kpA3 K u from rfl,
    show (kpData K u).E.a₄ = kpA4 K u from rfl,
    show (kpData K u).E.a₆ = kpA6 K u from rfl] at h
  simp only [← IsScalarTower.algebraMap_apply K L (kpFF K u L)] at h
  simp only [kpX, kpY]
  exact h

/-- The Weierstrass relation, as `kpWrel = 0`. -/
lemma kpWrel_eq_zero (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] :
    kpWrel K u L = 0 := by
  have h := kpRel K u L
  rw [kpWrel]
  rw [sub_eq_zero]
  exact h

/-- The quotient `w·Q_0`. -/
def kpQhat0 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  -((kpUF K u L) ^(42:ℕ) * (kpDF K u L) * (4 * (kpUF K u L) ^(15:ℕ) - 41 * (kpUF K u L) ^(10:ℕ)
        - 37 * (kpUF K u L) ^(5:ℕ) - 3) * 11920928955078125)
    - (kpUF K u L) ^(42:ℕ) * (kpDF K u L) * (500 * (kpUF K u L) ^(9:ℕ) - 250 * (kpUF K u L) ^(4:ℕ))
        * (kpX K u L) * 11920928955078125

/-- The quotient `w·Q_1`. -/
def kpQhat1 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  -((kpUF K u L) ^(41:ℕ) * (kpDF K u L) * (7 * (kpUF K u L) ^(15:ℕ) - 78 * (kpUF K u L) ^(10:ℕ)
        + 4 * (kpUF K u L) ^(5:ℕ) + 1) * 11920928955078125)
    - (kpUF K u L) ^(41:ℕ) * (kpDF K u L) * (250 * (kpUF K u L) ^(9:ℕ) - 125 * (kpUF K u L) ^(4:ℕ))
        * (kpX K u L) * 11920928955078125

/-- The quotient `w·Q_2`. -/
def kpQhat2 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  -((kpUF K u L) ^(43:ℕ) * (kpDF K u L) * (3 * (kpUF K u L) ^(15:ℕ) - 37 * (kpUF K u L) ^(10:ℕ)
        + 41 * (kpUF K u L) ^(5:ℕ) + 4) * 11920928955078125)
    - (kpUF K u L) ^(43:ℕ) * (kpDF K u L) * (-250 * (kpUF K u L) ^(9:ℕ) + 125 * (kpUF K u L) ^(4:ℕ))
        * (kpX K u L) * 11920928955078125

/-- The quotient `w·Q_3`. -/
def kpQhat3 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  -((kpUF K u L) ^(43:ℕ) * (kpDF K u L) * (3 * (kpUF K u L) ^(15:ℕ) - 37 * (kpUF K u L) ^(10:ℕ)
        + 41 * (kpUF K u L) ^(5:ℕ) + 4) * 11920928955078125)
    - (kpUF K u L) ^(43:ℕ) * (kpDF K u L) * (-250 * (kpUF K u L) ^(9:ℕ) + 125 * (kpUF K u L) ^(4:ℕ))
        * (kpX K u L) * 11920928955078125

/-- The quotient `w·Q_4`. -/
def kpQhat4 (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] : kpFF K u L :=
  -((kpUF K u L) ^(41:ℕ) * (kpDF K u L) * (7 * (kpUF K u L) ^(15:ℕ) - 78 * (kpUF K u L) ^(10:ℕ)
        + 4 * (kpUF K u L) ^(5:ℕ) + 1) * 11920928955078125)
    - (kpUF K u L) ^(41:ℕ) * (kpDF K u L) * (250 * (kpUF K u L) ^(9:ℕ) - 125 * (kpUF K u L) ^(4:ℕ))
        * (kpX K u L) * 11920928955078125

/-- The quotient `w·Q_k`, as a `Fin 5`-indexed family. -/
def kpQhat (K : Type) [Field K] (u : K) (L : Type) [Field L] [Algebra K L] :
    Fin 5 → kpFF K u L :=
  fun k => if k = 0 then kpQhat0 K u L else
    if k = 1 then kpQhat1 K u L else
    if k = 2 then kpQhat2 K u L else
    if k = 3 then kpQhat3 K u L else kpQhat4 K u L

end
end Work.MotT
