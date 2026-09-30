import Mathlib
import Submission.Work.RTOwed.cuspCert.tsetCoverData

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-
# The affine certificate `covAffine` for the cover of the truncation set

For every cube `a : Fin 48`, saturation pattern `e : Fin 8` and coordinate `r : Fin 4` the affine
function
`x ↦ covS a e r * kleinPt (covB a e) (zOf a e x) r − kleinPt a x r`
is the expansion, over the saturated coordinates, of the coefficient table `covC`:

  `covS a e r * kleinPt (covB a e) (zOf a e x) r − kleinPt a x r
     = ∑ i, (if satOf e i = 1 then covC a e r i / 5 else 0) * (x i − (cubeCorner a i + 1))`.

This is a finite identity of tables.  Instead of unfolding the four huge tables `covB`, `covK`,
`covS`, `covC` in each of the `48 · 8 · 4 = 1536` instances (which the elaborator cannot afford),
we verify it in *cleared form over `ℤ`*: `X10` and `covb10` are the integer tables `10 * cubeXToKlein`
and `10 * cubeXToKleinb`, and the two table identities `covA10` (`x`-coefficients) and `B10`
(constant term) are decidable statements about them which the kernel checks outright.  The whole
statement then follows by pure `ring` reasoning from those two identities, the bridge lemmas
`X10_cast_R`, `b10_cast_R` between the integer and rational tables, and the elementary fact
`satOf e i ∈ {0, 1}`.
-/

namespace Work.RTOwed.cuspCert

open scoped BigOperators

/-- `10` times the rational table `Work.Cusp.cubeXToKlein` (an integer table, all its entries are
multiples of `1/10`): the `x`-coefficients of the Klein map, cleared of denominators. -/
def X10 : Fin 48 → Fin 4 → Fin 3 → ℤ := ![
  ![![0, 0, 0], ![-4, 0, 0], ![0, -4, 0], ![0, 0, -4]],
  ![![0, 0, 0], ![4, 0, 0], ![0, -4, 0], ![0, 0, -4]],
  ![![0, 0, 0], ![4, 0, 0], ![0, 4, 0], ![0, 0, -4]],
  ![![0, 0, 0], ![-4, 0, 0], ![0, 4, 0], ![0, 0, -4]],
  ![![-4, 0, 0], ![0, 0, 0], ![0, -4, 0], ![0, 0, -4]],
  ![![4, 0, 0], ![0, 0, 0], ![0, -4, 0], ![0, 0, 4]],
  ![![-4, 0, 0], ![0, 0, 0], ![0, -4, 0], ![0, 0, 4]],
  ![![4, 0, 0], ![0, 0, 0], ![0, -4, 0], ![0, 0, -4]],
  ![![-4, 0, 0], ![0, -4, 0], ![0, 0, 0], ![0, 0, -4]],
  ![![4, 0, 0], ![0, -4, 0], ![0, 0, 0], ![0, 0, -4]],
  ![![4, 0, 0], ![0, -4, 0], ![0, 0, 0], ![0, 0, 4]],
  ![![-4, 0, 0], ![0, -4, 0], ![0, 0, 0], ![0, 0, 4]],
  ![![-4, 0, 0], ![0, -4, 0], ![0, 0, -4], ![0, 0, 0]],
  ![![-4, 0, 0], ![0, 4, 0], ![0, 0, 4], ![0, 0, 0]],
  ![![-4, 0, 0], ![0, -4, 0], ![0, 0, 4], ![0, 0, 0]],
  ![![-4, 0, 0], ![0, 4, 0], ![0, 0, -4], ![0, 0, 0]],
  ![![2, 2, -2], ![2, -2, 2], ![-2, 2, 2], ![-2, -2, -2]],
  ![![2, -2, 2], ![-2, -2, 2], ![2, 2, 2], ![2, -2, -2]],
  ![![2, -2, -2], ![2, 2, 2], ![2, 2, -2], ![-2, 2, -2]],
  ![![-2, -2, -2], ![-2, 2, 2], ![2, -2, 2], ![2, 2, -2]],
  ![![2, -2, -2], ![-2, -2, -2], ![-2, -2, 2], ![-2, 2, -2]],
  ![![-2, 2, -2], ![-2, -2, 2], ![2, 2, 2], ![-2, 2, 2]],
  ![![2, 2, 2], ![-2, 2, 2], ![-2, 2, -2], ![2, 2, -2]],
  ![![-2, 2, 2], ![2, 2, 2], ![-2, -2, 2], ![-2, 2, -2]],
  ![![2, 2, 2], ![2, -2, -2], ![2, -2, 2], ![2, 2, -2]],
  ![![-2, -2, 2], ![2, -2, 2], ![-2, 2, 2], ![2, 2, 2]],
  ![![-2, 2, -2], ![-2, -2, 2], ![-2, -2, -2], ![2, -2, -2]],
  ![![2, 2, -2], ![-2, 2, -2], ![2, -2, -2], ![-2, -2, -2]],
  ![![-2, -2, -2], ![-2, 2, 2], ![-2, 2, -2], ![-2, -2, 2]],
  ![![-2, 2, -2], ![2, 2, -2], ![2, 2, 2], ![2, -2, -2]],
  ![![2, -2, -2], ![2, 2, 2], ![-2, -2, 2], ![2, -2, 2]],
  ![![-2, -2, -2], ![2, -2, -2], ![2, -2, 2], ![-2, -2, 2]],
  ![![-2, -2, 2], ![2, -2, 2], ![2, -2, -2], ![-2, -2, -2]],
  ![![2, -2, 2], ![2, 2, -2], ![-2, -2, -2], ![2, -2, -2]],
  ![![-2, 2, 2], ![2, 2, 2], ![2, 2, -2], ![2, -2, 2]],
  ![![-2, -2, 2], ![-2, 2, -2], ![-2, 2, 2], ![-2, -2, -2]],
  ![![2, 2, 2], ![-2, 2, 2], ![2, -2, 2], ![-2, -2, 2]],
  ![![-2, 2, 2], ![-2, -2, -2], ![-2, -2, 2], ![2, -2, 2]],
  ![![-2, -2, -2], ![2, -2, -2], ![-2, 2, -2], ![2, 2, -2]],
  ![![2, 2, -2], ![2, -2, 2], ![2, -2, -2], ![2, 2, 2]],
  ![![-2, 2, -2], ![2, 2, -2], ![-2, -2, -2], ![-2, 2, 2]],
  ![![2, 2, -2], ![-2, 2, -2], ![-2, 2, 2], ![2, 2, 2]],
  ![![-2, 2, 2], ![-2, -2, -2], ![2, 2, -2], ![-2, 2, -2]],
  ![![2, -2, 2], ![-2, -2, 2], ![-2, -2, -2], ![-2, 2, 2]],
  ![![-2, -2, 2], ![-2, 2, -2], ![2, -2, -2], ![2, 2, 2]],
  ![![2, -2, 2], ![2, 2, -2], ![2, 2, 2], ![-2, 2, 2]],
  ![![2, -2, -2], ![-2, -2, -2], ![2, 2, -2], ![2, -2, 2]],
  ![![2, 2, 2], ![2, -2, -2], ![-2, 2, -2], ![-2, -2, 2]]
]


/-- `10` times the rational table `Work.Cusp.cubeXToKleinb` (an integer table): the translation
part of the Klein map, cleared of denominators. -/
def covb10 : Fin 48 → Fin 4 → ℤ := ![
  ![8, 2, 2, 2],
  ![-8, 2, 2, 2],
  ![-8, -2, -2, -2],
  ![8, -2, -2, -2],
  ![2, 8, 2, 2],
  ![-2, -8, -2, -2],
  ![2, -8, 2, 2],
  ![-2, 8, -2, 6],
  ![2, 2, 8, 2],
  ![2, 2, -8, 2],
  ![-2, -2, -8, -2],
  ![-2, -2, 8, -2],
  ![2, 2, 2, 8],
  ![-2, -2, -2, -8],
  ![2, 2, 2, -8],
  ![-2, -2, 6, 8],
  ![-5, -5, -5, -1],
  ![5, -5, -5, -1],
  ![-5, -5, 5, -1],
  ![5, 5, 5, 1],
  ![-1, 9, -1, -5],
  ![-1, -1, -9, 5],
  ![5, -5, 5, -1],
  ![-5, 5, 5, 1],
  ![1, 9, -1, -5],
  ![1, -1, -9, 5],
  ![5, 5, -5, 1],
  ![-1, 9, 1, -5],
  ![-1, -1, 9, 5],
  ![1, -9, 1, 5],
  ![1, 1, 9, -5],
  ![3, 5, -5, 9],
  ![-5, 5, -5, 1],
  ![1, 9, 1, -5],
  ![1, -1, 9, 5],
  ![-1, -9, 1, 5],
  ![-1, 1, 9, -5],
  ![-3, 5, -5, 9],
  ![1, -9, -1, 5],
  ![1, 1, -9, -5],
  ![3, 5, 5, 9],
  ![-3, -5, 5, -9],
  ![-1, -9, -1, 5],
  ![-1, 1, -9, -5],
  ![-3, 5, 5, 9],
  ![3, -5, 5, -9],
  ![-3, -5, -5, -9],
  ![3, -5, -5, -9]
]


/-- `satOf e i` is `0` or `1`. -/
theorem satOf_val (e : Fin 8) (i : Fin 3) : satOf e i = 0 ∨ satOf e i = 1 := by
  unfold satOf; split <;> simp

/-- The saturation factor, in multiplicative form: no `if` appears. -/
theorem satOf_mul (e : Fin 8) (i : Fin 3) (A : ℝ) :
    (satOf e i : ℝ) * A = (if satOf e i = 1 then A else 0) := by
  rcases satOf_val e i with h | h <;> simp [h]

/-- The `x`-coefficient identity of `covAffine` for the cube `a` (one cube `a` at a time, each a small kernel `decide`). -/
abbrev covA10Row (a : Fin 48) : Prop :=
  ∀ (e : Fin 8) (r : Fin 4) (j : Fin 3),
    covS a e r * X10 (covB a e) r j - X10 a r j = satOf e j * (2 * covC a e r j)

set_option maxHeartbeats 0 in
theorem covA10Row_0 : covA10Row 0 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_1 : covA10Row 1 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_2 : covA10Row 2 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_3 : covA10Row 3 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_4 : covA10Row 4 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_5 : covA10Row 5 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_6 : covA10Row 6 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_7 : covA10Row 7 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_8 : covA10Row 8 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_9 : covA10Row 9 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_10 : covA10Row 10 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_11 : covA10Row 11 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_12 : covA10Row 12 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_13 : covA10Row 13 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_14 : covA10Row 14 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_15 : covA10Row 15 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_16 : covA10Row 16 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_17 : covA10Row 17 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_18 : covA10Row 18 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_19 : covA10Row 19 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_20 : covA10Row 20 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_21 : covA10Row 21 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_22 : covA10Row 22 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_23 : covA10Row 23 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_24 : covA10Row 24 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_25 : covA10Row 25 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_26 : covA10Row 26 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_27 : covA10Row 27 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_28 : covA10Row 28 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_29 : covA10Row 29 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_30 : covA10Row 30 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_31 : covA10Row 31 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_32 : covA10Row 32 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_33 : covA10Row 33 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_34 : covA10Row 34 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_35 : covA10Row 35 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_36 : covA10Row 36 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_37 : covA10Row 37 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_38 : covA10Row 38 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_39 : covA10Row 39 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_40 : covA10Row 40 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_41 : covA10Row 41 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_42 : covA10Row 42 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_43 : covA10Row 43 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_44 : covA10Row 44 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_45 : covA10Row 45 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_46 : covA10Row 46 := by decide +kernel
set_option maxHeartbeats 0 in
theorem covA10Row_47 : covA10Row 47 := by decide +kernel

/- **The `x`-coefficients of `covAffine`, cleared of denominators and saturation cases.** -/
theorem covA10 : (∀ (a : Fin 48) (e : Fin 8) (r : Fin 4) (j : Fin 3),
    covS a e r * X10 (covB a e) r j - X10 a r j = satOf e j * (2 * covC a e r j)) := by
  intro a
  fin_cases a
  exacts [covA10Row_0, covA10Row_1, covA10Row_2, covA10Row_3, covA10Row_4, covA10Row_5, covA10Row_6, covA10Row_7, covA10Row_8, covA10Row_9, covA10Row_10, covA10Row_11, covA10Row_12, covA10Row_13, covA10Row_14, covA10Row_15, covA10Row_16, covA10Row_17, covA10Row_18, covA10Row_19, covA10Row_20, covA10Row_21, covA10Row_22, covA10Row_23, covA10Row_24, covA10Row_25, covA10Row_26, covA10Row_27, covA10Row_28, covA10Row_29, covA10Row_30, covA10Row_31, covA10Row_32, covA10Row_33, covA10Row_34, covA10Row_35, covA10Row_36, covA10Row_37, covA10Row_38, covA10Row_39, covA10Row_40, covA10Row_41, covA10Row_42, covA10Row_43, covA10Row_44, covA10Row_45, covA10Row_46, covA10Row_47]

/-- The constant-term identity of `covAffine` for the cube `a` (one cube `a` at a time, each a small kernel `decide`). -/
abbrev B10Row (a : Fin 48) : Prop :=
  ∀ (e : Fin 8) (r : Fin 4),
    covS a e r * (covb10 (covB a e) r - (X10 (covB a e) r 0 * latOf a e 0 + X10 (covB a e) r 1 * latOf a e 1 + X10 (covB a e) r 2 * latOf a e 2))
      - covb10 a r
    = -(satOf e 0 * (2 * covC a e r 0) * ((Work.Cusp.cubeCorner a 0 : ℤ) + 1)
        + satOf e 1 * (2 * covC a e r 1) * ((Work.Cusp.cubeCorner a 1 : ℤ) + 1)
        + satOf e 2 * (2 * covC a e r 2) * ((Work.Cusp.cubeCorner a 2 : ℤ) + 1))

set_option maxHeartbeats 0 in
theorem B10Row_0 : B10Row 0 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_1 : B10Row 1 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_2 : B10Row 2 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_3 : B10Row 3 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_4 : B10Row 4 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_5 : B10Row 5 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_6 : B10Row 6 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_7 : B10Row 7 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_8 : B10Row 8 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_9 : B10Row 9 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_10 : B10Row 10 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_11 : B10Row 11 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_12 : B10Row 12 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_13 : B10Row 13 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_14 : B10Row 14 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_15 : B10Row 15 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_16 : B10Row 16 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_17 : B10Row 17 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_18 : B10Row 18 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_19 : B10Row 19 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_20 : B10Row 20 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_21 : B10Row 21 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_22 : B10Row 22 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_23 : B10Row 23 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_24 : B10Row 24 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_25 : B10Row 25 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_26 : B10Row 26 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_27 : B10Row 27 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_28 : B10Row 28 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_29 : B10Row 29 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_30 : B10Row 30 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_31 : B10Row 31 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_32 : B10Row 32 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_33 : B10Row 33 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_34 : B10Row 34 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_35 : B10Row 35 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_36 : B10Row 36 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_37 : B10Row 37 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_38 : B10Row 38 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_39 : B10Row 39 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_40 : B10Row 40 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_41 : B10Row 41 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_42 : B10Row 42 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_43 : B10Row 43 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_44 : B10Row 44 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_45 : B10Row 45 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_46 : B10Row 46 := by decide +kernel
set_option maxHeartbeats 0 in
theorem B10Row_47 : B10Row 47 := by decide +kernel

/- **The constant term of `covAffine`, cleared of denominators and saturation cases.** -/
theorem B10 : (∀ (a : Fin 48) (e : Fin 8) (r : Fin 4),
    covS a e r * (covb10 (covB a e) r - (X10 (covB a e) r 0 * latOf a e 0 + X10 (covB a e) r 1 * latOf a e 1 + X10 (covB a e) r 2 * latOf a e 2))
      - covb10 a r
    = -(satOf e 0 * (2 * covC a e r 0) * ((Work.Cusp.cubeCorner a 0 : ℤ) + 1)
        + satOf e 1 * (2 * covC a e r 1) * ((Work.Cusp.cubeCorner a 1 : ℤ) + 1)
        + satOf e 2 * (2 * covC a e r 2) * ((Work.Cusp.cubeCorner a 2 : ℤ) + 1))) := by
  intro a
  fin_cases a
  exacts [B10Row_0, B10Row_1, B10Row_2, B10Row_3, B10Row_4, B10Row_5, B10Row_6, B10Row_7, B10Row_8, B10Row_9, B10Row_10, B10Row_11, B10Row_12, B10Row_13, B10Row_14, B10Row_15, B10Row_16, B10Row_17, B10Row_18, B10Row_19, B10Row_20, B10Row_21, B10Row_22, B10Row_23, B10Row_24, B10Row_25, B10Row_26, B10Row_27, B10Row_28, B10Row_29, B10Row_30, B10Row_31, B10Row_32, B10Row_33, B10Row_34, B10Row_35, B10Row_36, B10Row_37, B10Row_38, B10Row_39, B10Row_40, B10Row_41, B10Row_42, B10Row_43, B10Row_44, B10Row_45, B10Row_46, B10Row_47]

/- The integer table `X10` is `10` times the rational table `cubeXToKlein`. -/
set_option maxHeartbeats 0 in
theorem X10_cast_R (a : Fin 48) (r : Fin 4) (j : Fin 3) :
    ((X10 a r j : ℤ) : ℝ) = 10 * ((Work.Cusp.cubeXToKlein a r j : ℚ) : ℝ) := by
  fin_cases a <;> fin_cases r <;> fin_cases j <;>
    simp only [X10, Work.Cusp.cubeXToKlein, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/- The integer table `covb10` is `10` times the rational table `cubeXToKleinb`. -/
set_option maxHeartbeats 0 in
theorem b10_cast_R (a : Fin 48) (r : Fin 4) :
    ((covb10 a r : ℤ) : ℝ) = 10 * ((Work.Cusp.cubeXToKleinb a r : ℚ) : ℝ) := by
  fin_cases a <;> fin_cases r <;>
    simp only [covb10, Work.Cusp.cubeXToKleinb, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.cons_val_three] <;> norm_num

/-- The Klein map with the integer tables, i.e. `10` times the Klein map of the cube. -/
def kleinPtX (b : Fin 48) (y : CuspE3) : CuspE4 :=
  WithLp.toLp 2 fun i : Fin 4 => (∑ j : Fin 3, (X10 b i j : ℝ) * y j) + (covb10 b i : ℝ)

/-- **`kleinPtX` is `10` times `kleinPt`.** -/
theorem kleinPtX_eq (b : Fin 48) (y : CuspE3) (q : Fin 4) :
    kleinPtX b y q = 10 * Work.RTOwed.kleinPt b y q := by
  simp only [kleinPtX, Work.RTOwed.kleinPt, PiLp.toLp_apply, X10_cast_R, b10_cast_R]
  rw [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- **The affine certificate `covAffine`**: over the saturated coordinates the affine function
`x ↦ covS a e r * kleinPt (covB a e) (zOf a e x) r − kleinPt a x r` expands with the coefficients
`covC a e r · / 5`, the shift being `x i − (cubeCorner a i + 1)`. -/
theorem covAffine (a : Fin 48) (e : Fin 8) (x : Work.RTOwed.cuspCert.CuspE3) (r : Fin 4) :
    (Work.RTOwed.cuspCert.covS a e r : ℝ) *
        Work.RTOwed.kleinPt (Work.RTOwed.cuspCert.covB a e) (Work.RTOwed.cuspCert.zOf a e x) r
      - Work.RTOwed.kleinPt a x r
      = ∑ i : Fin 3, if Work.RTOwed.cuspCert.satOf e i = 1 then
          ((Work.RTOwed.cuspCert.covC a e r i : ℝ) / 5) *
            (x i - ((Work.Cusp.cubeCorner a i : ℝ) + 1)) else 0 := by
  have hkX : ∀ (b : Fin 48) (y : CuspE3) (q : Fin 4),
      kleinPtX b y q = (∑ j : Fin 3, (X10 b q j : ℝ) * y j) + (covb10 b q : ℝ) := by
    intro b y q; rfl
  have hz : ∀ j : Fin 3, (zOf a e x) j = x j - (latOf a e j : ℝ) := by
    intro j; rfl
  have hA : ∀ j : Fin 3,
      (covS a e r : ℝ) * (X10 (covB a e) r j : ℝ) - (X10 a r j : ℝ)
      = (satOf e j : ℝ) * (2 * (covC a e r j : ℝ)) := by
    intro j
    have h := congrArg (fun q : ℤ => (q : ℝ)) (covA10 a e r j)
    push_cast at h
    exact h
  have hB : (covS a e r : ℝ) *
        ((covb10 (covB a e) r : ℝ)
          - ((X10 (covB a e)) r 0 * (latOf a e 0 : ℝ)
            + (X10 (covB a e)) r 1 * (latOf a e 1 : ℝ)
            + (X10 (covB a e)) r 2 * (latOf a e 2 : ℝ)))
      - (covb10 a r : ℝ)
      = -((satOf e 0 : ℝ) * (2 * (covC a e r 0 : ℝ)) * ((Work.Cusp.cubeCorner a 0 : ℝ) + 1)
        + (satOf e 1 : ℝ) * (2 * (covC a e r 1 : ℝ)) * ((Work.Cusp.cubeCorner a 1 : ℝ) + 1)
        + (satOf e 2 : ℝ) * (2 * (covC a e r 2 : ℝ)) * ((Work.Cusp.cubeCorner a 2 : ℝ) + 1)) := by
    have h := congrArg (fun q : ℤ => (q : ℝ)) (B10 a e r)
    push_cast at h
    exact h
  have hmain : (covS a e r : ℝ) * kleinPtX (covB a e) (zOf a e x) r - kleinPtX a x r
      = ∑ i : Fin 3, (satOf e i : ℝ) * (2 * (covC a e r i : ℝ)) * (x i - ((Work.Cusp.cubeCorner a i : ℝ) + 1)) := by
    rw [hkX (covB a e) (zOf a e x) r, hkX a x r]
    simp only [hz, Fin.sum_univ_three]
    linear_combination (x 0) * (hA 0) + (x 1) * (hA 1) + (x 2) * (hA 2) + hB
  have hL : (covS a e r : ℝ) * Work.RTOwed.kleinPt (covB a e) (zOf a e x) r - Work.RTOwed.kleinPt a x r
      = (1/10) * ((covS a e r : ℝ) * kleinPtX (covB a e) (zOf a e x) r - kleinPtX a x r) := by
    rw [kleinPtX_eq (covB a e) (zOf a e x) r, kleinPtX_eq a x r]
    ring
  rw [hL, hmain, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← satOf_mul e i ((covC a e r i : ℝ) / 5 * (x i - ((Work.Cusp.cubeCorner a i : ℝ) + 1)))]
  ring

end Work.RTOwed.cuspCert
