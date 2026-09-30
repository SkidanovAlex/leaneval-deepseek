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

/- **The `x`-coefficients of `covAffine`, cleared of denominators and saturation cases.** -/
set_option maxHeartbeats 0 in
theorem covA10 : (∀ (a : Fin 48) (e : Fin 8) (r : Fin 4) (j : Fin 3),
    covS a e r * X10 (covB a e) r j - X10 a r j = satOf e j * (2 * covC a e r j)) := by decide

/- **The constant term of `covAffine`, cleared of denominators and saturation cases.** -/
set_option maxHeartbeats 0 in
theorem B10 : (∀ (a : Fin 48) (e : Fin 8) (r : Fin 4),
    covS a e r * (covb10 (covB a e) r - (X10 (covB a e) r 0 * latOf a e 0 + X10 (covB a e) r 1 * latOf a e 1 + X10 (covB a e) r 2 * latOf a e 2))
      - covb10 a r
    = -(satOf e 0 * (2 * covC a e r 0) * ((Work.Cusp.cubeCorner a 0 : ℤ) + 1)
        + satOf e 1 * (2 * covC a e r 1) * ((Work.Cusp.cubeCorner a 1 : ℤ) + 1)
        + satOf e 2 * (2 * covC a e r 2) * ((Work.Cusp.cubeCorner a 2 : ℤ) + 1))) := by decide

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
