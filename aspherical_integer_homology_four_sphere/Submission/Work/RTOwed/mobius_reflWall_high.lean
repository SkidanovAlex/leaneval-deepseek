import Mathlib
import Submission.Work.HypModel.Basic
import Submission.Work.HypModel.Lorentz
import Submission.Work.HypModel.lorentz_dHypOfUHS
import Submission.Work.HypModel.hypOfUHS_four_pos
import Submission.Work.HypModel.lorentz_hypOfUHS_self
import Submission.Work.HypModel.four_pos_of_lorentz_pair_neg
import Submission.Work.HypModel.hasFDerivAt_hypOfUHS
import Submission.Work.HypModel.hasFDerivAt_uhsOfHyp
import Submission.Work.HypModel.hypOfKlein_mem_upperSheet
import Submission.Work.HypModel.hypOfKlein_injOn
import Submission.Work.HypModel.hypOfKlein_kleinOfHyp
import Submission.Work.HypModel.hypOfKlein_diagonal
import Submission.Work.HypModel.hypOfKlein_segment_pos_combo
import Submission.Work.HypModel.hypOfUHS_injOn
import Submission.Work.HypModel.hypOfUHS_uhsOfHyp
import Submission.Work.HypModel.uhsOfHyp_three_pos
import Submission.Work.HypModel.isLorentzMat_uhsTranslation
import Submission.Work.HypModel.kleinOfHyp_hypOfKlein
import Submission.Work.HypModel.kleinOfHyp_mem_ball
import Submission.Work.HypModel.mobiusKlein_isometry
import Submission.Work.HypModel.mobiusKlein_mem
import Submission.Work.HypModel.mobiusKlein_mul
import Submission.Work.HypModel.mobius_contDiffOn
import Submission.Work.HypModel.uhsOfHyp_hypOfUHS
import Submission.Work.HypModel.mobius_isometry
import Submission.Work.HypModel.mobius_mul
import Submission.Work.HypModel.mobius_one
import Submission.Work.HypModel.mobius_uhsTranslation
import Submission.Work.HypModel.polarToUHS_isometry
import Submission.Work.HypModel.tangent_hypOfUHS
import Submission.Work.RTOwed.CuspRigid
import Submission.Work.RTOwed.mobius_reflWall

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `mobius_reflWall` for walls known only *high* in the upper half space model

`Work.RTOwed.mobius_reflWall` proves that a Lorentz matrix `A` which maps the *whole* vertical wall
`{z : z k = c}` of the upper half space model into the coordinate hyperplane `{y t = 0}` — i.e. the
hypothesis `hW` is available at every chart point of positive height — intertwines the reflection in
the wall with the reflection of the `t`-th coordinate.

For the applications one often knows the wall condition only on the *high* part of the wall, that is
for chart points with `z 3 ≥ 11/10` (the ceiling of the cusp collar).  This file shows that this
apparently weaker hypothesis suffices:

`mobius_reflWall_high`.

The mathematical point is that the proof of `mobius_reflWall` uses `hW` only through the *row
relation* `A (f3to5 t) j = A (f3to5 t) (f3to5 k) * wallDual k c j` (the `t`-th row of `A` is a
multiple of the Lorentz dual of the wall normal), which is obtained by evaluating `hW` on the wall
and comparing the coefficients of a quadratic polynomial in a horizontal coordinate.  That
computation is completely insensitive to the height at which it is performed: evaluating at the
fixed height `11/10` instead of at height `1` gives exactly the same row relation.  The row
relation in turn gives the wall condition at *every* positive height (the wall function
`P k + c P 3 - c P 4` vanishes on the wall), so `mobius_reflWall` becomes applicable.

## Main results

* `Work.RTOwed.hpt`, `hpt_poly` : the height `11/10` test points on the wall, and the quadratic
  relation they satisfy.
* `Work.RTOwed.high_rels`, `high_row_structure` : the row relation from the high hypothesis.
* `Work.RTOwed.wall_fun_hypOfUHS`, `mulVec_row` : the wall function vanishes on the wall, and the
  row relation computes the `t`-th coordinate of `A *ᵥ hypOfUHS z`.
* `Work.RTOwed.mobius_reflWall_high` : the target.
-/

noncomputable section

open Set Topology Function Matrix
open scoped Matrix

namespace Work.RTOwed

open Work.FoldInst

/-! ### The test points at height `11/10`

We evaluate the high wall hypothesis on the chart points which lie on the wall `{z k = c}`, whose
`i`-th coordinate is `s` (`i ≠ k`) and whose last coordinate is `11/10`. -/

/-- The chart point of height `11/10` with `k`-th coordinate `c`, `i`-th coordinate `s` and all
other horizontal coordinates `0`. -/
def hpt (k i : Fin 3) (c s : ℝ) : Work.HypModel.E4 :=
  !₂[ (if (0 : Fin 3) = k then c else if (0 : Fin 3) = i then s else 0),
      (if (1 : Fin 3) = k then c else if (1 : Fin 3) = i then s else 0),
      (if (2 : Fin 3) = k then c else if (2 : Fin 3) = i then s else 0),
      (11 / 10 : ℝ) ]

@[simp] lemma hpt_three (k i : Fin 3) (c s : ℝ) : hpt k i c s 3 = (11 / 10 : ℝ) := rfl

@[simp] lemma hpt_two (k i : Fin 3) (c s : ℝ) :
    hpt k i c s 2 = (if (2 : Fin 3) = k then c else if (2 : Fin 3) = i then s else 0) := rfl

@[simp] lemma hpt_one (k i : Fin 3) (c s : ℝ) :
    hpt k i c s 1 = (if (1 : Fin 3) = k then c else if (1 : Fin 3) = i then s else 0) := rfl

@[simp] lemma hpt_zero (k i : Fin 3) (c s : ℝ) :
    hpt k i c s 0 = (if (0 : Fin 3) = k then c else if (0 : Fin 3) = i then s else 0) := rfl

/-- The `k`-th coordinate of `hpt k i c s` is `c`. -/
lemma hpt_coord_k (k i : Fin 3) (c s : ℝ) (hi : i ≠ k) : hpt k i c s (f3to4 k) = c := by
  fin_cases k <;> fin_cases i <;> simp_all [hpt]

/-- The squared Euclidean norm of `hpt k i c s` is `c² + s² + (11/10)²`. -/
lemma norm_sq_hpt (k i : Fin 3) (c s : ℝ) (hi : i ≠ k) :
    ‖hpt k i c s‖ ^ 2 = c ^ 2 + s ^ 2 + (11 / 10 : ℝ) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four]
  simp only [Real.norm_eq_abs, sq_abs, hpt]
  fin_cases k <;> fin_cases i <;> simp_all <;> ring

/-! ### The quadratic relation on the wall -/

/-- Clearing the denominators of `hypOfUHS`: for `z 3 ≠ 0` the value of the `t`-th coordinate of
`A *ᵥ hypOfUHS z` times `2 z 3` is a polynomial in the coordinates of `z` (the Lorentz pairing is
`A (f3to5 t) 0 * z 0 + A (f3to5 t) 1 * z 1 + A (f3to5 t) 2 * z 2`). -/
lemma key_expand (A : Matrix (Fin 5) (Fin 5) ℝ) (z : Work.HypModel.E4) (hz : z 3 ≠ 0)
    (t : Fin 3) :
    2 * z 3 * ((A *ᵥ Work.HypModel.hypOfUHS z) (f3to5 t))
      = 2 * (A (f3to5 t) 0 * z 0 + A (f3to5 t) 1 * z 1 + A (f3to5 t) 2 * z 2)
        + A (f3to5 t) 3 * (‖z‖ ^ 2 - 1) + A (f3to5 t) 4 * (‖z‖ ^ 2 + 1) := by
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_five]
  simp only [Work.HypModel.hypOfUHS_apply_zero, Work.HypModel.hypOfUHS_apply_one,
    Work.HypModel.hypOfUHS_apply_two, Work.HypModel.hypOfUHS_apply_three,
    Work.HypModel.hypOfUHS_apply_four]
  field_simp

/-- **The quadratic relation on the wall.**  If the high wall hypothesis holds, then for every
`i ≠ k` the test points `hpt k i c s` satisfy, for all `s`,

`A (f3to5 t) (f3to5 k) * 2c + A (f3to5 t) (f3to5 i) * 2s
   + A (f3to5 t) 3 * (c² + s² + (11/10)² - 1) + A (f3to5 t) 4 * (c² + s² + (11/10)² + 1) = 0`.

This is a quadratic polynomial in `s` with leading coefficient `A (f3to5 t) 3 + A (f3to5 t) 4`,
linear coefficient `2 * A (f3to5 t) (f3to5 i)` and constant term coming from `s = 0`. -/
lemma hpt_poly {A : Matrix (Fin 5) (Fin 5) ℝ} (k t : Fin 3) (c : ℝ)
    (hW : ∀ z : Work.HypModel.E4, 11 / 10 ≤ z 3 → z (f3to4 k) = c →
      A.mulVec (Work.HypModel.hypOfUHS z) (f3to5 t) = 0)
    (i : Fin 3) (hi : i ≠ k) (s : ℝ) :
    A (f3to5 t) (f3to5 k) * (2 * c) + A (f3to5 t) (f3to5 i) * (2 * s)
      + A (f3to5 t) 3 * (c ^ 2 + s ^ 2 + (11 / 10 : ℝ) ^ 2 - 1)
      + A (f3to5 t) 4 * (c ^ 2 + s ^ 2 + (11 / 10 : ℝ) ^ 2 + 1) = 0 := by
  have hz : (hpt k i c s) 3 ≠ 0 := by rw [hpt_three]; norm_num
  have h2 : (11 / 10 : ℝ) ≤ (hpt k i c s) 3 := by rw [hpt_three]
  have h3 : (hpt k i c s) (f3to4 k) = c := hpt_coord_k k i c s hi
  have h := hW (hpt k i c s) h2 h3
  have hexp := key_expand A (hpt k i c s) hz t
  rw [h, mul_zero, norm_sq_hpt k i c s hi, hpt_zero, hpt_one, hpt_two] at hexp
  fin_cases k <;> fin_cases i
  all_goals try (exfalso; exact hi rfl)
  all_goals (simp at hexp ⊢; linarith)

/-! ### The row relation -/

/-- **The three relations forced by the high wall hypothesis.**  For `i ≠ k`, comparing the values
of the quadratic relation `hpt_poly` at `s = 1, -1, 0` gives

`A (f3to5 t) (f3to5 i) = 0`, `A (f3to5 t) 3 + A (f3to5 t) 4 = 0`, `A (f3to5 t) 3 = c * A (f3to5 t) (f3to5 k)`. -/
lemma high_rels {A : Matrix (Fin 5) (Fin 5) ℝ} (k t : Fin 3) (c : ℝ)
    (hW : ∀ z : Work.HypModel.E4, 11 / 10 ≤ z 3 → z (f3to4 k) = c →
      A.mulVec (Work.HypModel.hypOfUHS z) (f3to5 t) = 0)
    (i : Fin 3) (hi : i ≠ k) :
    A (f3to5 t) (f3to5 i) = 0 ∧ A (f3to5 t) 3 + A (f3to5 t) 4 = 0 ∧
      A (f3to5 t) 3 = c * A (f3to5 t) (f3to5 k) := by
  have e1 := hpt_poly k t c hW i hi 1
  have e2 := hpt_poly k t c hW i hi (-1)
  have e0 := hpt_poly k t c hW i hi 0
  have hi0 : A (f3to5 t) (f3to5 i) = 0 := by linarith
  have h34 : A (f3to5 t) 3 + A (f3to5 t) 4 = 0 := by linarith
  have h3 : A (f3to5 t) 3 = c * A (f3to5 t) (f3to5 k) := by nlinarith
  exact ⟨hi0, h34, h3⟩

/-- **The row relation from the high wall hypothesis.**  The `t`-th row of `A` is a multiple
`lam = A (f3to5 t) (f3to5 k)` of the Lorentz dual `wallDual k c` of the wall normal — exactly as in
`Work.RTOwed.wall_row_structure`, but with the hypothesis `hW` only available at height `≥ 11/10`. -/
lemma high_row_structure {A : Matrix (Fin 5) (Fin 5) ℝ} (k t : Fin 3) (c : ℝ)
    (hW : ∀ z : Work.HypModel.E4, 11 / 10 ≤ z 3 → z (f3to4 k) = c →
      A.mulVec (Work.HypModel.hypOfUHS z) (f3to5 t) = 0) (j : Fin 5) :
    A (f3to5 t) j = A (f3to5 t) (f3to5 k) * wallDual k c j := by
  have rel : ∀ i : Fin 3, i ≠ k →
      A (f3to5 t) (f3to5 i) = 0 ∧ A (f3to5 t) 3 + A (f3to5 t) 4 = 0 ∧
        A (f3to5 t) 3 = c * A (f3to5 t) (f3to5 k) :=
    fun i hi => high_rels k t c hW i hi
  fin_cases k
  · have r1 := rel 1 (by decide +kernel)
    have r2 := rel 2 (by decide +kernel)
    have h1 : A (f3to5 t) 1 = 0 := by simpa using r1.1
    have h2 : A (f3to5 t) 2 = 0 := by simpa using r2.1
    have h34 : A (f3to5 t) 3 + A (f3to5 t) 4 = 0 := r1.2.1
    have h3 : A (f3to5 t) 3 = c * A (f3to5 t) 0 := by simpa using r1.2.2
    have key : ∀ j : Fin 5, A (f3to5 t) j = A (f3to5 t) 0 * wallDual 0 c j := by
      intro j
      fin_cases j <;> simp [wallDual] <;> linarith
    simpa using key j
  · have r1 := rel 0 (by decide +kernel)
    have r2 := rel 2 (by decide +kernel)
    have h0 : A (f3to5 t) 0 = 0 := by simpa using r1.1
    have h2 : A (f3to5 t) 2 = 0 := by simpa using r2.1
    have h34 : A (f3to5 t) 3 + A (f3to5 t) 4 = 0 := r1.2.1
    have h3 : A (f3to5 t) 3 = c * A (f3to5 t) 1 := by simpa using r1.2.2
    have key : ∀ j : Fin 5, A (f3to5 t) j = A (f3to5 t) 1 * wallDual 1 c j := by
      intro j
      fin_cases j <;> simp [wallDual] <;> linarith
    simpa using key j
  · have r1 := rel 0 (by decide +kernel)
    have r2 := rel 1 (by decide +kernel)
    have h0 : A (f3to5 t) 0 = 0 := by simpa using r1.1
    have h1 : A (f3to5 t) 1 = 0 := by simpa using r2.1
    have h34 : A (f3to5 t) 3 + A (f3to5 t) 4 = 0 := r1.2.1
    have h3 : A (f3to5 t) 3 = c * A (f3to5 t) 2 := by simpa using r1.2.2
    have key : ∀ j : Fin 5, A (f3to5 t) j = A (f3to5 t) 2 * wallDual 2 c j := by
      intro j
      fin_cases j <;> simp [wallDual] <;> linarith
    simpa using key j

/-! ### From the row relation back to the wall condition at every positive height -/

/-- The Lorentz lift of a chart point is `z (f3to4 k) / z 3` in the `k`-th coordinate. -/
lemma hypOfUHS_f3to5 (k : Fin 3) (z : Work.HypModel.E4) :
    (Work.HypModel.hypOfUHS z) (f3to5 k) = z (f3to4 k) / z 3 := by
  fin_cases k <;> simp [f3to5]

/-- **The wall function vanishes on the wall.**  For a chart point with `z k = c` and `z 3 ≠ 0` the
Lorentz pairing with the wall normal vanishes: `⟨n_{k,c}, Π(z)⟩ = z k - c = 0`. -/
lemma wall_fun_hypOfUHS (k : Fin 3) (c : ℝ) (z : Work.HypModel.E4) (hz : z 3 ≠ 0)
    (hzk : z (f3to4 k) = c) :
    (Work.HypModel.hypOfUHS z) (f3to5 k) + c * (Work.HypModel.hypOfUHS z) 3
      - c * (Work.HypModel.hypOfUHS z) 4 = 0 := by
  rw [hypOfUHS_f3to5, hzk, Work.HypModel.hypOfUHS_apply_three, Work.HypModel.hypOfUHS_apply_four]
  field_simp
  ring

/-- The row relation computes the `t`-th coordinate of `A *ᵥ P`: it is `lam` times the wall
function `P k + c P 3 - c P 4` of `P`. -/
lemma mulVec_row {A : Matrix (Fin 5) (Fin 5) ℝ} (k t : Fin 3) (c : ℝ)
    (hrow : ∀ j : Fin 5, A (f3to5 t) j = A (f3to5 t) (f3to5 k) * wallDual k c j)
    (P : Work.HypModel.V5) :
    (A *ᵥ P) (f3to5 t) = A (f3to5 t) (f3to5 k) * (P (f3to5 k) + c * P 3 - c * P 4) := by
  have hsum : (A *ᵥ P) (f3to5 t) = ∑ j : Fin 5, A (f3to5 t) j * P j := by
    simp [Matrix.mulVec, dotProduct]
  rw [hsum]
  rw [show (∑ j : Fin 5, A (f3to5 t) j * P j)
      = ∑ j : Fin 5, A (f3to5 t) (f3to5 k) * (wallDual k c j * P j) from
    Finset.sum_congr rfl (fun j _ => by rw [hrow j]; ring)]
  rw [← Finset.mul_sum]
  rw [show (∑ j : Fin 5, wallDual k c j * P j) = wallDual k c ⬝ᵥ P from rfl]
  rw [wallDual_dotProduct]

/-! ### The main theorem -/

theorem mobius_reflWall_high {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : Work.HypModel.IsLorentzMat A)
    (k t : Fin 3) (c : ℝ)
    (hW : ∀ z : Work.HypModel.E4, 11 / 10 ≤ z 3 → z (Work.FoldInst.f3to4 k) = c →
      Matrix.mulVec A (Work.HypModel.hypOfUHS z) (Work.FoldInst.f3to5 t) = 0) :
    ∀ z : Work.HypModel.E4, 0 < z 3 →
      Work.HypModel.mobius A (Work.RTOwed.reflWall4 k c z)
        = Work.RTOwed.reflCoord t (Work.HypModel.mobius A z) := by
  intro z hz
  -- The high hypothesis forces the row relation, which makes the wall condition available at every
  -- positive height, so `mobius_reflWall` applies.
  refine mobius_reflWall hA k t c ?_ z hz
  intro w hw hwk
  have hrow := high_row_structure k t c hW
  rw [mulVec_row k t c hrow (Work.HypModel.hypOfUHS w),
    wall_fun_hypOfUHS k c w (ne_of_gt hw) hwk, mul_zero]

end Work.RTOwed
