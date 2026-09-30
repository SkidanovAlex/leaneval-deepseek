import Mathlib
import Submission.Work.Cusp.WedgeSCone
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `uPerim` is the angular parameter of the cone spanned by the two points `θ`, `θ + 1/4`

For `0 ≤ θ < 1/4` the perimeter parameter `uPerim` of the boundary `∂Sq = {q | nrm q = 1}` of the
square runs from `0` at `(1,1)`.  The two points

* `A = !₂[1, 1 - 8θ] = bndOfU θ` (on the right edge `q 0 = 1`), and
* `B = !₂[1 - 8θ, -1] = bndOfU (θ + 1/4) = rot90 A` (on the bottom edge `q 1 = -1`)

cut out the open quarter-arc `uPerim ∈ (θ, θ + 1/4)`.  This module identifies that arc with the
open cone spanned by `A` and `B`: a boundary point `q` lies in `wedgeCone A B` (i.e. in the open
cone of positive combinations of `A` and `B`) exactly when its perimeter parameter lies strictly
between `θ` and `θ + 1/4`.

Both conditions are homogeneous in the direction of `q`, so only the four edges of `Sq` are
relevant; on the right edge the cone membership is `0 < 1 + t*q₁ ∧ q₁ < t` and the arc condition
is `t - 2 < q₁ < t` (`t = 1 - 8θ`), which agree, and on the bottom edge both are `t < q₀`.  On the
two remaining edges both conditions are false.
-/

noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-- **Positivity of `1 + t·y` on the range of a coordinate.**  For `t ∈ (-1,1]` and `y ∈ [-1,1]`
the inequality `0 < 1 + t*y` is equivalent to `t - 2 < y`.  The two possible failure modes are
`t = 1, y = -1` (where `1 + t*y = 0`) and the automatic region `y = -1`, `t < 1`. -/
private lemma one_add_mul_pos_iff {t y : ℝ} (ht1 : -1 < t) (ht2 : t ≤ 1)
    (hy1 : -1 ≤ y) (hy2 : y ≤ 1) : 0 < 1 + t * y ↔ t - 2 < y := by
  constructor
  · intro h; nlinarith [sq_nonneg (t - 1), sq_nonneg (y + 1)]
  · intro h; nlinarith [sq_nonneg (t + 1), sq_nonneg (y - 1)]

/-- For `t ∈ (-1,1]` and `|y| ≤ 1` the product `t*y` is at most `1`; this is what rules out the
cone on the two edges of `Sq` opposite the arc. -/
private lemma tmul_le_one {t y : ℝ} (ht1 : -1 < t) (ht2 : t ≤ 1) (hy : |y| ≤ 1) :
    t * y ≤ 1 := by
  nlinarith [abs_le.mp hy, sq_nonneg t, sq_nonneg y]

theorem geo_quarter (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1/4) {q : E2} (hq : nrm q = 1) :
    q ∈ wedgeCone !₂[(1 : ℝ), 1 - 8 * θ] !₂[1 - 8 * θ, (-1 : ℝ)] ↔
      uPerim q ∈ Set.Ioo θ (θ + 1/4) := by
  set t : ℝ := 1 - 8 * θ with ht
  have ht1 : -1 < t := by rw [ht]; linarith
  have ht2 : t ≤ 1 := by rw [ht]; linarith
  have hqmax : max |q 0| |q 1| = 1 := by unfold nrm at hq; exact hq
  have hq0abs : |q 0| ≤ 1 := hqmax ▸ le_max_left |q 0| |q 1|
  have hq1abs : |q 1| ≤ 1 := hqmax ▸ le_max_right |q 0| |q 1|
  have hq0le : q 0 ≤ 1 := (abs_le.mp hq0abs).2
  have hq0ge : -1 ≤ q 0 := (abs_le.mp hq0abs).1
  have hq1le : q 1 ≤ 1 := (abs_le.mp hq1abs).2
  have hq1ge : -1 ≤ q 1 := (abs_le.mp hq1abs).1
  -- The cone of `!₂[1,t]` and `!₂[t,-1]` is the set `0 < q₀ + t*q₁ ∧ q₁ < t*q₀`.
  have hcone : q ∈ wedgeCone !₂[(1 : ℝ), t] !₂[t, (-1 : ℝ)] ↔
      0 < q 0 + t * q 1 ∧ q 1 < t * q 0 := by
    simp only [wedgeCone, Set.mem_ofPred_eq, cross, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> intro h <;> constructor <;> nlinarith [sq_nonneg t]
  by_cases hA : q 0 = 1
  · -- right edge: `uPerim q = (1 - q₁)/8`
    have hu : uPerim q = (1 - q 1) / 8 := by rw [uPerim, ite_eq_left hA]
    rw [hcone, hu, Set.mem_Ioo, hA]
    simp only [mul_one]
    have hL : (0 < 1 + t * q 1) ↔ t - 2 < q 1 := one_add_mul_pos_iff ht1 ht2 hq1ge hq1le
    have hR1 : (θ < (1 - q 1) / 8) ↔ q 1 < t := by
      rw [ht]; constructor <;> intro h <;> linarith
    have hR2 : ((1 - q 1) / 8 < θ + 1/4) ↔ t - 2 < q 1 := by
      rw [ht]; constructor <;> intro h <;> linarith
    rw [hL, hR1, hR2]
    tauto
  · by_cases hB : q 1 = -1
    · -- bottom edge: `uPerim q = (3 - q₀)/8`
      have hu : uPerim q = (3 - q 0) / 8 := by rw [uPerim, ite_eq_right hA, ite_eq_left hB]
      rw [hcone, hu, Set.mem_Ioo, hB]
      have hL : (0 < q 0 + t * (-1) ∧ -1 < t * q 0) ↔ t < q 0 := by
        constructor
        · intro h; linarith [h.1]
        · intro h
          exact ⟨by linarith, by nlinarith [sq_nonneg t, sq_nonneg (q 0 - 1), hq0le]⟩
      have hR : (θ < (3 - q 0) / 8 ∧ (3 - q 0) / 8 < θ + 1/4) ↔ t < q 0 := by
        constructor
        · intro h; linarith [h.2]
        · intro h
          exact ⟨by linarith, by linarith⟩
      rw [hL, hR]
    · by_cases hC : q 0 = -1
      · -- left edge: both conditions are false
        have hu : uPerim q = (5 + q 1) / 8 :=
          by rw [uPerim, ite_eq_right hA, ite_eq_right hB, ite_eq_left hC]
        rw [hcone, hu, Set.mem_Ioo, hC]
        have hQ : ¬ (θ < (5 + q 1) / 8 ∧ (5 + q 1) / 8 < θ + 1/4) := by
          intro h; linarith [h.2, hq1ge, h1]
        have hP : ¬ (0 < -1 + t * q 1 ∧ q 1 < t * (-1)) := by
          intro h; have := tmul_le_one ht1 ht2 hq1abs; linarith [h.1]
        exact ⟨fun h => (hP h).elim, fun h => (hQ h).elim⟩
      · -- top edge `q 1 = 1`: both conditions are false
        have hq1eq : q 1 = 1 := by
          have hq0lt : |q 0| < 1 := by
            rcases lt_or_eq_of_le hq0abs with hh | hh
            · exact hh
            · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hh with h2 | h2
              · exact absurd h2 hA
              · exact absurd h2 hC
          have hq1abs_eq : |q 1| = 1 := by
            rcases lt_or_eq_of_le (hqmax ▸ le_max_right |q 0| |q 1|) with hh | hh
            · exfalso; have : max |q 0| |q 1| < 1 := max_lt hq0lt hh; linarith
            · exact hh
          rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hq1abs_eq with h2 | h2
          · exact h2
          · exact absurd h2 hB
        have hu : uPerim q = (7 + q 0) / 8 :=
          by rw [uPerim, ite_eq_right hA, ite_eq_right hB, ite_eq_right hC]
        rw [hcone, hu, Set.mem_Ioo, hq1eq]
        simp only [mul_one]
        have hQ : ¬ (θ < (7 + q 0) / 8 ∧ (7 + q 0) / 8 < θ + 1/4) := by
          intro h; linarith [h.2, hq0ge, h1]
        have hP : ¬ (0 < q 0 + t ∧ 1 < t * q 0) := by
          intro h; have := tmul_le_one ht1 ht2 hq0abs; linarith [h.2]
        exact ⟨fun h => (hP h).elim, fun h => (hQ h).elim⟩

end Work.Cusp
