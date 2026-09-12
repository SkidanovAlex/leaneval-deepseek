import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Field.Basic

/-!
Pure ℝ-algebra fact used by the flat-stop impossibility proof (NoFlatStop.lean):
a symmetric 2×2 matrix `[[a,b],[b,c]]` with zero determinant (hdet : ac = b²),
kernel containing the nonzero vector `(w0,w1)` (hk0, hk1: the two entries of
`M·(w0,w1)ᵀ` vanish), and which is not the zero matrix (hM), must evaluate the
quadratic form on the perpendicular vector `(−w1,w0)` to a NONZERO value:
`(−w1)²a + 2(−w1)(w0)b + w0²c ≠ 0`.  (Rank-one symmetric with kernel span(w):
M = λ·(v⊗v)/‖v‖², v = (−w1,w0), so vᵀMv = λ‖v‖² ≠ 0 when M ≠ 0 and w ≠ 0.)
Suggested proof (case split on hw): if w1 = 0 then hk0 gives a·w0 = 0, hk1
gives b·w0 = 0, and the evaluation is w0²·c, all zero unless w0 = 0, contradicting
hM; if w1 ≠ 0 and w0 ≠ 0 derive `b·(w0⁴ + 2·w0²·w1² + w1⁴) = 0` by multiplying
the evaluation by w0·w1 and substituting a·w0 = −b·w1 (hk0) and c·w1 = −b·w0
(hk1), then use `w0⁴+2w0²w1²+w1⁴ = (w0²+w1²)² ≠ 0` to get b = 0, whence a = c = 0
from hk0/hk1; handle w1 ≠ 0 ∧ w0 = 0 symmetrically.  Mind that `nlinarith`
cannot multiply an equality by a term or use b = 0 to rewrite b·w1 = 0, so
rewrite the substitutions in with `rw` before the final `nlinarith`, and prove
products equal zero via `mul_eq_zero.mp ... |>.resolve_right ...`.
-/

namespace Commons.Algebra.Matrix

theorem symm_det0_kernel_perp_ne {a b c w0 w1 : ℝ}
    (hdet : a * c = b ^ 2)
    (hk0 : a * w0 + b * w1 = 0) (hk1 : b * w0 + c * w1 = 0)
    (hw : w0 ≠ 0 ∨ w1 ≠ 0) (hM : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    (-w1) ^ 2 * a + 2 * ((-w1) * w0) * b + (w0) ^ 2 * c ≠ 0 := by
  by_cases hw0 : w0 = 0
  · by_cases hw1 : w1 = 0
    · exfalso
      rcases hw with hw0' | hw1'
      · exact hw0' hw0
      · exact hw1' hw1
    · -- w0 = 0, w1 ≠ 0
      have hbw1 : b * w1 = 0 := by
        have hk0' := hk0
        rw [hw0] at hk0'
        simpa using hk0'
      have hb : b = 0 := (mul_eq_zero.mp hbw1).resolve_right hw1
      have hcw1 : c * w1 = 0 := by
        have hk1' := hk1
        rw [hw0] at hk1'
        simpa using hk1'
      have hc : c = 0 := (mul_eq_zero.mp hcw1).resolve_right hw1
      have ha : a ≠ 0 := by
        rcases hM with ha' | hb' | hc'
        · exact ha'
        · exact (hb' hb).elim
        · exact (hc' hc).elim
      have hneg : -w1 ≠ 0 := neg_ne_zero.mpr hw1
      have hmul : (-w1) ^ 2 * a ≠ 0 := mul_ne_zero (pow_ne_zero 2 hneg) ha
      simpa [hw0, hb, hc] using hmul
  · by_cases hw1 : w1 = 0
    · -- w0 ≠ 0, w1 = 0
      have haw0 : a * w0 = 0 := by
        have hk0' := hk0
        rw [hw1] at hk0'
        simpa using hk0'
      have ha : a = 0 := (mul_eq_zero.mp haw0).resolve_right hw0
      have hbw0 : b * w0 = 0 := by
        have hk1' := hk1
        rw [hw1] at hk1'
        simpa using hk1'
      have hb : b = 0 := (mul_eq_zero.mp hbw0).resolve_right hw0
      have hc : c ≠ 0 := by
        rcases hM with ha' | hb' | hc'
        · exact (ha' ha).elim
        · exact (hb' hb).elim
        · exact hc'
      have hmul : (w0) ^ 2 * c ≠ 0 := mul_ne_zero (pow_ne_zero 2 hw0) hc
      simpa [hw1, ha, hb] using hmul
    · -- both nonzero: suppose the quadratic form vanishes and derive a=b=c=0
      intro heq
      have hmul0 :
          w0 * w1 * ((-w1) ^ 2 * a + 2 * ((-w1) * w0) * b + (w0) ^ 2 * c) = 0 := by
        rw [heq]
        ring
      have hident :
          b * (w0 ^ 4 + 2 * (w0 ^ 2 * w1 ^ 2) + w1 ^ 4) =
            (a * w0 + b * w1) * w1 ^ 3 + (b * w0 + c * w1) * w0 ^ 3 -
              w0 * w1 * ((-w1) ^ 2 * a + 2 * ((-w1) * w0) * b + (w0) ^ 2 * c) := by
        ring
      have hbS : b * (w0 ^ 4 + 2 * (w0 ^ 2 * w1 ^ 2) + w1 ^ 4) = 0 := by
        rw [hident]
        rw [hk0, hk1, hmul0]
        ring
      have hpos : 0 < w0 ^ 2 + w1 ^ 2 :=
        add_pos (sq_pos_of_ne_zero hw0) (sq_pos_of_ne_zero hw1)
      have hS : w0 ^ 4 + 2 * (w0 ^ 2 * w1 ^ 2) + w1 ^ 4 ≠ 0 := by
        rw [show w0 ^ 4 + 2 * (w0 ^ 2 * w1 ^ 2) + w1 ^ 4 = (w0 ^ 2 + w1 ^ 2) ^ 2 by ring]
        exact pow_ne_zero 2 (ne_of_gt hpos)
      have hb : b = 0 := (mul_eq_zero.mp hbS).resolve_right hS
      have ha : a = 0 := by
        have hk0' := hk0
        rw [hb] at hk0'
        have : a * w0 = 0 := by simpa using hk0'
        exact (mul_eq_zero.mp this).resolve_right hw0
      have hc : c = 0 := by
        have hk1' := hk1
        rw [hb] at hk1'
        have : c * w1 = 0 := by simpa using hk1'
        exact (mul_eq_zero.mp this).resolve_right hw1
      rcases hM with ha' | hb' | hc'
      · exact ha' ha
      · exact hb' hb
      · exact hc' hc

end Commons.Algebra.Matrix