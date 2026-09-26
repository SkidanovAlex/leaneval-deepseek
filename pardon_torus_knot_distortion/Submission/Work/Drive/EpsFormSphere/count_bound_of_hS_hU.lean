import Mathlib
import Submission.Box

/-!
# The two counts of the crux compose to one: `10(1+ε)/ε·d + 2·5(1+ε)/ε·d = 150 d`

Pardon's Lemma 3 needs the single counting hypothesis `|S ∩ β| + 2 |D ∩ β| < I(F,β)` on the level
sphere `S` and the pinching disc `D`.  The crux supplies it as two *separate* bounds,
`#(K ∩ ∂PBox) ≤ 10(1+ε)/ε·d` (the sphere count) and `#(K ∩ ∂PBox ∩ {plane}) ≤ 5(1+ε)/ε·d` (the plane
count); since the knot meets the boundary sphere of the swept ball in at most
`#(K ∩ ∂PBox) + 2 #(K ∩ D)` points (the slab's short arcs, one per crossing of the cutting disc), the
two bounds compose to

    10(1+ε)/ε·d + 2·(5(1+ε)/ε·d) = 20(1+ε)/ε·d = 150 d = countConst · d < min p q.

This module records that arithmetic, in the `ENNReal` bookkeeping in which the two counts are stated,
so that the level-local counting step (P4) only has to produce the *geometric* inequality
`#(K ∩ ∂R_lam) ≤ nS + 2 nU` with `nS`, `nU` the two parameter counts.
-/

open LeanEval.KnotTheory.PardonDistortion
open scoped ENNReal

namespace Work.Drive.EpsFormSphere

/-- `10(1+ε)/ε = 75` and `5(1+ε)/ε = 37.5` at `ε = 2/13`, so the two counts add up to `150 d`. -/
theorem ten_mul_one_add_eps_div_eps : 10 * (1 + Submission.eps) / Submission.eps = 75 := by
  rw [show Submission.eps = 2 / 13 from rfl]; norm_num

theorem five_mul_one_add_eps_div_eps : 5 * (1 + Submission.eps) / Submission.eps = 75 / 2 := by
  rw [show Submission.eps = 2 / 13 from rfl]; norm_num

/-- **The two counting hypotheses of the crux compose to the bound of the count at a regular level.**
If `nS` is bounded by the sphere count and `nU` by the plane count at a crux configuration, then
`nS + 2 nU < min p q`. -/
theorem count_bound_of_hS_hU {p q : ℕ} {d : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ)) {nS nU : ℕ}
    (hS : (nS : ℝ≥0∞) ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d))
    (hU : (nU : ℝ≥0∞) ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) :
    ((nS + 2 * nU : ℕ) : ℝ≥0∞) < (Nat.min p q : ℝ≥0∞) := by
  have hS75 : (nS : ℝ) ≤ 75 * d := by
    have h := (ENNReal.le_ofReal_iff_toReal_le (a := (nS : ℝ≥0∞))
      (b := 10 * (1 + Submission.eps) / Submission.eps * d) (by simp) (by have := Submission.eps_pos; positivity)).mp hS
    rw [ENNReal.toReal_natCast, ten_mul_one_add_eps_div_eps] at h
    exact h
  have hU75 : (nU : ℝ) ≤ (75 / 2) * d := by
    have h := (ENNReal.le_ofReal_iff_toReal_le (a := (nU : ℝ≥0∞))
      (b := 5 * (1 + Submission.eps) / Submission.eps * d) (by simp) (by have := Submission.eps_pos; positivity)).mp hU
    rw [ENNReal.toReal_natCast, five_mul_one_add_eps_div_eps] at h
    exact h
  have hsmall' : 150 * d < (Nat.min p q : ℝ) := by
    rw [show Submission.countConst = 150 from rfl] at hsmall
    exact hsmall
  have hpos : 0 < (Nat.min p q : ℝ) := lt_of_le_of_lt (by linarith) hsmall'
  have hkey : ((nS + 2 * nU : ℕ) : ℝ) < (Nat.min p q : ℝ) := by
    have h2 : 2 * (nU : ℝ) ≤ 75 * d := by linarith
    have h1 : (nS : ℝ) ≤ 75 * d := hS75
    have hmin : (Nat.min p q : ℝ) = min (p : ℝ) (q : ℝ) := by push_cast; rfl
    push_cast
    linarith
  rw [← ENNReal.ofReal_natCast (nS + 2 * nU), ← ENNReal.ofReal_natCast (Nat.min p q)]
  exact (ENNReal.ofReal_lt_ofReal_iff hpos).mpr hkey

end Work.Drive.EpsFormSphere
