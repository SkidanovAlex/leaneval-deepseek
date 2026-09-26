import Submission.Work.BoxShrink.Core.Basic
import Submission.Work.BoxShrink.Core.Counting.encard_lt_natCast_of_coe_le_ofReal

/-!
# Turning the sweep's intersection counts into statements about `ℕ∞`

The sweep `Work.BoxSweep.sweep` produces its intersection counts as inequalities of `ℝ≥0∞`
(`ENNReal`), while Pardon's Lemma 4.2 and its consumers work with `Set.encard : ℕ∞`.  This file
supplies the conversion, together with the arithmetic which compares the sweep's constants
`10(1+ε)/ε = 75` and `5(1+ε)/ε = 37.5` with the hypothesis `countConst * d < min p q`
(`countConst = 150`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.BoxShrink.Core

noncomputable section

/-- **An `ℕ∞`-valued cardinal bounded by a real, at a natural strictly above that real.**

If `e : ℕ∞` satisfies `(e : ℝ≥0∞) ≤ ofReal C` and `C < n` for a positive natural `n`, then
`e < n`.  This is how the ENNReal-valued count of `Work.BoxSweep.sweep` becomes the `ℕ∞`-valued
count of Pardon's Lemma. -/
theorem encard_lt_of_coe_le_ofReal {e : ℕ∞} {C : ℝ} {n : ℕ} (hn : n ≠ 0)
    (h : ((e : ENNReal) ≤ ENNReal.ofReal C)) (hC : C < (n : ℝ)) : e < (n : ℕ∞) :=
  Counting.encard_lt_natCast_of_coe_le_ofReal hn h hC

/-- The arithmetic of the sphere count: `10(1+ε)/ε · d < min p q`, from Pardon's hypothesis
`countConst · d < min p q` (`countConst = 150`) and `0 ≤ d`. -/
theorem ten_coeff_mul_lt_min {p q : ℕ} (_hp : 0 < p) (_hq : 0 < q) {d : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ)) :
    10 * (1 + Submission.eps) / Submission.eps * d < (Nat.min p q : ℝ) := by
  have h1 : 10 * (1 + Submission.eps) / Submission.eps = 75 := by norm_num [Submission.eps]
  rw [h1]
  rw [Submission.countConst] at hsmall
  nlinarith [hd]

/-- The arithmetic of the plane count: `5(1+ε)/ε · d < min p q`. -/
theorem five_coeff_mul_lt_min {p q : ℕ} (_hp : 0 < p) (_hq : 0 < q) {d : ℝ} (hd : 0 ≤ d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ)) :
    5 * (1 + Submission.eps) / Submission.eps * d < (Nat.min p q : ℝ) := by
  have h1 : 5 * (1 + Submission.eps) / Submission.eps = 75 / 2 := by
    norm_num [Submission.eps]
  rw [h1]
  rw [Submission.countConst] at hsmall
  nlinarith [hd]

end

end Work.BoxShrink.Core
