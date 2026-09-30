import Mathlib
import Submission.Work.BMF.Defs
import Submission.Vinogradov.ChallengeDeps
import Submission.Work.BMF.prime_interval_count

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Bookkeeping for the uniform Vinogradov mean value estimate

Definitions shared by the assembly of `Work.BMF.vmvt_uniform`: the constant `pC` extracted from
the quantitative prime-count lemma `Work.BMF.prime_interval_count`, the classical exponent
`th k r = 2kr − k(k+1)/2 + (k²/2)(1−1/k)^r`, the admissible constant `Ac C₀ k r`, and the
chosen value `C0` of the constant in front of the exponential.
-/

namespace Work.BMF

open LeanEval.NumberTheory.VinogradovMeanValue
open scoped BigOperators

noncomputable section

/-- The absolute constant produced by `Work.BMF.prime_interval_count`. -/
def pC : ℝ := Classical.choose prime_interval_count

lemma pC_pos : 0 < pC := (Classical.choose_spec prime_interval_count).1

/-- The quantitative prime-count statement, at the extracted constant. -/
lemma pC_spec (k M : ℕ) (hk : 2 ≤ k) (hM : 1 ≤ M) :
    k^3 ≤ 2 * ((Finset.Ioc M (max (2*M) ⌈pC * (k:ℝ)^3 * Real.log k⌉₊)).filter Nat.Prime).card :=
  (Classical.choose_spec prime_interval_count).2 k M hk hM

/-- The classical exponent `2kr − k(k+1)/2 + (k²/2)(1−1/k)^r` (Vinogradov–Linnik). -/
def th (k r : ℕ) : ℝ :=
  2 * ((k : ℝ) * r) - (k : ℝ) * (k + 1) / 2 + (k : ℝ) ^ 2 / 2 * (1 - 1 / (k : ℝ)) ^ r

/-- The admissible size of the constant: `exp(C₀ k² r² (1 + log(kr)))`. -/
def Ac (C₀ : ℝ) (k r : ℕ) : ℝ :=
  Real.exp (C₀ * (k : ℝ) ^ 2 * (r : ℝ) ^ 2 * (1 + Real.log ((k : ℝ) * r)))

/-- The absolute value of the constant used in the proof. -/
def C0 : ℝ := 100 * (1 + Real.log (pC + 8))

lemma C0_pos : 0 < C0 := by
  have h : 0 < Real.log (pC + 8) := Real.log_pos (by linarith [pC_pos])
  simp only [C0]; linarith

/-- The key exponent recursion: `k + 2r + (k−1)/2 + th k r·(1−1/k) = th k (r+1)`. -/
lemma th_key (k r : ℕ) (hk : 1 ≤ k) :
    (k:ℝ) + (2*(r:ℝ) + ((k:ℝ)-1)/2) + th k r * (1 - 1/(k:ℝ)) = th k (r+1) := by
  have hk0 : (k:ℝ) ≠ 0 := by positivity
  have hpow : (1 - 1/(k:ℝ)) ^ (r+1) = (1 - 1/(k:ℝ)) ^ r * (1 - 1/(k:ℝ)) := pow_succ _ _
  simp only [th, hpow]
  push_cast
  field_simp
  ring

end
end Work.BMF
