import Mathlib

/-!
# The Möbius function, as a real number

Basic facts about `muR n = ((μ n : ℤ) : ℝ)` used by the reindexing identity
`Work.LinnikAreas.BGTZ.moebius_reindex`.
-/

namespace Work.LinnikAreas.BGTZ

/-- The Möbius function `μ` evaluated at `n`, as a real number. -/
abbrev muR (n : ℕ) : ℝ := ((ArithmeticFunction.moebius n : ℤ) : ℝ)

lemma muR_one : muR 1 = 1 := by
  simp only [muR]
  rw [ArithmeticFunction.moebius_apply_one]
  norm_num

/-- `μ` is multiplicative on coprime arguments. -/
lemma muR_mul {a b : ℕ} (h : Nat.Coprime a b) : muR (a * b) = muR a * muR b := by
  simp only [muR]
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h]
  push_cast
  ring

/-- `μ` vanishes off the squarefree integers. -/
lemma muR_eq_zero_of_not_squarefree {n : ℕ} (h : ¬ Squarefree n) : muR n = 0 := by
  simp only [muR]
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
  norm_num

/-- `μ n ≠ 0` exactly on the squarefree integers. -/
lemma muR_ne_zero_iff_squarefree {n : ℕ} : muR n ≠ 0 ↔ Squarefree n := by
  constructor
  · intro h
    by_contra hns
    exact h (muR_eq_zero_of_not_squarefree hns)
  · intro hs hc
    simp only [muR] at hc
    have hz : (ArithmeticFunction.moebius n : ℤ) = 0 := by exact_mod_cast hc
    exact (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hs) hz

end Work.LinnikAreas.BGTZ
