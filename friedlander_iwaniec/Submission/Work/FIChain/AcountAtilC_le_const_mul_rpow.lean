/-
# The trivial upper bound `Ã(x) ≪ x^{3/4}`

`Ã(x) = Σ_{n ≤ x} μ(n)² a_n` counts the squarefree `n ≤ x` represented as `a² + c⁴`.
Dropping the factor `μ(n)² ≤ 1` and the squarefree restriction,
  `Ã(x) ≤ Σ_{n ≤ x} a_n = A(x) = #{lattice points a² + c⁴ ≤ x}`,
and the latter is `≪ x^{3/4}` simply because the feasible pairs lie in the box
`|a| ≤ √x`, `|c| ≤ x^{1/4}`.  The published asymptotic `A(x) = 4κ x^{3/4} + O(√x)`
(the file `Submission/ASP_R.lean`, imported through `Work.FIChain.Defs`) already
supplies the exact form of this estimate, so the proof below only has to compare
the two counting functions.

This is the *easy* half of the companion paper's bound `Ã(x) ≍ x^{3/4}`; the lower
bound is a separate obligation.
-/
import Mathlib
import Submission.Work.FIChain.Defs

namespace Work.FIChain

open Finset

/-- `μ(n)² ≤ 1`: the Möbius function takes only the values `-1, 0, 1`, so its square is
`0` or `1` (`ArithmeticFunction.moebius_sq`). -/
private lemma moebius_cast_sq_le_one (n : ℕ) : (ArithmeticFunction.moebius n : ℝ) ^ 2 ≤ 1 := by
  rw [← Int.cast_pow, ArithmeticFunction.moebius_sq]
  split <;> norm_num

/-- `Ã(x) ≤ A(x)`: the squarefree-supported counting function of `μ(n)² a_n` is dominated
by the counting function of `a_n`, because `μ(n)² ≤ 1` and `a_n ≥ 0`. -/
private lemma AcountAtilC_le_Aseq (Z : ℕ) :
    Work.FIChain.AcountAtilC Z ≤ (Submission.Aseq Z : ℝ) := by
  rw [Work.FIChain.AcountAtilC, Work.FITop.AcountAtil, Submission.ASP.Acount,
      Nat.floor_natCast, Submission.Aseq, Nat.cast_sum]
  have hterm : ∀ n ∈ Finset.Icc 1 Z,
      Work.FITop.atilFIa n ≤ (Submission.an n : ℝ) := by
    intro n _
    rw [Work.FITop.atilFIa, Submission.ASP.atil, Submission.ASP.FIa]
    calc (ArithmeticFunction.moebius n : ℝ) ^ 2 * (Submission.an n : ℝ)
        ≤ 1 * (Submission.an n : ℝ) :=
          mul_le_mul_of_nonneg_right (moebius_cast_sq_le_one n) (Nat.cast_nonneg _)
      _ = (Submission.an n : ℝ) := one_mul _
  have hsub : Finset.Icc 1 Z ⊆ Finset.range (Z + 1) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_range]
    omega
  calc ∑ n ∈ Finset.Icc 1 Z, Work.FITop.atilFIa n
      ≤ ∑ n ∈ Finset.Icc 1 Z, (Submission.an n : ℝ) := Finset.sum_le_sum hterm
    _ ≤ ∑ n ∈ Finset.range (Z + 1), (Submission.an n : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.cast_nonneg _)

/-- `Ã(Z) ≪ Z^{3/4}`: the squarefree-supported counting function of `a_n = #{(a,c) : a² + c⁴ = n}`
is bounded by the (already established) bound `A(Z) ≤ C Z^{3/4}` for the full counting function. -/
theorem AcountAtilC_le_const_mul_rpow :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℕ, 1 ≤ Z →
      Work.FIChain.AcountAtilC Z ≤ C * (Z : ℝ) ^ ((3 : ℝ) / 4) := by
  obtain ⟨C, hC, hC'⟩ := Submission.Aseq_le_const_mul_rpow
  exact ⟨C, hC, fun Z hZ => le_trans (AcountAtilC_le_Aseq Z) (hC' Z hZ)⟩

end Work.FIChain
