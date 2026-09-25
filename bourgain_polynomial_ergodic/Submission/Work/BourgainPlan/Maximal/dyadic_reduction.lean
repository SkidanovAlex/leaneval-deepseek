import Mathlib
import Submission.Work.BourgainPlan.Maximal.DRDFDefs

namespace Work.BourgainPlan.Maximal

noncomputable section

open MeasureTheory

/-- A sum over `Finset.range (M * n)` splits into `M` consecutive blocks of length `n`. -/
lemma sum_range_mul_block (f : ℕ → ℂ) (M n : ℕ) :
    (∑ k ∈ Finset.range (M * n), f k)
      = ∑ j ∈ Finset.range M, ∑ r ∈ Finset.range n, f (j * n + r) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih,
      Finset.sum_range_succ (fun j => ∑ r ∈ Finset.range n, f (j * n + r)) M]

/-- Telescoping sum of successive differences over a block of length `n`. -/
lemma sum_range_telescope (S : ℕ → ℂ) (c n : ℕ) :
    ∑ r ∈ Finset.range n, (S (c + r) - S (c + (r + 1))) = S c - S (c + n) := by
  have h := Finset.sum_range_sub' (fun r => S (c + r)) n
  simpa using h

/-- The Abel rearrangement underlying the dyadic reduction. -/
lemma sum_range_mul_div (S : ℕ → ℂ) (a : ℕ → ℂ) (M i : ℕ) :
    (∑ k ∈ Finset.range (M * 2 ^ i), a (k / 2 ^ i) * (S k - S (k + 1)))
      = ∑ j ∈ Finset.range M, a j * (S (j * 2 ^ i) - S ((j + 1) * 2 ^ i)) := by
  rw [sum_range_mul_block (fun k => a (k / 2 ^ i) * (S k - S (k + 1))) M (2 ^ i)]
  apply Finset.sum_congr rfl
  intro j hj
  have hpos : 0 < 2 ^ i := pow_pos (by norm_num) i
  have hcoeff : ∀ r : ℕ, r < 2 ^ i → a ((j * 2 ^ i + r) / 2 ^ i) = a j := by
    intro r hr
    congr 1
    rw [add_comm, Nat.add_mul_div_right r j hpos, Nat.div_eq_of_lt hr, zero_add]
  trans ∑ r ∈ Finset.range (2 ^ i), a j * (S (j * 2 ^ i + r) - S (j * 2 ^ i + (r + 1)))
  · apply Finset.sum_congr rfl
    intro r hr
    rw [hcoeff r (Finset.mem_range.mp hr), Nat.add_assoc]
  · rw [← Finset.mul_sum, sum_range_telescope S (j * 2 ^ i) (2 ^ i), Nat.succ_mul]

theorem dyadic_reduction (P : Polynomial ℤ) (i M : ℕ) (ε : ℕ → ℂ) :
    Work.BourgainPlan.Maximal.mstThetaOp P i M ε = Work.BourgainPlan.Maximal.dyadSum P (M * 2 ^ i) (fun k => ε (k / 2 ^ i)) := by
  funext h x
  simp only [mstThetaOp, dyadSum, dyadD, curveSigma, Nat.cast_pow, Nat.cast_ofNat]
  exact (sum_range_mul_div (fun k => ∫ t in (0:ℝ)..1,
    h (x - (toRealPoly P).eval (((2:ℝ) ^ k) * t))) ε M i).symm

end

end Work.BourgainPlan.Maximal
