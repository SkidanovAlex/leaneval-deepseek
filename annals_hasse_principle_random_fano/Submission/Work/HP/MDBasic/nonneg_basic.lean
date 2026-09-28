import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDCommon

/-!
# Basic non-negativity of the second-moment objects

All the analytic objects of the second-moment computation (`ι_{d,n}`, `E_{d,n}(B)`,
the pair counts `pairS0`, the two partial sums `Σ^{(1)}`, `Σ^{(2)}` and the main term)
are counts, volumes or sums of non-negative quantities, hence non-negative.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset

namespace Work.HP.MDBasic

open Work.HP

/-- `ι_{d,n} = V_{N-2} / (8 ζ(N-2))` is non-negative: a volume over a positive denominator. -/
lemma iotaDN_nonneg (d n : ℕ) : 0 ≤ iotaDN d n := by
  unfold iotaDN ballVol
  apply div_nonneg
  · exact ENNReal.toReal_nonneg
  · apply mul_nonneg (by norm_num)
    apply tsum_nonneg
    intro k
    apply div_nonneg zero_le_one
    apply pow_nonneg
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith

/-- `E_{d,n}(B) = Σ_{Ω(B)} 1/det Γ_{x,y}` is non-negative: each summand is `1/√(det Gram) ≥ 0`. -/
lemma EE_nonneg (d n : ℕ) (B : ℝ) : 0 ≤ EE d n B := by
  unfold EE
  rw [finsum_mem_def]
  apply finsum_nonneg
  intro p
  apply Set.indicator_nonneg
  intro p _
  apply div_nonneg zero_le_one
  unfold detL
  exact Real.sqrt_nonneg _

/-- `pairS0` is a cardinality cast, hence non-negative. -/
lemma pairS0_nonneg (d n : ℕ) (A : ℝ)
    (p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) : 0 ≤ pairS0 d n A p := by
  unfold pairS0
  exact Nat.cast_nonneg _

/-- `Σ^{(1)}` is a sum of pair counts. -/
lemma Sigma1_nonneg (d n : ℕ) (A B : ℝ) : 0 ≤ Sigma1 d n A B := by
  unfold Sigma1
  apply mul_nonneg (by norm_num)
  rw [finsum_mem_def]
  apply finsum_nonneg
  intro p
  apply Set.indicator_nonneg
  intro p _
  exact pairS0_nonneg d n A p

/-- `Σ^{(2)}` is a sum of pair counts. -/
lemma Sigma2_nonneg (d n : ℕ) (A B : ℝ) : 0 ≤ Sigma2 d n A B := by
  unfold Sigma2
  apply mul_nonneg (by norm_num)
  rw [finsum_mem_def]
  apply finsum_nonneg
  intro p
  apply Set.indicator_nonneg
  intro p _
  exact pairS0_nonneg d n A p

/-- `2 ι_{d,n} A^{N-2} E_{d,n}(B) ≥ 0` for `A ≥ 0`. -/
lemma mainTerm_nonneg (d n : ℕ) (A B : ℝ) (hA : 0 ≤ A) : 0 ≤ mainTerm d n A B := by
  unfold mainTerm
  apply mul_nonneg
  · exact mul_nonneg (mul_nonneg (by norm_num) (iotaDN_nonneg d n)) (pow_nonneg hA _)
  · exact EE_nonneg d n B

theorem nonneg_basic (d n : ℕ) (A B : ℝ) (hA : 0 ≤ A) :
    0 ≤ iotaDN d n ∧ 0 ≤ EE d n B ∧ (∀ p, 0 ≤ pairS0 d n A p) ∧ 0 ≤ Sigma1 d n A B ∧
      0 ≤ Sigma2 d n A B ∧ 0 ≤ mainTerm d n A B :=
  ⟨iotaDN_nonneg d n, EE_nonneg d n B, fun p => pairS0_nonneg d n A p,
    Sigma1_nonneg d n A B, Sigma2_nonneg d n A B, mainTerm_nonneg d n A B hA⟩

end Work.HP.MDBasic
