import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.twoLetterTlDefs

namespace Work.OROneRel

/-- The weight of the two-letter case at the first generator: `tlW p q 0 = q`. -/
private theorem tlW_zero' (p q : ℕ) : tlW p q (0 : Fin 2) = (q : ℤ) := by simp [tlW]

theorem walkMid_a_mem {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (a : ℤ) (ha : a ≤ 1) {j : ℕ}
    (hj : j + 2 ≤ p) :
    (((0 : Fin 2), a - 1 + ((j : ℤ) + 1) * (q : ℤ)) : Fin 2 × ℤ) ∈
      Work.OROneRel.winE (Work.OROneRel.tlW p q) a ((p : ℤ) * (q : ℤ)) := by
  have hq1 : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  have hq0 : (0 : ℤ) ≤ (q : ℤ) := by linarith
  have hj0 : (0 : ℤ) ≤ (j : ℤ) := by positivity
  have hj2 : (j : ℤ) + 2 ≤ (p : ℤ) := by exact_mod_cast hj
  have hj1p : (j : ℤ) + 1 ≤ (p : ℤ) := by linarith
  have h2 : ((j : ℤ) + 1) * (q : ℤ) ≤ (p : ℤ) * (q : ℤ) :=
    mul_le_mul_of_nonneg_right hj1p hq0
  have h4 : ((j : ℤ) + 2) * (q : ℤ) ≤ (p : ℤ) * (q : ℤ) :=
    mul_le_mul_of_nonneg_right hj2 hq0
  have h1 : (1 : ℤ) ≤ ((j : ℤ) + 1) * (q : ℤ) := by nlinarith [hj0, hq1]
  rw [mem_winE, tlW_zero']
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end Work.OROneRel
