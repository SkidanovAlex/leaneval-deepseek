import Mathlib
import Submission.Work.BW.DefsAC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Shared definitions and elementary facts for the proof of `Work.BW.bprodOdd_norm_ge`
(BW (25), lower half).  The main index set is `oddIdx X`, the product `bprodOdd` runs over it. -/

namespace Work.BW

/-- The index set of `bprodOdd R X z`: the odd integers `k` with `|k| ≤ X`. -/
def oddIdx (X : ℕ) : Finset ℤ := (Finset.Icc (-(X : ℤ)) (X : ℤ)).filter Odd

/-- `bprodOdd` is the product of `bfac` over `oddIdx`. -/
lemma bprodOdd_eq_prod (R : ℝ) (X : ℕ) (z : ℂ) :
    bprodOdd R X z = ∏ k ∈ oddIdx X, bfac R k z := rfl

lemma mem_oddIdx {X : ℕ} {k : ℤ} :
    k ∈ oddIdx X ↔ Odd k ∧ k ∈ Finset.Icc (-(X : ℤ)) (X : ℤ) := by
  rw [oddIdx, Finset.mem_filter]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

lemma mem_oddIdx_iff {X : ℕ} {k : ℤ} :
    k ∈ oddIdx X ↔ Odd k ∧ -((X : ℤ)) ≤ k ∧ k ≤ (X : ℤ) := by
  rw [mem_oddIdx, Finset.mem_Icc]

/-- The denominator bound for the factor `β(z;k)`: `D_k = |R² − k·l| + |k|·η`. -/
noncomputable def bpD (R η : ℝ) (l k : ℤ) : ℝ := |R^2 - (k:ℝ)*(l:ℝ)| + |(k:ℝ)| * η

/-- The numerator bound for the factor `β(z;k)`: `U_k = max η (|k − l| − η)`. -/
noncomputable def bpU (η : ℝ) (l k : ℤ) : ℝ := max η (|(k:ℝ) - (l:ℝ)| - η)

/-- `∏_{t=1}^{A}(2t − η) · ∏_{t=1}^{B}(2t − η)`, the shape of the products of distances
`|k − l|` over the odd indices, split at `l`. -/
noncomputable def bpG (η : ℝ) (A B : ℕ) : ℝ :=
  (∏ t ∈ Finset.range A, (2*(t:ℝ) + 2 - η)) * (∏ t ∈ Finset.range B, (2*(t:ℝ) + 2 - η))

/-- The double-factorial product `(2m−1)!!(2m−3)!! = ∏_{t=0}^{m−2}(2t+1)(2t+3)`. -/
noncomputable def bpNum (m : ℕ) : ℝ :=
  ∏ t ∈ Finset.range (m - 1), ((2*(t:ℝ) + 1) * (2*(t:ℝ) + 3))

/-- Any `D_k` in the range of interest is strictly positive. -/
lemma bpD_pos {R η : ℝ} (hη : 0 ≤ η) {l k : ℤ}
    (h : |(k:ℝ)| * (|(l:ℝ)| + η) < R^2) : 0 < bpD R η l k := by
  have hk : (0:ℝ) ≤ |(k:ℝ)| := abs_nonneg _
  have hl : (0:ℝ) ≤ |(l:ℝ)| := abs_nonneg _
  have h1 : |(k:ℝ)| * |(l:ℝ)| < R^2 := by
    have : (0:ℝ) ≤ |(k:ℝ)| * η := mul_nonneg hk hη
    linarith [mul_add (|(k:ℝ)|) (|(l:ℝ)|) η]
  have h2 : R^2 - |(k:ℝ)| * |(l:ℝ)| ≤ |R^2 - (k:ℝ)*(l:ℝ)| := by
    have h3 := abs_sub_abs_le_abs_sub (R^2) ((k:ℝ)*(l:ℝ))
    rw [abs_mul, abs_of_nonneg (sq_nonneg R)] at h3
    linarith
  unfold bpD
  nlinarith [abs_nonneg ((k:ℝ)), hη]

/-- The natural numbers `(m−1−i)` and `(m+i)` for `i ∈ [−m, m−1]` add up to `2m−1`. -/
lemma toNat_add_toNat (m : ℕ) (i : ℤ) (h1 : 0 ≤ (m:ℤ) - 1 - i) (h2 : 0 ≤ (m:ℤ) + i)
    (hm : 1 ≤ m) :
    ((m:ℤ) - 1 - i).toNat + ((m:ℤ) + i).toNat = 2*m - 1 := by
  have e1 := Int.toNat_of_nonneg h1
  have e2 := Int.toNat_of_nonneg h2
  omega

end Work.BW
