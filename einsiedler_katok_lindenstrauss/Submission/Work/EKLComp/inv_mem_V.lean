import Mathlib
import Submission.Work.EKLProd.inv_entries_bound

/-!
# The displacement neighbourhood `V δ` is stable under inversion

`Work.EKLContract.V δ = {g : SL₃(ℝ) | ∀ i j, |g i j - 1 i j| < δ}` is the entrywise
`δ`-neighbourhood of the identity.  This file proves that for `0 < δ ≤ 1` the inverse of an
element of `V δ` lies in `V (10 δ)`.

Mathematically, if `A = 1 + B` with `|B i j| < δ`, then `A⁻¹ = adjugate A` (because `det A = 1`),
and the entries of the adjugate are `2 × 2` minors of `A`.  A minor has either two diagonal
entries (`A i i = 1 + bᵢᵢ`, contributing a deviation `< 2δ + 2δ²` from `1` at a diagonal position)
or exactly one diagonal entry (contributing a magnitude `< δ + 2δ²` at an off-diagonal position).
Since `δ ≤ 1` we get `δ² ≤ δ`, so both bounds are `< 4δ ≤ 10δ`.

The argument is carried out on the explicit formula `Matrix.adjugate_fin_three`; the two
elementary estimates are factored out as `abs_diag` and `abs_off`.
-/

set_option linter.unusedVariables false

namespace Work.EKLComp

/-- Entrywise estimate for a diagonal position of the adjugate: if `m` and `n` are `δ`-close
to `1` and `u`, `v` are within `δ` of `0`, then `m n - u v` is within `10 δ` of `1`. -/
lemma abs_diag {δ m n u v : ℝ} (hδ : 0 < δ) (h1 : δ ≤ 1)
    (hm : |m - 1| < δ) (hn : |n - 1| < δ) (hu : |u| < δ) (hv : |v| < δ) :
    |m * n - u * v - 1| < 10 * δ := by
  have hδnn : (0 : ℝ) ≤ δ := le_of_lt hδ
  have key : m * n - u * v - 1 = (m - 1) + (n - 1) + (m - 1) * (n - 1) - u * v := by ring
  rw [key]
  have hm' : |m - 1| ≤ δ := le_of_lt hm
  have hn' : |n - 1| ≤ δ := le_of_lt hn
  have hmn : |(m - 1) * (n - 1)| ≤ δ ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hm' hn' (abs_nonneg _) hδnn
  have huv : |u * v| ≤ δ ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (le_of_lt hu) (le_of_lt hv) (abs_nonneg _) hδnn
  have htri : |(m - 1) + (n - 1) + (m - 1) * (n - 1) - u * v|
      ≤ |m - 1| + |n - 1| + |(m - 1) * (n - 1)| + |u * v| := by
    calc |(m - 1) + (n - 1) + (m - 1) * (n - 1) - u * v|
        ≤ |(m - 1) + (n - 1) + (m - 1) * (n - 1)| + |u * v| := abs_sub _ _
      _ ≤ (|(m - 1) + (n - 1)| + |(m - 1) * (n - 1)|) + |u * v| := by
            gcongr
            exact abs_add_le _ _
      _ ≤ ((|m - 1| + |n - 1|) + |(m - 1) * (n - 1)|) + |u * v| := by
            gcongr
            exact abs_add_le _ _
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith [hδ, h1]
  linarith [htri, hm', hn', hmn, huv, hδ, hδ2]

/-- Entrywise estimate for an off-diagonal position of the adjugate: if `m` is `δ`-close to `1`
and `a`, `b`, `c` are within `δ` of `0`, then `a b - m c` is within `10 δ` of `0`. -/
lemma abs_off {δ a b c m : ℝ} (hδ : 0 < δ) (h1 : δ ≤ 1)
    (ha : |a| < δ) (hb : |b| < δ) (hc : |c| < δ) (hm : |m - 1| < δ) :
    |a * b - m * c| < 10 * δ := by
  have hδnn : (0 : ℝ) ≤ δ := le_of_lt hδ
  have hmabs : |m| ≤ 1 + δ := by
    calc |m| = |(m - 1) + 1| := by ring_nf
      _ ≤ |m - 1| + |1| := abs_add_le _ _
      _ ≤ δ + 1 := by rw [abs_one]; linarith [le_of_lt hm]
      _ = 1 + δ := by ring
  have htri : |a * b - m * c| ≤ |a * b| + |m * c| := abs_sub _ _
  rw [abs_mul, abs_mul] at htri
  have h1' : |a| * |b| ≤ δ * δ := mul_le_mul (le_of_lt ha) (le_of_lt hb) (abs_nonneg b) hδnn
  have h2' : |m| * |c| ≤ (1 + δ) * δ := mul_le_mul hmabs (le_of_lt hc) (abs_nonneg c) (by linarith)
  have hfin : δ * δ + (1 + δ) * δ < 10 * δ := by nlinarith [hδ, h1]
  linarith [htri, h1', h2', hfin]

/-- If every entry of `A` is within `δ` of the corresponding entry of the identity (`δ ≤ 1`),
then every entry of `A.adjugate` is within `10 δ` of the identity. -/
lemma adjugate_close {A : Matrix (Fin 3) (Fin 3) ℝ} {δ : ℝ} (hδ : 0 < δ) (h1 : δ ≤ 1)
    (hA : ∀ i j, |A i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < δ) :
    ∀ i j, |A.adjugate i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < 10 * δ := by
  intro i j
  rw [Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases j <;> simp
  all_goals
    first
      | exact abs_diag hδ h1 (by simpa using hA 1 1) (by simpa using hA 2 2) (by simpa using hA 1 2) (by simpa using hA 2 1)
      | exact abs_diag hδ h1 (by simpa using hA 0 0) (by simpa using hA 2 2) (by simpa using hA 0 2) (by simpa using hA 2 0)
      | exact abs_diag hδ h1 (by simpa using hA 0 0) (by simpa using hA 1 1) (by simpa using hA 0 1) (by simpa using hA 1 0)
      | (rw [show -(A 0 1 * A 2 2) + A 0 2 * A 2 1 = A 0 2 * A 2 1 - A 2 2 * A 0 1 by ring]
         exact abs_off hδ h1 (by simpa using hA 0 2) (by simpa using hA 2 1) (by simpa using hA 0 1) (by simpa using hA 2 2))
      | (rw [show A 0 1 * A 1 2 - A 0 2 * A 1 1 = A 0 1 * A 1 2 - A 1 1 * A 0 2 by ring]
         exact abs_off hδ h1 (by simpa using hA 0 1) (by simpa using hA 1 2) (by simpa using hA 0 2) (by simpa using hA 1 1))
      | (rw [show -(A 1 0 * A 2 2) + A 1 2 * A 2 0 = A 1 2 * A 2 0 - A 2 2 * A 1 0 by ring]
         exact abs_off hδ h1 (by simpa using hA 1 2) (by simpa using hA 2 0) (by simpa using hA 1 0) (by simpa using hA 2 2))
      | (rw [show -(A 0 0 * A 1 2) + A 0 2 * A 1 0 = A 0 2 * A 1 0 - A 0 0 * A 1 2 by ring]
         exact abs_off hδ h1 (by simpa using hA 0 2) (by simpa using hA 1 0) (by simpa using hA 1 2) (by simpa using hA 0 0))
      | exact abs_off hδ h1 (by simpa using hA 1 0) (by simpa using hA 2 1) (by simpa using hA 2 0) (by simpa using hA 1 1)
      | (rw [show -(A 0 0 * A 2 1) + A 0 1 * A 2 0 = A 0 1 * A 2 0 - A 0 0 * A 2 1 by ring]
         exact abs_off hδ h1 (by simpa using hA 0 1) (by simpa using hA 2 0) (by simpa using hA 2 1) (by simpa using hA 0 0))

theorem inv_mem_V {δ : ℝ} (hδ : 0 < δ) (h1 : δ ≤ 1) {g : Work.EKLContract.SL3} (hg : g ∈ Work.EKLContract.V δ) : g⁻¹ ∈ Work.EKLContract.V (10 * δ) := by
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_inv]
  exact adjugate_close hδ h1 hg i j

end Work.EKLComp
