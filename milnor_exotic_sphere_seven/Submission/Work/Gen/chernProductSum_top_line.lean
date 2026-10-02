import Mathlib
import Submission.Work.Whitney.ChernProduct
import Submission.Work.Whitney.chernProductSum_eq_fin
import Submission.Work.LerayHirsch.Series
import Submission.Work.Thom.chernClass_eq_zero_of_lt
import Submission.Work.Thom.trivialChern

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace Work.Gen

/-- **The right-hand side of the Whitney formula in the top degree, with a line bundle in the
first slot.**  For `L` of rank `1` and `W` of rank `m`, the sum `chernProductSum L W (m+1)` has
exactly one non-vanishing summand, namely the one with `i = 1` (the `i = 0` summand carries
`c_{m+1}(W) = 0` because the rank of `W` is `m`, and the `i ≥ 2` summands carry `c_i(L) = 0` because
the rank of `L` is `1`).  The statement is the crash-free form of that collapse, with the degree cast
`2 * (1 + m) = 2 * (m + 1)` matching `Work.Whitney.chernClass_whitneySum_top`, whose right-hand side
is `cupChern 1 m (c₁ L) (c_m W)`.

Proof route: `Work.Whitney.chernProductSum` is `∑ i ∈ Finset.range (k + 1), …`; kill the `i = 0`
summand with `Work.Thom.chernClass_eq_zero_of_lt` (applied to `W`, which covers `m = 0` as well)
together with `Work.Cohomology.cupH'_zero_right` (note: *right*, not left), and the `i ≥ 2` summands
with `Work.Thom.chernClass_eq_zero_of_lt` (applied to `L`, since `1 < i`) together with
`Work.LerayHirsch.cupChern_zero_left`; then identify the surviving summand. -/
theorem chernProductSum_top_line {B : Type} [TopologicalSpace B] {ι ι' : Type} [Fintype ι]
    [Fintype ι'] {m : ℕ} (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') :
    Work.Whitney.chernProductSum L W (m + 1)
      = Work.Thom.cohTransport (by omega : 2 * (1 + m) = 2 * (m + 1))
          (Work.Whitney.cupChern 1 m (Work.Thom.chernClass 1 1 L)
            (Work.Thom.chernClass m m W)) := by
  unfold Work.Whitney.chernProductSum
  rw [Finset.sum_eq_single 1]
  · rw [dif_pos (by omega : 1 ≤ m + 1), Work.Whitney.chernSummand_def]
    rfl
  · intro b hb hb1
    rw [dif_pos (by simp only [Finset.mem_range] at hb; omega : b ≤ m + 1)]
    rcases b with _ | _ | b
    · simp only [Work.Whitney.chernSummand_def, Work.Whitney.cupChern_def, Nat.sub_zero]
      rw [Work.Thom.chernClass_eq_zero_of_lt W (by omega : m < m + 1)]
      simp only [Work.Cohomology.cupH'_zero_right, Work.Thom.cohTransport_zero]
    · exact absurd rfl hb1
    · simp only [Work.Whitney.chernSummand_def, Work.Whitney.cupChern_def]
      rw [Work.Thom.chernClass_eq_zero_of_lt L (by omega : 1 < b + 2)]
      simp only [Work.Cohomology.cupH'_zero_left, Work.Thom.cohTransport_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega : 1 < m + 2)) h

end Work.Gen
