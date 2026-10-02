import Mathlib
import Submission.Work.Whitney.ChernProduct
import Submission.Work.Whitney.chernProductSum_eq_fin
import Submission.Work.LerayHirsch.Series
import Submission.Work.Thom.chernClass_eq_zero_of_lt

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false

namespace Work.Gen

open scoped BigOperators

/-- The graded product `Work.Whitney.cupChern` vanishes when its second argument does. -/
theorem cupChern_zero_right {B : Type} [TopologicalSpace B] (a b : ℕ)
    (x : Work.Thom.Coh ℤ (2 * a) B) :
    Work.Whitney.cupChern a b x (0 : Work.Thom.Coh ℤ (2 * b) B) = 0 := by
  rw [Work.Whitney.cupChern_def, Work.Cohomology.cupH'_zero_right]
  exact map_zero (Work.Thom.cohTransportLM (Nat.mul_add 2 a b).symm)

/-- **The right-hand side of the Whitney formula vanishes above the total rank, with a line bundle
in the first slot.**  For `L` of rank `1` and `W` of rank `m`, every summand of
`chernProductSum L W k` vanishes as soon as `k > m + 1`: the `i = 0` summand carries `c_k(W) = 0`
because `k > m`, the `i = 1` summand carries `c_{k-1}(W) = 0` because `k - 1 > m`, and the `i ≥ 2`
summands carry `c_i(L) = 0` because the rank of `L` is `1`.

Proof route: as for `Work.Gen.chernProductSum_top_line`, using `Work.Thom.chernClass_eq_zero_of_lt`
(for `W`, in both the `i = 0` and `i = 1` cases) and for `L` (in the `i ≥ 2` case), the zero laws
`Work.Cohomology.cupH'_zero_left`/`_right` for the graded product, and `Finset.sum_eq_zero` for the
sum. -/
theorem chernProductSum_high_line {B : Type} [TopologicalSpace B] {ι ι' : Type} [Fintype ι]
    [Fintype ι'] {m : ℕ} (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') {k : ℕ} (hk : m + 1 < k) :
    Work.Whitney.chernProductSum L W k = 0 := by
  unfold Work.Whitney.chernProductSum
  refine Finset.sum_eq_zero fun i hi => ?_
  have hle : i ≤ k := by
    simp only [Finset.mem_range] at hi
    omega
  rw [dif_pos hle, Work.Whitney.chernSummand_def]
  rcases Nat.lt_or_ge 1 i with hi2 | hi2
  · -- `i ≥ 2`: the first factor carries `c_i(L) = 0` because `rank L = 1`
    rw [Work.Thom.chernClass_eq_zero_of_lt (m := 1) (j := i) L hi2,
      Work.LerayHirsch.cupChern_zero_left (a := i) (b := k - i)
        (y := Work.Thom.chernClass m (k - i) W)]
    exact map_zero (Work.Thom.cohTransportLM _)
  · -- `i ≤ 1`: the second factor carries `c_{k-i}(W) = 0` because `k - i > m`
    have hkm : m < k - i := by omega
    rw [Work.Thom.chernClass_eq_zero_of_lt (m := m) (j := k - i) W hkm,
      cupChern_zero_right (a := i) (b := k - i)]
    exact map_zero (Work.Thom.cohTransportLM _)

end Work.Gen
