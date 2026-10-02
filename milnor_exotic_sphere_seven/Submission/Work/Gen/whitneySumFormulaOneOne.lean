import Mathlib
import Submission.Work.LerayHirsch.Splitting
import Submission.Work.Gen.C1LineTrivial
import Submission.Work.Whitney.ChernProduct
import Submission.Work.Whitney.Cup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The Whitney sum formula in ranks `(1,1)`

The `Prop` `Work.LerayHirsch.WhitneySumFormula 1 1` asks, for every base `B` and every pair of
complex **line** bundles `L`, `M` over `B` (gluing-data bundles in the standard fibre
`EuclideanSpace ℂ (Fin 1)`, `Work.Whitney.whitneySum L M` being their direct sum of rank two), and
for **every** degree `k`,

  `c_k(L ⊕ M) = Σ_{i+j=k} c_i(L) ⌣ c_j(M)`   (`Work.Whitney.chernProductSum L M k`).

This module proves that statement from its two *irreducible* instances, which the caller supplies:

* `hOne` — degree `1`: `c_1(L ⊕ M) = c_1(L) + c_1(M)` (the determinant/`c₁`-additivity instance);
* `hCrux` — degree `2`: `c_2(L ⊕ M) = c_1(L) ⌣ c_1(M)` (the top class of the rank-two sum, i.e.
  the Euler-class multiplicativity `Work.Whitney.TopClassMul` at `m = n = 1`).

All the remaining degrees are bookkeeping, and this is what the file carries out:

* **degree `0`** (`chernProductSum_one_one_zero`): the single surviving summand is
  `c_0(L) ⌣ c_0(M) = 1 ⌣ 1 = 1`, using `Work.Thom.chernClass_zero_eq_oneH` (`c_0 = 1`) and the
  right unit law `Work.Cohomology.cupH'_one_right` of the cup product;
* **degrees `≥ 3`** (`chernProductSum_one_one_eq_zero` and `whitneySum_one_one_chernClass_eq_zero`):
  both sides vanish — the left-hand side because the Chern classes of a rank-two bundle vanish above
  degree two (`Work.Thom.chernClass_succ_of_gt`), and the right-hand side because for `k ≥ 3` and
  `i + (k - i) = k` at least one of `i`, `k - i` is `≥ 2`, where the Chern class of a line bundle
  vanishes (`Work.Thom.chernClass_succ_of_gt` again), and the graded product absorbs `0`
  (`Work.Cohomology.cupH'_zero_left`, `Work.Cohomology.cupH'_zero_right`).
-/

namespace Work.Gen

open Work.TangentClasses

noncomputable section

/-- The transport `Work.Thom.cohTransport` only depends on the two degrees: two proofs of the same
degree identity give the same transported class.  (A local copy of
`Work.LerayHirsch.cohTransport_congr_proof`, to keep the import footprint of this module small.) -/
theorem cohTransport_congr_proof_local {B : Type} [TopologicalSpace B] {n n' : ℕ}
    {x : Work.Thom.Coh ℤ n B} (h h' : n = n') :
    Work.Thom.cohTransport h x = Work.Thom.cohTransport h' x := by
  rw [Subsingleton.elim h h']

/-- **The right-hand side of the Whitney formula for two line bundles, in degree `0`**: the only
summand is `c_0(L) ⌣ c_0(M) = 1 ⌣ 1 = 1`. -/
theorem chernProductSum_one_one_zero {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type}
    [Fintype ι₁] [Fintype ι₂]
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (M : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂) :
    Work.Whitney.chernProductSum L M 0 = Work.Cohomology.oneH ℤ (Work.Whitney.ssB B) := by
  rw [Work.Whitney.chernProductSum, Finset.sum_range_one, dif_pos (Nat.zero_le 0),
    Work.Whitney.chernSummand_def, Work.Thom.chernClass_zero_eq_oneH,
    Work.Thom.chernClass_zero_eq_oneH, Work.Whitney.cupChern_def,
    Work.Cohomology.cupH'_one_right, Work.Whitney.cohTransport_trans]
  exact (cohTransport_congr_proof_local _ (rfl : 2 * 0 = 2 * 0)).trans
    (Work.Thom.cohTransport_rfl _)

/-- **The right-hand side of the Whitney formula for two line bundles vanishes in degrees `≥ 3`**:
in the summand indexed by `i ≤ k` one of the two factors has index `≥ 2`, where the Chern class of a
line bundle is `0`, and the graded product absorbs `0`. -/
theorem chernProductSum_one_one_eq_zero {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type}
    [Fintype ι₁] [Fintype ι₂]
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (M : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂) {k : ℕ} (hk : 2 < k) :
    Work.Whitney.chernProductSum L M k = 0 := by
  rw [Work.Whitney.chernProductSum]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finset.mem_range] at hi
  by_cases h : i ≤ k
  · rw [dif_pos h, Work.Whitney.chernSummand_def]
    rcases lt_or_ge i 2 with h2 | h2
    · -- `k - i ≥ 2`, so `c_{k-i}(M) = 0`
      have hM : Work.Thom.chernClass 1 (k - i) M = 0 :=
        Work.Thom.chernClass_succ_of_gt (m := 0) (j := k - i) M (by omega)
      rw [hM, Work.Whitney.cupChern_def, Work.Cohomology.cupH'_zero_right,
        Work.Thom.cohTransport_zero, Work.Thom.cohTransport_zero]
    · -- `i ≥ 2`, so `c_i(L) = 0`
      have hL : Work.Thom.chernClass 1 i L = 0 :=
        Work.Thom.chernClass_succ_of_gt (m := 0) (j := i) L (by omega)
      rw [hL, Work.Whitney.cupChern_def, Work.Cohomology.cupH'_zero_left,
        Work.Thom.cohTransport_zero, Work.Thom.cohTransport_zero]
  · rw [dif_neg h]

/-- **The left-hand side of the Whitney formula for two line bundles vanishes in degrees `> 2`**:
`L ⊕ M` has rank two, and the Chern classes of a bundle vanish above its rank. -/
theorem whitneySum_one_one_chernClass_eq_zero {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type}
    [Fintype ι₁] [Fintype ι₂]
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (M : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂)
    {j : ℕ} (hj : 2 < j) :
    Work.Thom.chernClass (1 + 1) j (Work.Whitney.whitneySum L M) = 0 :=
  Work.Thom.chernClass_succ_of_gt (m := 1) (j := j) (Work.Whitney.whitneySum L M) (by omega)

/-- **The Whitney sum formula in ranks `(1,1)`**, from its degrees `1` and `2`:
`Work.LerayHirsch.WhitneySumFormula 1 1` says `c_k(L ⊕ M) = Σ_{i+j=k} c_i(L) ⌣ c_j(M)` for all `k`.
Degree `1` is `hOne`, degree `2` is `hCrux`; degree `0` and the degrees `≥ 3` are the bookkeeping
carried out above (both sides are then `1`, resp. `0`). -/
theorem whitneySumFormulaOneOne
    (hCrux : ∀ {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
      (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
      (M : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂),
      Work.Thom.chernClass (1 + 1) 2 (Work.Whitney.whitneySum L M)
        = Work.Whitney.chernProductSum L M 2)
    (hOne : ∀ {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
      (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
      (M : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂),
      Work.Thom.chernClass (1 + 1) 1 (Work.Whitney.whitneySum L M)
        = Work.Whitney.chernProductSum L M 1) :
    Work.LerayHirsch.WhitneySumFormula 1 1 := by
  intro B _ ι₁ ι₂ _ _ L M k
  rcases k with _ | _ | _ | k
  · -- degree `0`: both sides are the unit class
    rw [chernProductSum_one_one_zero L M]
    exact Work.Thom.chernClass_zero_eq_oneH (Work.Whitney.whitneySum L M)
  · -- degree `1`: the input `hOne`
    exact hOne L M
  · -- degree `2`: the input `hCrux`
    exact hCrux L M
  · -- degrees `≥ 3`: both sides vanish
    rw [whitneySum_one_one_chernClass_eq_zero L M (j := k + 3) (by omega),
      chernProductSum_one_one_eq_zero L M (k := k + 3) (by omega)]

end

end Work.Gen
