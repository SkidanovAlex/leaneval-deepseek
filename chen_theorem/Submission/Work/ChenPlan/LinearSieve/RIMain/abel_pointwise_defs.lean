import Mathlib
import Submission.Work.ChenPlan.LinearSieve.FrameworkR
import Submission.Work.ChenPlan.LinearSieve.Abel.abel_sum_le

/-!
# Vocabulary for the pointwise Abel estimate (`RIMain.abel_pointwise`)

* `pSet A w Z` : the primes of the sieve modulus `P = A.prodPrimes` lying in `[w, Z)`.
* `vEnum A w Z k` : the increasing enumeration of `pSet A w Z`, extended past the last
  element by the constant value `Z`.
* `Vnorm A Z u` : `VfR A u / VfR A Z`.
* `hprof K Z u` : the extremal profile `(1 + K / log u)·log Z / log u` of the linear sieve.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve.RIMain

noncomputable section

/-- The primes of the sieve modulus `P = A.prodPrimes` lying in the half-open real interval
`[w, Z)`. -/
def pSet (A : BoundingSieve) (w Z : ℝ) : Finset ℕ :=
  A.prodPrimes.primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < Z)

/-- The increasing enumeration of `pSet A w Z`, extended past the last element by the value `Z`. -/
noncomputable def vEnum (A : BoundingSieve) (w Z : ℝ) (k : ℕ) : ℝ :=
  Work.ChenPlan.LinearSieve.Abel.enumExt (pSet A w Z) Z k

/-- `VfR A u` normalised by its value at the sift limit `Z`. -/
noncomputable def Vnorm (A : BoundingSieve) (Z u : ℝ) : ℝ := VfR A u / VfR A Z

/-- The extremal profile `u ↦ (1 + K / log u)·log Z / log u`. -/
noncomputable def hprof (K Z u : ℝ) : ℝ := (1 + K / Real.log u) * (Real.log Z / Real.log u)

theorem mem_pSet {A : BoundingSieve} {w Z : ℝ} {p : ℕ} :
    p ∈ pSet A w Z ↔ p ∈ A.prodPrimes.primeFactors ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < Z := by
  rw [pSet, Finset.mem_filter]

theorem vEnum_card (A : BoundingSieve) (w Z : ℝ) : vEnum A w Z (pSet A w Z).card = Z :=
  Work.ChenPlan.LinearSieve.Abel.enumExt_self _ _

theorem vEnum_mono (A : BoundingSieve) (w Z : ℝ) : Monotone (vEnum A w Z) :=
  Work.ChenPlan.LinearSieve.Abel.enumExt_mono (fun p hp => le_of_lt (mem_pSet.mp hp).2.2)

theorem le_vEnum (A : BoundingSieve) {w Z : ℝ} (hwZ : w ≤ Z) (k : ℕ) : w ≤ vEnum A w Z k :=
  Work.ChenPlan.LinearSieve.Abel.enumExt_ge (fun p hp => (mem_pSet.mp hp).2.1) hwZ k

theorem vEnum_le (A : BoundingSieve) (w Z : ℝ) (k : ℕ) : vEnum A w Z k ≤ Z :=
  Work.ChenPlan.LinearSieve.Abel.enumExt_le_Z (fun p hp => (mem_pSet.mp hp).2.2) k

theorem Vnorm_Z (A : BoundingSieve) (Z : ℝ) : Vnorm A Z Z = 1 :=
  div_self (ne_of_gt (VfR_pos A Z))

theorem Vnorm_nonneg (A : BoundingSieve) (Z u : ℝ) : 0 ≤ Vnorm A Z u :=
  div_nonneg (VfR_nonneg A u) (le_of_lt (VfR_pos A Z))

theorem Vnorm_le_hprof {A : BoundingSieve} {K Z u : ℝ}
    (h : VfR A u ≤ VfR A Z * hprof K Z u) : Vnorm A Z u ≤ hprof K Z u := by
  rw [Vnorm]
  exact (div_le_iff₀ (VfR_pos A Z)).mpr (by simpa [hprof, mul_comm] using h)

theorem hprof_Z {K Z : ℝ} (hlog : Real.log Z ≠ 0) : hprof K Z Z = 1 + K / Real.log Z := by
  rw [hprof, div_self hlog, mul_one]

end

end Work.ChenPlan.LinearSieve.RIMain
