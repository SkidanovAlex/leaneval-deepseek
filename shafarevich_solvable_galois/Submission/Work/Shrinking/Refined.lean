/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The refinement `P_{(i,j)} = (P_i ∩ P_j)P_{i+1}` of the `p`-central series

Definition 3 of Schmidt–Wingberg refines the descending `p`-central series by
`P_{(i,j)} := (P_i ∩ P_j) P_{i+1}` for `i, j ≥ 1`, ordered lexicographically with
`τ + 1 = (i, j+1)` for `i > j` and `τ + 1 = (i+1, 1)` for `τ = (i,i)`.

Indexing: `Work.Shrinking.pCentralRefined p P i j` is the paper's `P_{(i,j)}`, and
`pCentralSeries p P n` is the paper's `P_{n+1}` (see `Work.Shrinking.PCentral`).

## Main results

* `Work.Shrinking.pCentralRefined_one` : `P_{(i,1)} = P_i`.
* `Work.Shrinking.pCentralRefined_eq_succ` : `P_{(i,j)} = P_{i+1}` for `j > i`.
* `Work.Shrinking.pCentralRefined_le_self_succ_j` : the refinement is descending in `j`.
* `Work.Shrinking.instNormalPCentralRefined`, `instCharacteristicPCentralRefined`,
  `map_pCentralRefined_eq` : every `P_{(i,j)}` is characteristic, hence invariant under
  every automorphism of `P`.
-/

import Mathlib
import Submission.Work.Shrinking.PCentral
import Submission.Work.Shrinking.pCentralSeries_le_succ
import Submission.Work.Shrinking.pCentralSeries_antitone
import Submission.Work.Shrinking.pCentralSeries_normal
import Submission.Work.Shrinking.pCentralSeries_characteristic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Shrinking

set_option linter.style.haveILetI false

universe u

variable {P : Type*} [Group P]

/-- `P_{(i,1)} = P_i`: the refinement starts with the original series. -/
theorem pCentralRefined_one (p : ℕ) (i : ℕ) :
    pCentralRefined p P i 1 = pCentralSeries p P (i - 1) := by
  rw [pCentralRefined, Nat.sub_self, pCentralSeries_zero, inf_top_eq, sup_eq_left]
  exact pCentralSeries_antitone p P (Nat.sub_le i 1)

/-- `P_{(i,j)} = P_{i+1}` for `j > i`: the refinement ends at the next term of the series. -/
theorem pCentralRefined_eq_succ (p : ℕ) {i j : ℕ} (hij : i < j) :
    pCentralRefined p P i j = pCentralSeries p P i := by
  rw [pCentralRefined, sup_eq_right]
  exact le_trans inf_le_right (pCentralSeries_antitone p P (Nat.le_sub_one_of_lt hij))

/-- The refinement is descending in the second index. -/
theorem pCentralRefined_le_self_succ_j (p : ℕ) (i j : ℕ) :
    pCentralRefined p P i (j + 1) ≤ pCentralRefined p P i j := by
  rw [pCentralRefined, pCentralRefined, Nat.add_sub_cancel]
  refine sup_le_sup (le_inf inf_le_left ?_) le_rfl
  exact le_trans inf_le_right (pCentralSeries_antitone p P (Nat.sub_le j 1))

/-- Every `P_{(i,j)}` is a normal subgroup. -/
instance instNormalPCentralRefined (p : ℕ) (i j : ℕ) : (pCentralRefined p P i j).Normal := by
  haveI h₁ : (pCentralSeries p P (i - 1)).Normal := pCentralSeries_normal p P (i - 1)
  haveI h₂ : (pCentralSeries p P (j - 1)).Normal := pCentralSeries_normal p P (j - 1)
  haveI h₃ : (pCentralSeries p P i).Normal := pCentralSeries_normal p P i
  rw [pCentralRefined]
  infer_instance

/-- Every `P_{(i,j)}` is a characteristic subgroup. -/
instance instCharacteristicPCentralRefined (p : ℕ) (i j : ℕ) :
    (pCentralRefined p P i j).Characteristic := by
  haveI h₁ : (pCentralSeries p P (i - 1)).Characteristic := pCentralSeries_characteristic p P (i - 1)
  haveI h₂ : (pCentralSeries p P (j - 1)).Characteristic := pCentralSeries_characteristic p P (j - 1)
  haveI h₃ : (pCentralSeries p P i).Characteristic := pCentralSeries_characteristic p P i
  rw [pCentralRefined]
  infer_instance

/-- Every `P_{(i,j)}` is invariant under every automorphism of `P`. -/
theorem map_pCentralRefined_eq (p : ℕ) (φ : P ≃* P) (i j : ℕ) :
    (pCentralRefined p P i j).map φ.toMonoidHom = pCentralRefined p P i j :=
  Subgroup.characteristic_iff_map_eq.mp (instCharacteristicPCentralRefined (P := P) p i j) φ

end Work.Shrinking
