/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The inverse of the trailing block `lacWB`

The trailing block `lacWB d n = -1 + lacSB d n` of the companion matrix (see `PolyTDefs`) is the
matrix `-(1 - t·N)` where `N = lacSB d n` is the nilpotent downward shift (`lacSB_pow_eq_zero`), and
`lacWiB d n = -∑_{k<d} (lacSB d n)^k` is the negative of the finite geometric series.  Hence
`lacWB · lacWiB = (1 - N) · ∑_{k<d} N^k = 1 - N^d = 1` and similarly `lacWiB · lacWB = 1`; this file
assembles those facts.  The Mathlib geometric-series identities used are
`mul_neg_geom_sum` and `geom_sum_mul_neg`.
-/
import Mathlib
import Submission.Work.ORHughesFree.LacNatExt.PolyTDefs
import Submission.Work.ORHughesFree.LacNatExt.ShiftDefs
import Submission.Work.ORHughesFree.LacNatExt.WB_eq_SB
import Submission.Work.ORHughesFree.LacNatExt.WiB_eq

set_option autoImplicit false

namespace Work.ORHughesFree.NaturalExtension

theorem lacWB_mul_WiB {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R] (d n : ℕ) :
    lacWB (R := R) d n * lacWiB (R := R) d n = 1 ∧ lacWiB (R := R) d n * lacWB (R := R) d n = 1 := by
  have hW : lacWB (R := R) d n = -1 + lacSB (R := R) d n := lacWB_eq_SB d n
  have hWi : lacWiB (R := R) d n = -(∑ k ∈ Finset.range d, (lacSB (R := R) d n) ^ k) := lacWiB_eq d n
  have hnil : lacSB (R := R) d n ^ d = 0 := lacSB_pow_eq_zero d n
  constructor
  · calc lacWB (R := R) d n * lacWiB (R := R) d n
        = (-1 + lacSB (R := R) d n) * (-(∑ k ∈ Finset.range d, (lacSB (R := R) d n) ^ k)) := by
          rw [hW, hWi]
      _ = (1 - lacSB (R := R) d n) * (∑ k ∈ Finset.range d, (lacSB (R := R) d n) ^ k) := by
          noncomm_ring
      _ = 1 - lacSB (R := R) d n ^ d := mul_neg_geom_sum _ _
      _ = 1 := by rw [hnil, sub_zero]
  · calc lacWiB (R := R) d n * lacWB (R := R) d n
        = (-(∑ k ∈ Finset.range d, (lacSB (R := R) d n) ^ k)) * (-1 + lacSB (R := R) d n) := by
          rw [hW, hWi]
      _ = (∑ k ∈ Finset.range d, (lacSB (R := R) d n) ^ k) * (1 - lacSB (R := R) d n) := by
          noncomm_ring
      _ = 1 - lacSB (R := R) d n ^ d := geom_sum_mul_neg _ _
      _ = 1 := by rw [hnil, sub_zero]

end Work.ORHughesFree.NaturalExtension
