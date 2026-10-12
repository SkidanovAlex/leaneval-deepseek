import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.PerSector.Strat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.PerSector.Support` — the disjointness of the slot shift sets

The formal content of the **slot additivity of the localised word**: the per-slot projections
`Q_{B,i}` and the windowed amplitudes of the slot pieces are supported in the shift sets
`slotShiftSet B S i` resp. `slotAmpSet B S i` (`Defs.lean`), and those are *pairwise disjoint* as
`S` varies.  Hence a sum of slot pieces has at most one nonzero summand at every configuration, and
the square of the sum is the sum of the squares — the elementary fact behind the additivity of the
excited count and of the spectral form.

Contents:

* `exists_ne_of_ne_of_mem` — two distinct slot sets both containing `i` differ at some slot other
  than `i` (any two distinct finite sets differ somewhere, and if they both contain `i` the
  difference can be taken elsewhere);
* `slotShiftSet_disjoint`, `slotAmpSet_disjoint` — the pairwise disjointness;
* `sq_sum_eq_sum_sq`, `norm_sq_sum_eq_sum_norm_sq` — the two elementary "disjoint sum" identities
  (real and complex) used by the assembly.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.PerSector

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Classical

set_option autoImplicit false
set_option linter.unusedVariables false

variable {N : ℕ}

/-! ## 1. The combinatorial core -/

/-- **Two distinct slot sets which both contain `i` differ off `i`.** -/
theorem exists_ne_of_ne_of_mem {S S' : Finset (Fin N)} {i : Fin N} (hSS' : S ≠ S')
    (hS : i ∈ S) (hS' : i ∈ S') :
    ∃ j : Fin N, j ≠ i ∧ ((j ∈ S ∧ j ∉ S') ∨ (j ∉ S ∧ j ∈ S')) := by
  classical
  by_contra hcon
  push_neg at hcon
  exact hSS' (Finset.ext (fun j => by
    by_cases hj : j = i
    · subst hj
      exact ⟨fun _ => hS', fun _ => hS⟩
    · exact ⟨(hcon j hj).1, fun h => by
        by_contra hji
        exact (hcon j hj).2 hji h⟩))

/-- **The projection shift sets are pairwise disjoint in `S`.** -/
theorem slotShiftSet_disjoint {B : Set ℝ³} {S S' : Finset (Fin N)} {i : Fin N} (h : S ≠ S') :
    Disjoint (slotShiftSet B S i) (slotShiftSet B S' i) := by
  classical
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨hiS, hxi, hagree⟩ := hx
  obtain ⟨hiS', -, hagree'⟩ := hx'
  obtain ⟨j, hji, hcases⟩ := exists_ne_of_ne_of_mem h hiS hiS'
  rcases hcases with ⟨hjS, hjS'⟩ | ⟨hjS, hjS'⟩
  · exact hjS' ((hagree' j hji).mp ((hagree j hji).mpr hjS))
  · exact hjS ((hagree j hji).mp ((hagree' j hji).mpr hjS'))

/-- **The amplitude shift sets are pairwise disjoint in `S`.** -/
theorem slotAmpSet_disjoint {B : Set ℝ³} {S S' : Finset (Fin N)} {i : Fin N} (h : S ≠ S') :
    Disjoint (slotAmpSet B S i) (slotAmpSet B S' i) := by
  classical
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨hiS, hagree⟩ := hx
  obtain ⟨hiS', hagree'⟩ := hx'
  obtain ⟨j, hji, hcases⟩ := exists_ne_of_ne_of_mem h hiS hiS'
  rcases hcases with ⟨hjS, hjS'⟩ | ⟨hjS, hjS'⟩
  · exact hjS' ((hagree' j hji).mp ((hagree j hji).mpr hjS))
  · exact hjS ((hagree j hji).mp ((hagree' j hji).mpr hjS'))

/-! ## 2. The disjoint-sum identities -/

/-- **A sum of pairwise-orthogonal reals has square equal to the sum of the squares.** -/
theorem sq_sum_eq_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * f j = 0) :
    (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, (f i) ^ 2 := by
  classical
  have key : (∑ i ∈ s, f i) * (∑ i ∈ s, f i) = ∑ i ∈ s, f i * f i := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_eq_single i (fun j hj hji => h i hi j hj (Ne.symm hji))
      (fun hnot => absurd hi hnot)
  rw [sq, key]
  exact Finset.sum_congr rfl (fun i _ => (sq (f i)).symm)

/-- **A sum of pairwise-orthogonal complex numbers has squared norm equal to the sum of the squared
norms.** -/
theorem norm_sq_sum_eq_sum_norm_sq {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * f j = 0) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
  classical
  by_cases hex : ∃ i ∈ s, f i ≠ 0
  · obtain ⟨i, hi, hfi⟩ := hex
    have hzero : ∀ j ∈ s, j ≠ i → f j = 0 := by
      intro j hj hji
      rcases mul_eq_zero.mp (h i hi j hj (Ne.symm hji)) with h1 | h2
      · exact absurd h1 hfi
      · exact h2
    rw [Finset.sum_eq_single i (fun j hj hji => hzero j hj hji) (fun hnot => absurd hi hnot),
      Finset.sum_eq_single i (fun j hj hji => by rw [hzero j hj hji]; simp)
        (fun hnot => absurd hi hnot)]
  · push_neg at hex
    have hz : ∑ i ∈ s, f i = 0 := Finset.sum_eq_zero (fun i hi => hex i hi)
    have hz2 : ∑ i ∈ s, ‖f i‖ ^ 2 = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [hex i hi]; simp)
    rw [hz, hz2]
    simp

end Work.PerSector
