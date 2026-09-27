import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC6Core.Staircase
import Submission.Work.EKLC6Core.staircase_iUnion
import Submission.Work.EKLC6Core.staircase_disjoint
import Submission.Work.EKLC6Core.staircase_frontier
import Submission.Work.Misiurewicz.frontier_finite_subset

/-!
# `Work.EKLC6Core.thin_pattern_partition`

A finite measurable family `U : Fin m → X₃` whose members have *thin* frontiers — meaning that
the `V η`-collar of `∂U i` pushed to `X₃` by the action has `μ`-measure at most `c i · η` — and
which covers all of `X₃` up to measure `< ε`, can be refined to a *partition* `P : Fin N → X₃`
with

* pairwise disjoint measurable pieces covering `X₃`,
* a single exceptional piece `P i₀` with `μ (P i₀) < ε`,
* every other piece contained in some `U j`,
* and the thin-frontier estimate surviving with a single constant.

## Proof

The partition is the *staircase* associated with the family: `P (castSucc j) = staircase U j` is
the part of `U j` not covered by the earlier members `U k` (`k < j`), and the extra index
`i₀ = Fin.last m` carries the complement `(⋃ j, U j)ᶜ`.  The point of the staircase is that it
keeps the frontier under control:

`∂(staircase U j) ⊆ ∂U j ∪ ⋃_{k < j} ∂U k`  (frontier of a difference / finite union),

so `∂(P i) ⊆ ⋃ j, ∂U j` for every `i`, and the collar bound is inherited by a plain finite union
bound (no measurability of the collars is needed: `μ` is a total outer measure on sets).

The three ingredients used here — that the staircase pieces are disjoint
(`Work.EKLC6Core.staircase_disjoint`), that they cover `⋃ j, U j` (`Work.EKLC6Core.staircase_iUnion`),
and that their frontiers stay in `⋃ j, ∂U j` (`Work.EKLC6Core.staircase_frontier`) — are proved
in the neighbouring modules.
-/

namespace Work.EKLC6Core

open MeasureTheory Set
open scoped ENNReal

set_option linter.unusedVariables false

noncomputable section

/-- An index of `Fin (m+1)` which is not the last one has value `< m`; equivalently it is
`Fin.castSucc j` for a (unique) `j : Fin m`. -/
theorem val_lt_of_ne_last__thin_pattern_partition {m : ℕ} {i : Fin (m + 1)} (hi : i ≠ Fin.last m) : i.val < m := by
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp i.isLt) with h | h
  · exact h
  · exact absurd (Fin.ext h) hi

/-- **The staircase partition of a finite family.**  Given `U : Fin m → Set X`, there is a
partition of `X` into `m + 1` measurable pieces, the last of which is the complement of
`⋃ j, U j`, every other one being contained in the corresponding `U j`, and all of whose
frontiers are contained in `⋃ j, ∂U j`. -/
theorem staircase_partition_of_finite_family {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    {m : ℕ} (U : Fin m → Set X) (hUmeas : ∀ i, MeasurableSet (U i)) :
    ∃ (P : Fin (m + 1) → Set X) (i₀ : Fin (m + 1)),
      (∀ i, MeasurableSet (P i)) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (⋃ i, P i) = Set.univ ∧
      P i₀ = (⋃ j, U j)ᶜ ∧
      (∀ i, i ≠ i₀ → ∃ j, P i ⊆ U j) ∧
      (∀ i, frontier (P i) ⊆ ⋃ j, frontier (U j)) := by
  classical
  refine ⟨Fin.snoc (staircase U) ((⋃ j, U j)ᶜ), Fin.last m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- all pieces are measurable
    intro i
    by_cases hi : i = Fin.last m
    · rw [hi, Fin.snoc_last]
      exact (MeasurableSet.iUnion hUmeas).compl
    · obtain ⟨j, rfl⟩ : ∃ j : Fin m, i = Fin.castSucc j :=
        ⟨⟨i.val, val_lt_of_ne_last__thin_pattern_partition hi⟩, Fin.ext rfl⟩
      rw [Fin.snoc_castSucc]
      exact staircase_measurable hUmeas j
  · -- the pieces are pairwise disjoint
    intro i j hij
    by_cases hi : i = Fin.last m
    · rw [hi, Fin.snoc_last]
      have hji : j ≠ Fin.last m := fun h => hij (hi.trans h.symm)
      obtain ⟨j', rfl⟩ : ∃ j' : Fin m, j = Fin.castSucc j' :=
        ⟨⟨j.val, val_lt_of_ne_last__thin_pattern_partition hji⟩, Fin.ext rfl⟩
      rw [Fin.snoc_castSucc, Set.disjoint_left]
      intro x hx1 hx2
      exact hx1 (Set.mem_iUnion.mpr ⟨j', staircase_subset U j' hx2⟩)
    · by_cases hj : j = Fin.last m
      · rw [hj, Fin.snoc_last]
        obtain ⟨i', rfl⟩ : ∃ i' : Fin m, i = Fin.castSucc i' :=
          ⟨⟨i.val, val_lt_of_ne_last__thin_pattern_partition hi⟩, Fin.ext rfl⟩
        rw [Fin.snoc_castSucc, Set.disjoint_left]
        intro x hx1 hx2
        exact hx2 (Set.mem_iUnion.mpr ⟨i', staircase_subset U i' hx1⟩)
      · obtain ⟨i', rfl⟩ : ∃ i' : Fin m, i = Fin.castSucc i' :=
          ⟨⟨i.val, val_lt_of_ne_last__thin_pattern_partition hi⟩, Fin.ext rfl⟩
        obtain ⟨j', rfl⟩ : ∃ j' : Fin m, j = Fin.castSucc j' :=
          ⟨⟨j.val, val_lt_of_ne_last__thin_pattern_partition hj⟩, Fin.ext rfl⟩
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact staircase_disjoint U (fun h => hij (congrArg Fin.castSucc h))
  · -- the pieces cover everything
    rw [Set.eq_univ_iff_forall]
    intro x
    by_cases hx : x ∈ ⋃ j : Fin m, U j
    · rw [← staircase_iUnion] at hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      refine Set.mem_iUnion.mpr ⟨Fin.castSucc j, ?_⟩
      rwa [Fin.snoc_castSucc]
    · refine Set.mem_iUnion.mpr ⟨Fin.last m, ?_⟩
      rw [Fin.snoc_last]
      exact hx
  · -- the last piece is the complement of the union
    rw [Fin.snoc_last]
  · -- every other piece is contained in a member of the family
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j : Fin m, i = Fin.castSucc j :=
      ⟨⟨i.val, val_lt_of_ne_last__thin_pattern_partition hi⟩, Fin.ext rfl⟩
    refine ⟨j, ?_⟩
    rw [Fin.snoc_castSucc]
    exact staircase_subset U j
  · -- the frontiers of the pieces stay in the union of the frontiers of the family
    intro i
    by_cases hi : i = Fin.last m
    · rw [hi, Fin.snoc_last, frontier_compl]
      exact Work.Misiurewicz.frontier_iUnion_subset U
    · obtain ⟨j, rfl⟩ : ∃ j : Fin m, i = Fin.castSucc j :=
        ⟨⟨i.val, val_lt_of_ne_last__thin_pattern_partition hi⟩, Fin.ext rfl⟩
      rw [Fin.snoc_castSucc]
      exact staircase_frontier U j

/-- **Collar bound.**  If every `frontier (P i)` is contained in `⋃ j, frontier (U j)` and each
`U j` has a thin frontier with constant `cU j`, then the total `V η`-mass of the shifted
`P`-frontiers is at most `(∑ j, cU j + 1) · η` — the `+ 1` absorbing the possibility that the
index range of `P` is the degenerate one. -/
theorem smul_collar_iUnion_le (μ : MeasureTheory.Measure Work.EKLContract.X3) {m n : ℕ}
    (U : Fin m → Set Work.EKLContract.X3) (P : Fin n → Set Work.EKLContract.X3)
    {cU : Fin m → ℝ} (hcU : ∀ j, 0 < cU j) {η : ℝ} (hη : 0 < η)
    (hU : ∀ j, μ ((fun p : Work.EKLContract.SL3 × Work.EKLContract.X3 => p.1 • p.2) ''
        (Work.EKLContract.V η ×ˢ frontier (U j))) ≤ ENNReal.ofReal (cU j * η))
    (hfr : ∀ i, frontier (P i) ⊆ ⋃ j, frontier (U j)) :
    μ (⋃ i, (fun p : Work.EKLContract.SL3 × Work.EKLContract.X3 => p.1 • p.2) ''
        (Work.EKLContract.V η ×ˢ frontier (P i)))
      ≤ ENNReal.ofReal ((∑ j, cU j + 1) * η) := by
  set M : Work.EKLContract.SL3 × Work.EKLContract.X3 → Work.EKLContract.X3 :=
    fun p => p.1 • p.2 with hM
  have hsub : (⋃ i, M '' (Work.EKLContract.V η ×ˢ frontier (P i)))
      ⊆ ⋃ j, M '' (Work.EKLContract.V η ×ˢ frontier (U j)) := by
    intro x hx
    rw [Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hx⟩ := hx
    rw [Set.mem_image] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    rw [Set.mem_prod] at hq
    obtain ⟨hqV, hqfr⟩ := hq
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hfr i hqfr)
    exact ⟨j, q, ⟨hqV, hj⟩, rfl⟩
  calc μ (⋃ i, M '' (Work.EKLContract.V η ×ˢ frontier (P i)))
      ≤ μ (⋃ j, M '' (Work.EKLContract.V η ×ˢ frontier (U j))) := measure_mono hsub
    _ ≤ ∑ j : Fin m, μ (M '' (Work.EKLContract.V η ×ˢ frontier (U j))) :=
        measure_iUnion_fintype_le μ _
    _ ≤ ∑ j : Fin m, ENNReal.ofReal (cU j * η) := Finset.sum_le_sum (fun j _ => hU j)
    _ = ENNReal.ofReal (∑ j : Fin m, cU j * η) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        exact fun j _ => le_of_lt (mul_pos (hcU j) hη)
    _ = ENNReal.ofReal ((∑ j : Fin m, cU j) * η) := by rw [Finset.sum_mul]
    _ ≤ ENNReal.ofReal ((∑ j : Fin m, cU j + 1) * η) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : (0 : ℝ) ≤ ∑ j : Fin m, cU j := Finset.sum_nonneg fun j _ => (hcU j).le
        nlinarith

theorem thin_pattern_partition (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsFiniteMeasure μ] {m : ℕ} (U : Fin m → Set Work.EKLContract.X3)
    (hUmeas : ∀ i, MeasurableSet (U i))
    (hthin : ∀ i, ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η →
      μ ((fun p : Work.EKLContract.SL3 × Work.EKLContract.X3 => p.1 • p.2) ''
          ((Work.EKLContract.V η) ×ˢ frontier (U i))) ≤ ENNReal.ofReal (c * η))
    (ε : ℝ) (hε : 0 < ε)
    (hcomp : μ ((⋃ i, U i))ᶜ < ENNReal.ofReal ε) :
    ∃ (N : ℕ) (P : Fin N → Set Work.EKLContract.X3) (i₀ : Fin N) (c : ℝ),
      0 < c ∧ (∀ i, MeasurableSet (P i)) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (⋃ i, P i) = Set.univ ∧
      (∀ i, i ≠ i₀ → ∃ j, P i ⊆ U j) ∧
      μ (P i₀) < ENNReal.ofReal ε ∧
      (∀ η : ℝ, 0 < η →
        μ (⋃ i, (fun p : Work.EKLContract.SL3 × Work.EKLContract.X3 => p.1 • p.2) ''
          ((Work.EKLContract.V η) ×ˢ (frontier (P i)))) ≤ ENNReal.ofReal (c * η)) := by
  classical
  choose cU hcUpos hcUbound using hthin
  obtain ⟨P, i₀, hPmeas, hPdisj, hPcover, hPi₀, hPsub, hPfr⟩ :=
    staircase_partition_of_finite_family U hUmeas
  refine ⟨m + 1, P, i₀, (∑ j, cU j) + 1, ?_, hPmeas, hPdisj, hPcover, hPsub, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ ∑ j : Fin m, cU j := Finset.sum_nonneg fun j _ => (hcUpos j).le
    linarith
  · rw [hPi₀]
    exact hcomp
  · intro η hη
    exact smul_collar_iUnion_le μ U P hcUpos hη (fun j => hcUbound j η hη) hPfr

end

end Work.EKLC6Core
