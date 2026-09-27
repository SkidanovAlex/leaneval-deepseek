import Mathlib
import Submission.Work.EKLC6Core.returnTimeDefs
import Submission.Work.EKLC6Core.firstReturn_partition
import Submission.Work.EKLC6Core.towerDefs

/-!
# `Work.EKLC6Core.toReal_firstReturnSet_eq_sub_firstHitSet`

Kac's identity for the entrance tower of `T = (x ↦ aDiag t • x)` on `X₃`:

`μ (firstReturnSet t Ω (n+1)) = μ (firstHitSet T Ω n) - μ (firstHitSet T Ω (n+1))`.

The underlying set identity is

`T ⁻¹' firstHitSet T Ω n = firstReturnSet t Ω (n+1) ∪ firstHitSet T Ω (n+1)`,

a disjoint union: the points of `T ⁻¹' firstHitSet T Ω n` are those whose first visit of `Ω` after
time `0` happens at time `n + 1`, and such a point either already lies in `Ω` (giving a point of
the first-return set of level `n + 1`) or not (giving a point of the first-hit set of level
`n + 1`). Transporting along the measure-preserving map `T` and splitting the measure of a
disjoint union yields the identity; it is upgraded to `ENNReal.toReal` using that `μ` is a
probability measure.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

section Helpers

/-- Membership in a first-return set of positive level: the normal form
`x ∈ Ω ∧ Tⁱ x ∈ Ω ∧ ∀ j, 1 ≤ j → j < i → Tʲ x ∉ Ω`. -/
theorem mem_firstReturnSet_succ {t : Fin 3 → ℝ} {Ω : Set Work.EKLContract.X3} (n : ℕ)
    {x : Work.EKLContract.X3} :
    x ∈ firstReturnSet t Ω (n + 1) ↔
      x ∈ Ω ∧ (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n + 1] x ∈ Ω ∧
        ∀ j : ℕ, 1 ≤ j → j < n + 1 →
          (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[j] x ∉ Ω := by
  rw [firstReturnSet]
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, Set.mem_compl_iff,
    Finset.mem_Icc, Nat.add_sub_cancel]
  constructor
  · rintro ⟨⟨hxΩ, hxi⟩, hprev⟩
    exact ⟨hxΩ, hxi, fun j hj1 hjn => hprev j ⟨hj1, by omega⟩⟩
  · rintro ⟨hxΩ, hxi, hprev⟩
    exact ⟨⟨hxΩ, hxi⟩, fun j hj => hprev j hj.1 (by omega)⟩

/-- The first-hit sets of `T = (x ↦ aDiag t • x)` are measurable for measurable `Ω`. -/
theorem measurableSet_firstHitSet {t : Fin 3 → ℝ} {Ω : Set Work.EKLContract.X3}
    (hΩ : MeasurableSet Ω) (n : ℕ) :
    MeasurableSet
      (firstHitSet (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) Ω n) := by
  have hc : Measurable (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) := by
    fun_prop
  unfold firstHitSet
  exact ((hc.iterate n) hΩ).inter
    (Finset.measurableSet_biInter _ (fun j _ => ((hc.iterate j) hΩ).compl))

/-- The entrance-tower recursion, in set form: the preimage under `T` of the `n`-th first-hit set
of `Ω` is the disjoint union of the first-return set of level `n + 1` (the points that are already
in `Ω`, i.e. that return) and the first-hit set of level `n + 1` (the points outside `Ω`, i.e.
that enter). -/
theorem preimage_firstHitSet_eq (t : Fin 3 → ℝ) (Ω : Set Work.EKLContract.X3) (n : ℕ) :
    (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) ⁻¹'
        firstHitSet (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) Ω n =
      firstReturnSet t Ω (n + 1) ∪
        firstHitSet (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) Ω (n + 1) := by
  ext x
  simp only [Set.mem_preimage, mem_firstHitSet, Set.mem_union, mem_firstReturnSet_succ]
  constructor
  · rintro ⟨hmem, hprev⟩
    by_cases hx : x ∈ Ω
    · left
      rw [iterate_apply_self] at hmem
      refine ⟨hx, hmem, fun j hj1 hjn => ?_⟩
      have h := hprev (j - 1) (by omega)
      rwa [iterate_apply_self, Nat.sub_add_cancel hj1] at h
    · right
      rw [iterate_apply_self] at hmem
      refine ⟨hmem, fun j hj => ?_⟩
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · exact hx
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hjpos.ne'
        have h := hprev k (by omega)
        rwa [iterate_apply_self] at h
  · rintro (⟨hxΩ, hmem, hprev⟩ | ⟨hmem, hprev⟩)
    · refine ⟨hmem, fun j hj => ?_⟩
      have h := hprev (j + 1) (by omega) (by omega)
      rwa [iterate_apply_self]
    · refine ⟨hmem, fun j hj => ?_⟩
      have h := hprev (j + 1) (by omega)
      rwa [iterate_apply_self]

/-- The two pieces of the decomposition are disjoint: the first-return set of level `n + 1` lies
inside `Ω`, while the first-hit set of level `n + 1` lies in `Ωᶜ`. -/
theorem disjoint_firstReturnSet_firstHitSet_succ (t : Fin 3 → ℝ) (Ω : Set Work.EKLContract.X3)
    (n : ℕ) :
    Disjoint (firstReturnSet t Ω (n + 1))
      (firstHitSet (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) Ω (n + 1)) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [mem_firstReturnSet_succ] at hx
  rw [mem_firstHitSet] at hx'
  exact hx'.2 0 (Nat.succ_pos n) hx.1

end Helpers

theorem toReal_firstReturnSet_eq_sub_firstHitSet {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ}
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {Ω : Set Work.EKLContract.X3} (hΩ : MeasurableSet Ω) (n : ℕ) :
    (μ (Work.EKLC6Core.firstReturnSet t Ω (n + 1))).toReal =
      (μ (Work.EKLC6Core.firstHitSet (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) Ω n)).toReal -
        (μ (Work.EKLC6Core.firstHitSet (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) Ω (n + 1))).toReal := by
  have hpre : μ ((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) ⁻¹'
        firstHitSet (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) Ω n) =
      μ (firstHitSet (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) Ω n) :=
    hmp.measure_preimage (measurableSet_firstHitSet hΩ n).nullMeasurableSet
  have hB : MeasurableSet
      (firstHitSet (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) Ω (n + 1)) :=
    measurableSet_firstHitSet hΩ (n + 1)
  have hdisj := disjoint_firstReturnSet_firstHitSet_succ t Ω n
  have hsum : μ (firstReturnSet t Ω (n + 1)) +
      μ (firstHitSet (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) Ω (n + 1)) =
      μ (firstHitSet (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) Ω n) := by
    rw [← hpre, preimage_firstHitSet_eq, measure_union hdisj hB]
  have hfinR : μ (firstReturnSet t Ω (n + 1)) ≠ ∞ := measure_ne_top μ _
  have hfinB : μ (firstHitSet (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) Ω (n + 1)) ≠ ∞ :=
    measure_ne_top μ _
  have hsumR : (μ (firstReturnSet t Ω (n + 1))).toReal +
      (μ (firstHitSet (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) Ω (n + 1))).toReal =
      (μ (firstHitSet (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) Ω n)).toReal := by
    rw [← ENNReal.toReal_add hfinR hfinB, hsum]
  linarith

end Work.EKLC6Core

end
