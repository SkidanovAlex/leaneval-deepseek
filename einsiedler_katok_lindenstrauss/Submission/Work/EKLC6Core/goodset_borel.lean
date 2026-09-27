import Mathlib
import Submission.Work.EKLC6Core.UBoxDef
import Submission.Work.EKLC6Core.countable_dense_subgroup
import Submission.Work.EKLC6Core.dense_disjoint_iff
import Submission.Work.EKLComp.measurableSet_smul_mem_atom

/-!
# `Work.EKLC6Core.goodset_borel`

The good set of "comparable atoms" (Pisa 7.34) is Borel.

For a closed subgroup `U ≤ SL₃(ℝ)`, a σ-algebra `A` and `Z ∈ A` such that `A` is a *plaque
algebra* for `U` on `Z` (frozen `EKLContract.IsPlaqueAlgebra`: `A ≤ borel X₃`, `A` countably
generated, and for `y ∈ Z` the atom `[y]_A` is an open bounded `U`-plaque inside `Z`), and for
every `R : ℝ` the set

`{y ∈ Z | shape A U y ⊆ UBox U R}`

of points whose atom shape is contained in the closed entrywise box `UBox U R ⊆ U` is Borel.

## The argument

`shape A U y = {u ∈ U | u • y ∈ [y]_A}` is an *open* subset of `U` (plaque condition), and
`UBox U R = U ∩ {g | ∀ i j, |g i j| ≤ R}`.  So on `Z` the condition `shape A U y ⊆ UBox U R`
is the disjointness of the two open sets `shape A U y` and `O₂ := U ∩ {g | ¬ ∀ i j, |g i j| ≤ R}`.

Since `SL₃(ℝ)` is second countable, `O₂` has a countable subset `D` meeting every relatively open
subset of `O₂` (`EKLC6Core.exists_countable_dense_subset_of_secondCountable`).  A nonempty open
set meets such a `D`, so

`shape A U y ⊆ UBox U R  ↔  ∀ d ∈ D, d ∉ shape A U y  ↔  ∀ d ∈ D, d • y ∉ [y]_A`

(`EKLC6Core.dense_disjoint_iff`).  Each of the sets `{y | d • y ∉ [y]_A}` is Borel: it is the
complement of `{y | d • y ∈ [y]_A}`, which is
`Work.EKLComp.measurableSet_smul_mem_atom` (an atom is cut out by a countable generating family,
and `y ↦ d • y` is continuous).  Finally `Z` is Borel because `A ≤ borel X₃`, and a countable
intersection of Borel sets is Borel.

Note that the hypothesis `IsClosed U` is not needed by this argument; it is kept because it is
part of the interface in which the lemma is consumed.
-/

set_option linter.unusedVariables false

open MeasureTheory
open Work.EKLContract

namespace Work.EKLC6Core

theorem goodset_borel {U : Subgroup Work.EKLContract.SL3}
    (hUc : IsClosed (U : Set Work.EKLContract.SL3))
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplq : Work.EKLContract.IsPlaqueAlgebra U Z A) (R : ℝ) :
    @MeasurableSet Work.EKLContract.X3 (borel Work.EKLContract.X3)
      {y | y ∈ Z ∧ Work.EKLContract.shape A U y ⊆ Work.EKLC6Core.UBox U R} := by
  obtain ⟨hAle, ⟨b, hbc, hAeq⟩, hZ, hS⟩ := hplq
  -- The open set `U ∩ {entries not all ≤ R}`.
  set O₂ : Set SL3 := (U : Set SL3) ∩ {g : SL3 | ¬ ∀ i j, |g i j| ≤ R} with hO₂def
  have hO₂sub : O₂ ⊆ (U : Set SL3) := by rw [hO₂def]; exact Set.inter_subset_left
  -- A countable subset of `O₂` meeting every relatively open subset of `O₂`.
  obtain ⟨D, hDc, hDsub, hDense⟩ :=
    exists_countable_dense_subset_of_secondCountable (X := SL3) O₂
  -- `Z` is Borel.
  have hZmeas : MeasurableSet[(borel X3)] Z := hAle Z hZ
  -- Each piece `{y | d • y ∉ atom A y}` is Borel.
  have hpiece : ∀ d : SL3, MeasurableSet[(borel X3)] {y : X3 | d • y ∉ atom A y} := by
    intro d
    have h := Work.EKLComp.measurableSet_smul_mem_atom (𝔪 := ⟨A⟩) hAle ⟨b, hbc, hAeq⟩ d
    rw [show {y : X3 | d • y ∉ atom A y} = {x : X3 | d • x ∈ atom A x}ᶜ by
      ext y; simp]
    exact h.compl
  -- The characterisation of the good set on `Z`.
  have hkey : ∀ y ∈ Z, (shape A U y ⊆ UBox U R ↔ ∀ d ∈ D, d • y ∉ atom A y) := by
    intro y hy
    obtain ⟨O, hOopen, hOeq⟩ := (hS y hy).2.2.1
    -- Step 1: `shape ⊆ UBox` is disjointness from `O₂`.
    have hstep : (shape A U y ⊆ UBox U R) ↔ (O ∩ (U : Set SL3)) ∩ O₂ = ∅ := by
      rw [hOeq, hO₂def]
      constructor
      · intro h
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨⟨hxO, hxU⟩, hxU', hxR⟩
        exact hxR (h ⟨hxO, hxU⟩).2
      · intro h x hx
        refine ⟨hx.2, ?_⟩
        by_contra hxR
        exact (Set.eq_empty_iff_forall_notMem.mp h) x ⟨hx, hx.2, hxR⟩
    -- Step 2: disjointness is detected on a countable dense subset.
    have hdd : (O ∩ (U : Set SL3)) ∩ O₂ = ∅ ↔ ∀ d ∈ D, d ∉ O ∩ (U : Set SL3) :=
      dense_disjoint_iff hOopen hO₂sub hDsub hDense
    -- Step 3: replace `O ∩ U` by the shape.
    have hstep2 : (∀ d ∈ D, d ∉ O ∩ (U : Set SL3)) ↔ ∀ d ∈ D, d ∉ shape A U y := by
      constructor
      · intro h d hd; rw [hOeq]; exact h d hd
      · intro h d hd; rw [hOeq] at h; exact h d hd
    -- Step 4: `d ∉ shape` is `d • y ∉ atom A y` for `d ∈ U`.
    have hstep3 : (∀ d ∈ D, d ∉ shape A U y) ↔ ∀ d ∈ D, d • y ∉ atom A y := by
      constructor
      · intro h d hd hmem
        exact h d hd ⟨hO₂sub (hDsub hd), hmem⟩
      · intro h d hd hmem
        exact h d hd hmem.2
    exact hstep.trans (hdd.trans (hstep2.trans hstep3))
  -- Assemble.
  have hset : {y : X3 | y ∈ Z ∧ shape A U y ⊆ UBox U R} =
      Z ∩ ⋂ d ∈ D, {y : X3 | d • y ∉ atom A y} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hyZ, hsub⟩
      exact ⟨hyZ, fun d hd => (hkey y hyZ).mp hsub d hd⟩
    · rintro ⟨hyZ, h⟩
      exact ⟨hyZ, (hkey y hyZ).mpr (fun d hd => h d hd)⟩
  rw [hset]
  exact hZmeas.inter (MeasurableSet.biInter hDc (fun d _ => hpiece d))

end Work.EKLC6Core
