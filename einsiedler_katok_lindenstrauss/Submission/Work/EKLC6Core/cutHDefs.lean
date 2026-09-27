import Mathlib
import Submission.Work.EKLC6Core.cutSetup
import Submission.Work.EKLC6Core.cut_defs
import Submission.Work.EKLC6Core.atom_gen_cut
import Submission.Work.EKLC6Core.exists_base_sat_sep
import Submission.Work.EKLC6Core.shell_borel_cantelli
import Submission.Work.EKLC6Core.ae_free_orbit_of_contraction

/-!
# `Work.EKLC6Core.cutHDefs` — vocabulary for the "good set" of the cut (Pisa 7.38)

This module fixes the interface through which the cut construction (`Work.EKLC6Core.CutData`,
Pisa 7.38) feeds the descending plaque algebra `A = pastSig t M` of the target
`Work.EKLC6Core.exists_desc_subordinate`.

* `shellThin S η` is the `η`-thickening of the union of the frontiers of the cells and of the
  exceptional piece `bad`; by the thin-boundary fields of `CutData` its measure is `O (η)`.
* `famAtom S O` is the generating family of the cut σ-algebra used by
  `Work.EKLC6Core.atom_gen_cut` (the cell-wise cylinder generators together with `bad`), and
  `MCut S O` is the σ-algebra it generates.
* `CutGood S t C μ0 N` is the *good set*: the points of the cells whose **whole forward orbit**
  stays in the cells and in `bad`, is free (trivial `U`-stabiliser), and is at `C μ0ⁿ`-distance
  from the shell at every time `n ≥ N`.

The mathematical content of the last definition is Pisa 7.31: for a.e. point the orbit stays
`C μ0ⁿ`-deep inside the partition for every `C` and all large `n` (Borel–Cantelli).  The
quantitative form of that statement used by the assembly is `CutGood_measure_le` together with
`exists_borel_subset_CutGood`.
-/

open MeasureTheory Set Topology Filter
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

variable {μ : MeasureTheory.Measure X3} {U : Subgroup SL3} {ε : ℝ}

/-- The thin shell of the cut at scale `η`: the union of the `η`-thickenings of the frontiers of
the cells and of the exceptional piece. -/
def shellThin (S : CutData μ U ε) (η : ℝ) : Set X3 :=
  (⋃ i, VThick η (frontier (S.cell i))) ∪ VThick η (frontier S.bad)

/-- The unthickened shell (the union of the frontiers). -/
def shell0 (S : CutData μ U ε) : Set X3 :=
  (⋃ i, frontier (S.cell i)) ∪ frontier S.bad

/-- The shell at scale `η` contains the unthickened shell. -/
theorem subset_shellThin (S : CutData μ U ε) {η : ℝ} (hη : 0 < η) :
    shell0 S ⊆ shellThin S η := by
  refine Set.union_subset (Set.iUnion_subset fun i => ?_) ?_
  · intro z hz; exact Or.inl (Set.mem_iUnion.mpr ⟨i, subset_VThick hη _ hz⟩)
  · intro z hz; exact Or.inr (subset_VThick hη _ hz)

/-- **The shell has linear measure.**  The thin-boundary fields of the cut give a constant `C` with
`μ (shellThin S η) ≤ C η` for every `η > 0`. -/
theorem shellThin_bound (S : CutData μ U ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → μ (shellThin S η) ≤ ENNReal.ofReal (C * η) := by
  set D : ℝ := max S.c 0 + 1 with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hcD : S.c ≤ D := by
    rw [hDdef]; exact le_of_lt (lt_of_le_of_lt (le_max_left _ _) (lt_add_one _))
  refine ⟨2 * D, by positivity, fun η hη => ?_⟩
  have hstep : ENNReal.ofReal (S.c * η) ≤ ENNReal.ofReal (D * η) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcD (le_of_lt hη))
  have hDη : 0 < D * η := mul_pos hDpos hη
  calc μ (shellThin S η)
      ≤ μ (⋃ i, VThick η (frontier (S.cell i))) + μ (VThick η (frontier S.bad)) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (S.c * η) + ENNReal.ofReal (S.c * η) :=
        add_le_add (S.hthin η hη) (S.hthin_bad η hη)
    _ ≤ ENNReal.ofReal (D * η) + ENNReal.ofReal (D * η) := add_le_add hstep hstep
    _ = ENNReal.ofReal (D * η + D * η) :=
        (ENNReal.ofReal_add (le_of_lt hDη) (le_of_lt hDη)).symm
    _ = ENNReal.ofReal (2 * D * η) := by
        congr 1; ring

/-! ## The generating family of the cut σ-algebra -/

/-- The generating family used by `Work.EKLC6Core.atom_gen_cut`: the cell-wise cylinder
generators together with the exceptional piece. -/
@[reducible] def famAtom (S : CutData μ U ε) (O : ℕ → Set SL3) : Set (Set X3) :=
  Set.range (fun p : Fin S.N × ℕ => genCell S O p.1 p.2) ∪ {S.bad}

/-- The cut σ-algebra of the family `famAtom`. -/
@[reducible] def MCut (S : CutData μ U ε) (O : ℕ → Set SL3) : MeasurableSpace X3 :=
  MeasurableSpace.generateFrom (famAtom S O)

/-- Each member of the generating family is open. -/
theorem isOpen_famAtom (S : CutData μ U ε) (O : ℕ → Set SL3) (hO : ∀ m, IsOpen (O m)) :
    ∀ A ∈ famAtom S O, IsOpen A := by
  intro A hA
  rcases hA with ⟨p, rfl⟩ | rfl
  · exact isOpen_genCell S O hO p.1 p.2
  · exact S.hbad_open

/-- The cut σ-algebra is contained in the Borel σ-algebra (all its generators are open). -/
theorem MCut_le_borel (S : CutData μ U ε) (O : ℕ → Set SL3) (hO : ∀ m, IsOpen (O m)) :
    MCut S O ≤ borel X3 :=
  MeasurableSpace.generateFrom_le fun _ hA => (isOpen_famAtom S O hO _ hA).measurableSet

/-- **An enumeration of the generating family by `ℕ`.**  The family is countable (countably many
cylinder generators together with one more piece) and nonempty, so it is the range of a sequence
of open sets. -/
theorem exists_enum_famAtom (S : CutData μ U ε) (O : ℕ → Set SL3) (hO : ∀ m, IsOpen (O m)) :
    ∃ b : ℕ → Set X3, (∀ n, IsOpen (b n)) ∧ Set.range b = famAtom S O := by
  have hcount : (famAtom S O).Countable :=
    Set.Countable.union (Set.countable_range _) (Set.countable_singleton _)
  obtain ⟨b, hb⟩ := hcount.exists_eq_range ⟨S.bad, Or.inr rfl⟩
  exact ⟨b, fun n => isOpen_famAtom S O hO _ (hb ▸ Set.mem_range_self n), hb.symm⟩

/-! ## The good set -/

/-- The set of points at which the `U`-action is free. -/
def cutFree (U : Subgroup SL3) : Set X3 := {x : X3 | ∀ u ∈ U, u • x = x → u = 1}

/-- **The good set of the cut.**  A point is good if

* it lies in one of the cells (so that its level-`0` shape is bounded),
* its whole forward orbit stays in the cells and in `bad` (so that the level-`n` shapes are
  relatively open sets described by the cell/bad structure),
* its whole forward orbit is free (so that the shape of the `M`-atom is the closed condition
  `u • y ∈ Q_i ∧ u * lift ∈ V (10 ρ) * g_i`),
* at every time `n ≥ N` it is at distance `C μ0ⁿ` from the shell (so that the atom of the
  descending σ-algebra contains the `U`-ball of radius `≍ μ0ⁿ`). -/
def CutGood (S : CutData μ U ε) (t : Fin 3 → ℝ) (C μ0 : ℝ) (N : ℕ) : Set X3 :=
  {y : X3 | y ∈ ⋃ i, S.cell i} ∩
  {y : X3 | ∀ n : ℕ, (((fun x : X3 => aDiag t • x)^[n]) y) ∈ (⋃ i, S.cell i) ∪ S.bad} ∩
  {y : X3 | ∀ n : ℕ, (((fun x : X3 => aDiag t • x)^[n]) y) ∈ cutFree U} ∩
  {y : X3 | ∀ n : ℕ, N ≤ n →
      (((fun x : X3 => aDiag t • x)^[n]) y) ∉ shellThin S (C * μ0 ^ n)}

variable {S : CutData μ U ε} {t : Fin 3 → ℝ} {C μ0 : ℝ} {N : ℕ}

theorem mem_CutGood {y : X3} :
    y ∈ CutGood S t C μ0 N ↔
      (y ∈ ⋃ i, S.cell i) ∧
      (∀ n : ℕ, (((fun x : X3 => aDiag t • x)^[n]) y) ∈ (⋃ i, S.cell i) ∪ S.bad) ∧
      (∀ n : ℕ, (((fun x : X3 => aDiag t • x)^[n]) y) ∈ cutFree U) ∧
      (∀ n : ℕ, N ≤ n →
        (((fun x : X3 => aDiag t • x)^[n]) y) ∉ shellThin S (C * μ0 ^ n)) := by
  simp only [CutGood, Set.mem_inter_iff, Set.mem_ofPred_eq]
  tauto

theorem CutGood_subset_cell {y : X3} (hy : y ∈ CutGood S t C μ0 N) :
    y ∈ ⋃ i, S.cell i := (mem_CutGood.mp hy).1

theorem CutGood_orbit_mem {y : X3} (hy : y ∈ CutGood S t C μ0 N) (n : ℕ) :
    (((fun x : X3 => aDiag t • x)^[n]) y) ∈ (⋃ i, S.cell i) ∪ S.bad :=
  (mem_CutGood.mp hy).2.1 n

theorem CutGood_free {y : X3} (hy : y ∈ CutGood S t C μ0 N) (n : ℕ) :
    (((fun x : X3 => aDiag t • x)^[n]) y) ∈ cutFree U := (mem_CutGood.mp hy).2.2.1 n

theorem CutGood_deep {y : X3} (hy : y ∈ CutGood S t C μ0 N) {n : ℕ} (hn : N ≤ n) :
    (((fun x : X3 => aDiag t • x)^[n]) y) ∉ shellThin S (C * μ0 ^ n) :=
  (mem_CutGood.mp hy).2.2.2 n hn

/-- **The good set is large.**  Its complement is contained in the union of the exceptional piece,
the complement of the cells and the set of points whose orbit meets the shell at a time `n ≥ N`. -/
theorem CutGood_measure_le {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    (S : CutData μ U ε) (t : Fin 3 → ℝ) (hmp : MeasurePreserving
      (fun x : X3 => aDiag t • x) μ μ) (hfree : ∀ᵐ x ∂μ, x ∈ cutFree U)
    {C μ0 : ℝ} (N : ℕ) :
    μ (CutGood S t C μ0 N)ᶜ ≤ μ S.bad +
      μ (⋃ n ∈ Set.Ici N, ((fun x : X3 => aDiag t • x)^[n]) ⁻¹' shellThin S (C * μ0 ^ n)) := by
  set φ : X3 → X3 := fun x => aDiag t • x with hφ
  set A1 : Set X3 := (⋃ i, S.cell i)ᶜ with hA1
  set A2 : Set X3 := ⋃ n : ℕ, (φ^[n]) ⁻¹' ((⋃ i, S.cell i) ∪ S.bad)ᶜ with hA2
  set A3 : Set X3 := ⋃ n : ℕ, (φ^[n]) ⁻¹' (cutFree U)ᶜ with hA3
  set A4 : Set X3 := ⋃ n ∈ Set.Ici N, (φ^[n]) ⁻¹' shellThin S (C * μ0 ^ n) with hA4
  have hA2zero : μ A2 = 0 := by
    rw [hA2]
    exact measure_iUnion_null fun n => (hmp.iterate n).preimage_null S.hcover
  have hA3zero : μ A3 = 0 := by
    rw [hA3]
    refine measure_iUnion_null fun n => (hmp.iterate n).preimage_null ?_
    rwa [MeasureTheory.ae_iff] at hfree
  -- `μ A1 = μ (bad)`: the exceptional piece is contained in the complement of the cells
  have hA1eq : μ A1 = μ S.bad := by
    refine le_antisymm ?_ ?_
    · have hcom : A1 ⊆ S.bad ∪ A2 := by
        intro x hx
        by_cases hxb : x ∈ S.bad
        · exact Or.inl hxb
        · refine Or.inr (Set.mem_iUnion.mpr ⟨0, ?_⟩)
          simpa using (show x ∉ (⋃ i, S.cell i) ∪ S.bad from fun h => h.elim hx hxb)
      calc μ A1 ≤ μ (S.bad ∪ A2) := measure_mono hcom
        _ ≤ μ S.bad + μ A2 := measure_union_le _ _
        _ = μ S.bad := by rw [hA2zero, add_zero]
    · rw [hA1]
      refine measure_mono fun x hx hxc => ?_
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxc
      exact Set.disjoint_left.mp (S.hbad_disj i) hi hx
  have hstep : (CutGood S t C μ0 N)ᶜ ⊆ A1 ∪ (A2 ∪ (A3 ∪ A4)) := by
    intro y hy
    by_cases h1 : y ∈ ⋃ i, S.cell i
    · by_cases h2 : ∀ n : ℕ, (φ^[n]) y ∈ (⋃ i, S.cell i) ∪ S.bad
      · by_cases h3 : ∀ n : ℕ, (φ^[n]) y ∈ cutFree U
        · have h4 : ¬ ∀ n : ℕ, N ≤ n → (φ^[n]) y ∉ shellThin S (C * μ0 ^ n) :=
            fun h4 => hy (mem_CutGood.mpr ⟨h1, h2, h3, h4⟩)
          push Not at h4
          obtain ⟨n, hn, hnmem⟩ := h4
          refine Or.inr (Or.inr (Or.inr ?_))
          rw [hA4]
          exact Set.mem_iUnion₂.mpr ⟨n, hn, hnmem⟩
        · push Not at h3
          obtain ⟨n, hnmem⟩ := h3
          refine Or.inr (Or.inr (Or.inl ?_))
          rw [hA3]
          exact Set.mem_iUnion.mpr ⟨n, hnmem⟩
      · push Not at h2
        obtain ⟨n, hnmem⟩ := h2
        refine Or.inr (Or.inl ?_)
        rw [hA2]
        exact Set.mem_iUnion.mpr ⟨n, hnmem⟩
    · exact Or.inl h1
  calc μ (CutGood S t C μ0 N)ᶜ ≤ μ (A1 ∪ (A2 ∪ (A3 ∪ A4))) := measure_mono hstep
    _ ≤ μ A1 + μ (A2 ∪ (A3 ∪ A4)) := measure_union_le _ _
    _ ≤ μ A1 + (μ A2 + μ (A3 ∪ A4)) := by
        gcongr; exact measure_union_le _ _
    _ ≤ μ A1 + (μ A2 + (μ A3 + μ A4)) := by
        gcongr; exact measure_union_le _ _
    _ = μ S.bad + μ A4 := by
        rw [hA1eq, hA2zero, hA3zero]; simp
    _ = μ S.bad + μ (⋃ n ∈ Set.Ici N,
          ((fun x : X3 => aDiag t • x)^[n]) ⁻¹' shellThin S (C * μ0 ^ n)) := by
        rw [hA4]

/-- **A Borel core of the good set of large measure.**  If the good set misses less than `ε`, it
contains a *Borel* set which misses less than `ε` (using `toMeasurable` on its complement). -/
theorem exists_borel_subset_CutGood {μ : MeasureTheory.Measure X3} (S : CutData μ U ε)
    {t : Fin 3 → ℝ} {C μ0 : ℝ} {N : ℕ} {ε' : ENNReal}
    (h : μ (CutGood S t C μ0 N)ᶜ < ε') :
    ∃ H : Set X3, MeasurableSet H ∧ H ⊆ CutGood S t C μ0 N ∧ μ Hᶜ < ε' := by
  refine ⟨(MeasureTheory.toMeasurable μ (CutGood S t C μ0 N)ᶜ)ᶜ,
    (MeasureTheory.measurableSet_toMeasurable μ _).compl, ?_, ?_⟩
  · intro x hx
    by_contra hcon
    exact hx (MeasureTheory.subset_toMeasurable μ _ hcon)
  · rw [compl_compl, MeasureTheory.measure_toMeasurable]
    exact h

end Work.EKLC6Core
