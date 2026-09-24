import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Second-countable CW complexes have countably many cells

If a Hausdorff space `Y` admits a CW-complex structure with all of `Y` as its underlying space and
`Y` is second countable, then for every `n : ℕ` the set of `n`-cells is countable.

The proof is the classical one: pick the centre `map n i 0` of each `n`-cell. Distinct cells give
distinct points (the open cells are pairwise disjoint), and each such point is isolated in the
image, because the complement of a single one of them is closed by the weak topology together with
closure-finiteness (a closed cell meets only finitely many open cells). A closed discrete subset of
a second-countable space is countable.
-/

open Set

set_option linter.style.haveILetI false

namespace Commons.Topology.CWComplex

/-- Closure-finiteness in the form used below: for an absolute CW complex, the closed `m`-cell
meets only finitely many open `n`-cells, for `n` fixed. More precisely, the set of `n`-cell indices
`i` such that `map n i 0` lies in `closedCell m j` is finite. -/
private lemma finite_cell_mem_closedCell
    {Y : Type*} [TopologicalSpace Y] {C : Set Y} [Topology.RelCWComplex C (∅ : Set Y)]
    (n m : ℕ) (j : Topology.RelCWComplex.cell C m) :
    Set.Finite {i : Topology.RelCWComplex.cell C n |
        Topology.RelCWComplex.map (C := C) n i 0 ∈ Topology.RelCWComplex.closedCell (C := C) m j} := by
  classical
  obtain ⟨I, hI⟩ :=
    Topology.RelCWComplex.cellFrontier_subset_finite_openCell (C := C) (D := (∅ : Set Y)) m j
  simp only [Set.empty_union] at hI
  have hclosed : Topology.RelCWComplex.closedCell (C := C) m j ⊆
      Topology.RelCWComplex.openCell (C := C) m j ∪
        ⋃ (l : ℕ) (_ : l < m) (k : Topology.RelCWComplex.cell C l) (_ : k ∈ I l),
          Topology.RelCWComplex.openCell (C := C) l k := by
    rw [← Topology.RelCWComplex.cellFrontier_union_openCell_eq_closedCell (C := C) (D := (∅ : Set Y))
      m j]
    exact Set.union_subset (hI.trans Set.subset_union_right) Set.subset_union_left
  rcases lt_or_ge n m with hnm | hmn
  · -- `n < m`: only open `n`-cells occurring in `I n` can meet the closed `m`-cell.
    apply Set.Finite.subset (s := (I n : Set (Topology.RelCWComplex.cell C n)))
    · exact (I n).finite_toSet
    · intro i hi
      have hxi : Topology.RelCWComplex.map (C := C) n i 0 ∈
          Topology.RelCWComplex.openCell (C := C) n i :=
        Topology.RelCWComplex.map_zero_mem_openCell (C := C) (D := (∅ : Set Y)) n i
      rcases hclosed hi with hmem | hmem
      · exfalso
        have hnd : ¬ Disjoint (Topology.RelCWComplex.openCell (C := C) n i)
            (Topology.RelCWComplex.openCell (C := C) m j) :=
          fun hd => Set.disjoint_left.1 hd hxi hmem
        have heq := Topology.RelCWComplex.eq_of_not_disjoint_openCell (C := C) (D := (∅ : Set Y)) hnd
        obtain ⟨hnl, -⟩ := Sigma.mk.inj heq
        omega
      · rcases Set.mem_iUnion.1 hmem with ⟨l, hmem⟩
        rcases Set.mem_iUnion.1 hmem with ⟨hl, hmem⟩
        rcases Set.mem_iUnion.1 hmem with ⟨k, hmem⟩
        rcases Set.mem_iUnion.1 hmem with ⟨hk, hmem⟩
        have hnd : ¬ Disjoint (Topology.RelCWComplex.openCell (C := C) n i)
            (Topology.RelCWComplex.openCell (C := C) l k) :=
          fun hd => Set.disjoint_left.1 hd hxi hmem
        have heq := Topology.RelCWComplex.eq_of_not_disjoint_openCell (C := C) (D := (∅ : Set Y)) hnd
        obtain ⟨hnl, hik⟩ := Sigma.mk.inj heq
        subst hnl
        rw [eq_of_heq hik]
        exact hk
  · rcases lt_or_eq_of_le hmn with hmn' | heq
    · -- `m < n`: no open cell of dimension `n` can meet the closed `m`-cell.
      apply Set.Finite.subset (s := (∅ : Set (Topology.RelCWComplex.cell C n)))
      · exact Set.finite_empty
      · intro i hi
        have hxi : Topology.RelCWComplex.map (C := C) n i 0 ∈
            Topology.RelCWComplex.openCell (C := C) n i :=
          Topology.RelCWComplex.map_zero_mem_openCell (C := C) (D := (∅ : Set Y)) n i
        rcases hclosed hi with hmem | hmem
        · exfalso
          have hnd : ¬ Disjoint (Topology.RelCWComplex.openCell (C := C) n i)
              (Topology.RelCWComplex.openCell (C := C) m j) :=
            fun hd => Set.disjoint_left.1 hd hxi hmem
          have heq := Topology.RelCWComplex.eq_of_not_disjoint_openCell (C := C) (D := (∅ : Set Y)) hnd
          obtain ⟨hnl, -⟩ := Sigma.mk.inj heq
          omega
        · rcases Set.mem_iUnion.1 hmem with ⟨l, hmem⟩
          rcases Set.mem_iUnion.1 hmem with ⟨hl, hmem⟩
          rcases Set.mem_iUnion.1 hmem with ⟨k, hmem⟩
          rcases Set.mem_iUnion.1 hmem with ⟨hk, hmem⟩
          have hnd : ¬ Disjoint (Topology.RelCWComplex.openCell (C := C) n i)
              (Topology.RelCWComplex.openCell (C := C) l k) :=
            fun hd => Set.disjoint_left.1 hd hxi hmem
          have heq := Topology.RelCWComplex.eq_of_not_disjoint_openCell (C := C) (D := (∅ : Set Y)) hnd
          obtain ⟨hnl, -⟩ := Sigma.mk.inj heq
          omega
    · -- `m = n`: at most the cell `j` itself qualifies.
      subst heq
      apply Set.Finite.subset (s := ({j} : Set (Topology.RelCWComplex.cell C m)))
      · exact Set.finite_singleton j
      · intro i hi
        have hxi : Topology.RelCWComplex.map (C := C) m i 0 ∈
            Topology.RelCWComplex.openCell (C := C) m i :=
          Topology.RelCWComplex.map_zero_mem_openCell (C := C) (D := (∅ : Set Y)) m i
        rcases hclosed hi with hmem | hmem
        · have hnd : ¬ Disjoint (Topology.RelCWComplex.openCell (C := C) m i)
              (Topology.RelCWComplex.openCell (C := C) m j) :=
            fun hd => Set.disjoint_left.1 hd hxi hmem
          have heq := Topology.RelCWComplex.eq_of_not_disjoint_openCell (C := C) (D := (∅ : Set Y)) hnd
          obtain ⟨-, hik⟩ := Sigma.mk.inj heq
          simpa using hik
        · exfalso
          rcases Set.mem_iUnion.1 hmem with ⟨l, hmem⟩
          rcases Set.mem_iUnion.1 hmem with ⟨hl, hmem⟩
          rcases Set.mem_iUnion.1 hmem with ⟨k, hmem⟩
          rcases Set.mem_iUnion.1 hmem with ⟨hk, hmem⟩
          have hnd : ¬ Disjoint (Topology.RelCWComplex.openCell (C := C) m i)
              (Topology.RelCWComplex.openCell (C := C) l k) :=
            fun hd => Set.disjoint_left.1 hd hxi hmem
          have heq := Topology.RelCWComplex.eq_of_not_disjoint_openCell (C := C) (D := (∅ : Set Y)) hnd
          obtain ⟨hnl, -⟩ := Sigma.mk.inj heq
          omega

/-- A second-countable Hausdorff CW complex has only countably many cells in each dimension. -/
theorem countable_cell_of_secondCountable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] (hC : Topology.CWComplex (X := Y) Set.univ) (n : ℕ) :
    Countable (hC.cell n) := by
  classical
  letI : Topology.RelCWComplex (Set.univ : Set Y) ∅ :=
    @Topology.CWComplex.instRelCWComplex Y _ Set.univ hC
  -- The centre of the `i`-th `n`-cell.
  let x : Topology.RelCWComplex.cell (Set.univ : Set Y) n → Y :=
    fun i => Topology.RelCWComplex.map (C := Set.univ) n i 0
  have hx_inj : Function.Injective x := by
    intro i j hij
    have hi : x i ∈ Topology.RelCWComplex.openCell (C := Set.univ) n i :=
      Topology.RelCWComplex.map_zero_mem_openCell (C := Set.univ) (D := ∅) n i
    have hj : x j ∈ Topology.RelCWComplex.openCell (C := Set.univ) n j :=
      Topology.RelCWComplex.map_zero_mem_openCell (C := Set.univ) (D := ∅) n j
    have hmem : x i ∈ Topology.RelCWComplex.openCell (C := Set.univ) n j := by
      rw [hij]; exact hj
    have hnd : ¬ Disjoint (Topology.RelCWComplex.openCell (C := Set.univ) n i)
        (Topology.RelCWComplex.openCell (C := Set.univ) n j) :=
      fun hd => (Set.disjoint_left.1 hd hi) hmem
    have heq := Topology.RelCWComplex.eq_of_not_disjoint_openCell (C := Set.univ) (D := ∅) hnd
    exact eq_of_heq (Sigma.mk.inj heq).2
  let P : Set Y := Set.range x
  -- A closed cell contains only finitely many of the centres.
  have hPfin : ∀ m (j : Topology.RelCWComplex.cell (Set.univ : Set Y) m),
      (P ∩ Topology.RelCWComplex.closedCell (C := Set.univ) m j).Finite := by
    intro m j
    have h := finite_cell_mem_closedCell (C := Set.univ) n m j
    have hset : P ∩ Topology.RelCWComplex.closedCell (C := Set.univ) m j =
        x '' {i : Topology.RelCWComplex.cell (Set.univ : Set Y) n |
          x i ∈ Topology.RelCWComplex.closedCell (C := Set.univ) m j} := by
      ext y; constructor
      · rintro ⟨hyP, hyC⟩
        obtain ⟨i, rfl⟩ := hyP
        exact ⟨i, hyC, rfl⟩
      · rintro ⟨i, hiC, rfl⟩
        exact ⟨⟨i, rfl⟩, hiC⟩
    rw [hset]
    exact h.image x
  -- Each centre is isolated among the centres.
  have hiso : ∀ i : Topology.RelCWComplex.cell (Set.univ : Set Y) n,
      ∃ U : Set Y, IsOpen U ∧ x i ∈ U ∧ U ∩ P = {x i} := by
    intro i
    have hclosed : IsClosed (P \ {x i}) := by
      rw [Topology.RelCWComplex.closed (Set.univ : Set Y) (P \ {x i}) (by simp)]
      refine ⟨?_, by simp⟩
      intro m j
      have hf : ((P \ {x i}) ∩ Topology.RelCWComplex.closedCell (C := Set.univ) m j).Finite := by
        apply (hPfin m j).subset
        intro y hy
        exact ⟨hy.1.1, hy.2⟩
      exact hf.isClosed
    refine ⟨(P \ {x i})ᶜ, hclosed.isOpen_compl, by simp, ?_⟩
    ext y
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    tauto
  obtain ⟨B, hBc, hBne, hBb⟩ := TopologicalSpace.exists_countable_basis Y
  -- Assign to each centre a basic open set containing exactly that centre among `P`.
  have hchoice : ∀ i : Topology.RelCWComplex.cell (Set.univ : Set Y) n,
      ∃ b : Set Y, b ∈ B ∧ x i ∈ b ∧ b ∩ P = {x i} := by
    intro i
    obtain ⟨U, hUo, hxU, hUP⟩ := hiso i
    obtain ⟨b, hbB, hxb, hbU⟩ := hBb.exists_subset_of_mem_open hxU hUo
    refine ⟨b, hbB, hxb, ?_⟩
    rw [Set.eq_singleton_iff_unique_mem]
    refine ⟨⟨hxb, Set.mem_range_self i⟩, fun y hy => ?_⟩
    have : y ∈ U ∩ P := ⟨hbU hy.1, hy.2⟩
    rw [hUP] at this
    exact this
  choose f hf using hchoice
  have hfinj : Function.Injective (fun i => (⟨f i, (hf i).1⟩ : {b : Set Y // b ∈ B})) := by
    intro i j hij
    have h1 : f i ∩ P = {x i} := (hf i).2.2
    have h2 : f j ∩ P = {x j} := (hf j).2.2
    have hbij : f i = f j := Subtype.mk.inj hij
    have : x i = x j := by
      have hsingle : ({x i} : Set Y) = {x j} := by rw [← h1, ← h2, hbij]
      simpa using hsingle
    exact hx_inj this
  haveI : Countable {b : Set Y // b ∈ B} := Set.countable_coe_iff.2 hBc
  have hcount : Countable (Topology.RelCWComplex.cell (Set.univ : Set Y) n) :=
    Function.Injective.countable hfinj
  exact hcount

end Commons.Topology.CWComplex