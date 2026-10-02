import Mathlib
import Submission.Work.Cohomology.StageSplitDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Decomposing a finite union of closed balls into connected pieces

Let `U = ⋃_{j : Fin k} closedBall (c j) (r j)` be a finite union of closed balls in `ℝ^N`, and let
`S ⊆ ℝ^N` meet every connected component of `U` (hypothesis `hcomp`, phrased with
`connectedComponentIn`).  Then `U` can be written as a disjoint union of connected pieces, each
piece a union of some subfamily of the balls, and each piece meeting `S`:

`U = ⨆ i, ⋃ j ∈ idx i, closedBall (c j) (r j)`.

The pieces are the connected components of `U`; each connected component of a finite union of
(nonempty) closed balls is itself a union of the balls lying in it, because a closed ball is
preconnected.  The components are enumerated as `Fin m` via the `Fintype` structure on the finset
of components.
-/

namespace Work.Cohomology

/-- Two connected components (in a set `F`) that are distinct sets are disjoint. -/
lemma connectedComponentIn_disjoint_of_ne {α : Type*} [TopologicalSpace α] {F : Set α} {x y : α}
    (h : connectedComponentIn F x ≠ connectedComponentIn F y) :
    Disjoint (connectedComponentIn F x) (connectedComponentIn F y) := by
  rw [Set.disjoint_left]
  intro z hz1 hz2
  exact h ((connectedComponentIn_eq hz1).trans (connectedComponentIn_eq hz2).symm)

theorem exists_connected_piece_decomposition {N : ℕ} {k : ℕ}
    (c : Fin k → EuclideanSpace ℝ (Fin N)) (r : Fin k → ℝ)
    {S : Set (EuclideanSpace ℝ (Fin N))}
    (hcomp : ∀ x ∈ (⋃ j, Metric.closedBall (c j) (r j)),
      ∃ y ∈ S, x ∈ connectedComponentIn (⋃ j, Metric.closedBall (c j) (r j)) y) :
    ∃ (m : ℕ) (idx : Fin m → Finset (Fin k)) (y : Fin m → EuclideanSpace ℝ (Fin N)),
      (∀ i, y i ∈ S) ∧
      (∀ i, y i ∈ ⋃ j ∈ idx i, Metric.closedBall (c j) (r j)) ∧
      (∀ i, IsConnected (⋃ j ∈ idx i, Metric.closedBall (c j) (r j))) ∧
      (∀ i j', i ≠ j' → Disjoint (⋃ j ∈ idx i, Metric.closedBall (c j) (r j))
        (⋃ j ∈ idx j', Metric.closedBall (c j) (r j))) ∧
      (⋃ i, ⋃ j ∈ idx i, Metric.closedBall (c j) (r j))
        = ⋃ j, Metric.closedBall (c j) (r j) := by
  classical
  -- `U` is the union of the balls, and `hcomp` now refers to `U`.
  set U : Set (EuclideanSpace ℝ (Fin N)) := ⋃ j, Metric.closedBall (c j) (r j) with hU
  -- `T` is the finite set of connected components of `U` that occur (as `connectedComponentIn U (c j)`).
  set T : Finset (Set (EuclideanSpace ℝ (Fin N))) :=
    (Finset.univ.image (fun j => connectedComponentIn U (c j))).filter (fun C => C.Nonempty) with hT
  have hmemT : ∀ C, C ∈ T ↔ (∃ j, connectedComponentIn U (c j) = C) ∧ C.Nonempty := by
    intro C
    rw [hT]
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  -- For a piece `C`, `idxOf C` is the (finite) set of balls meeting `C`.
  let idxOf : Set (EuclideanSpace ℝ (Fin N)) → Finset (Fin k) :=
    fun C => Finset.univ.filter (fun j => (Metric.closedBall (c j) (r j) ∩ C).Nonempty)
  have hidx : ∀ C j, j ∈ idxOf C ↔ (Metric.closedBall (c j) (r j) ∩ C).Nonempty := by
    intro C j
    simp only [idxOf, Finset.mem_filter, Finset.mem_univ, true_and]
  -- Every element of `T` is connected.
  have hconn : ∀ C ∈ T, IsConnected C := by
    intro C hC
    obtain ⟨⟨j, hj⟩, hne⟩ := (hmemT C).mp hC
    rw [← hj]
    exact isConnected_connectedComponentIn_iff.mpr
      (connectedComponentIn_nonempty_iff.mp (hj ▸ hne))
  -- Every element of `T` is the union of the balls meeting it.
  have hpiece : ∀ C ∈ T, C = ⋃ j ∈ idxOf C, Metric.closedBall (c j) (r j) := by
    intro C hC
    obtain ⟨⟨j0, hj0⟩, hne⟩ := (hmemT C).mp hC
    apply le_antisymm
    · intro z hzC
      have hzC' : z ∈ connectedComponentIn U (c j0) := by rw [hj0]; exact hzC
      have hzU : z ∈ U := connectedComponentIn_subset U (c j0) hzC'
      obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hzU
      exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨(hidx C j).mpr ⟨z, hzj, hzC⟩, hzj⟩⟩
    · intro z hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨j, hz⟩ := hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨hjmem, hzj⟩ := hz
      obtain ⟨w, hwj, hwC⟩ := (hidx C j).mp hjmem
      have hwC' : w ∈ connectedComponentIn U (c j0) := by rw [hj0]; exact hwC
      have hwcomp : C = connectedComponentIn U w := hj0.symm.trans (connectedComponentIn_eq hwC')
      have hBU : Metric.closedBall (c j) (r j) ⊆ U :=
        Set.subset_iUnion (fun j => Metric.closedBall (c j) (r j)) j
      have hsub : Metric.closedBall (c j) (r j) ⊆ connectedComponentIn U w :=
        Metric.isPreconnected_closedBall.subset_connectedComponentIn hwj hBU
      rw [hwcomp]; exact hsub hzj
  -- Distinct elements of `T` are disjoint.
  have hdisjT : ∀ C ∈ T, ∀ C' ∈ T, C ≠ C' → Disjoint C C' := by
    intro C hC C' hC' hne
    obtain ⟨⟨j, hj⟩, _⟩ := (hmemT C).mp hC
    obtain ⟨⟨j', hj'⟩, _⟩ := (hmemT C').mp hC'
    rw [← hj, ← hj'] at hne ⊢
    exact connectedComponentIn_disjoint_of_ne hne
  -- The elements of `T` cover `U`.
  have hcover : (⋃ C ∈ T, C) = U := by
    apply le_antisymm
    · intro x hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨C, hx⟩ := hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨hC, hxC⟩ := hx
      obtain ⟨⟨j, hj⟩, _⟩ := (hmemT C).mp hC
      rw [← hj] at hxC
      exact connectedComponentIn_subset U (c j) hxC
    · intro x hxU
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxU
      have hr : 0 ≤ r j := le_trans dist_nonneg (Metric.mem_closedBall.mp hxj)
      have hcj : c j ∈ Metric.closedBall (c j) (r j) := Metric.mem_closedBall_self hr
      have hBU : Metric.closedBall (c j) (r j) ⊆ U :=
        Set.subset_iUnion (fun j => Metric.closedBall (c j) (r j)) j
      have hsub : Metric.closedBall (c j) (r j) ⊆ connectedComponentIn U (c j) :=
        Metric.isPreconnected_closedBall.subset_connectedComponentIn hcj hBU
      exact Set.mem_iUnion.mpr ⟨connectedComponentIn U (c j),
        Set.mem_iUnion.mpr ⟨(hmemT _).mpr ⟨⟨j, rfl⟩, ⟨x, hsub hxj⟩⟩, hsub hxj⟩⟩
  -- Enumerate `T` as `Fin m` and let `pc` be the resulting family of pieces.
  let m : ℕ := Fintype.card ↥T
  let e : ↥T ≃ Fin m := Fintype.equivFin ↥T
  let pc : Fin m → Set (EuclideanSpace ℝ (Fin N)) := fun i => (e.symm i).1
  have hpc_mem : ∀ i, pc i ∈ T := fun i => (e.symm i).2
  have hpc_surj : ∀ C ∈ T, ∃ i, pc i = C := by
    intro C hC
    refine ⟨e ⟨C, hC⟩, ?_⟩
    show (e.symm (e ⟨C, hC⟩)).1 = C
    rw [Equiv.symm_apply_apply]
  have hpc_union : (⋃ i, pc i) = U := by
    have h1 : (⋃ i, pc i) = ⋃ C ∈ T, C := by
      apply le_antisymm
      · intro x hx
        obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨pc i, Set.mem_iUnion.mpr ⟨hpc_mem i, hxi⟩⟩
      · intro x hx
        rw [Set.mem_iUnion] at hx
        obtain ⟨C, hx⟩ := hx
        rw [Set.mem_iUnion] at hx
        obtain ⟨hC, hxC⟩ := hx
        obtain ⟨i, hi⟩ := hpc_surj C hC
        refine Set.mem_iUnion.mpr ⟨i, ?_⟩
        rw [hi]; exact hxC
    exact h1.trans hcover
  -- Each piece meets `S`: this is `hcomp`.
  have hy : ∀ i, ∃ z, z ∈ S ∧ z ∈ pc i := by
    intro i
    have hnei : (pc i).Nonempty := ((hmemT (pc i)).mp (hpc_mem i)).2
    obtain ⟨x, hx⟩ := hnei
    obtain ⟨⟨j, hj⟩, _⟩ := (hmemT (pc i)).mp (hpc_mem i)
    have hx_in : x ∈ connectedComponentIn U (c j) := by rw [hj]; exact hx
    have hxU : x ∈ U := connectedComponentIn_subset U (c j) hx_in
    obtain ⟨y, hyS, hxy⟩ := hcomp x hxU
    refine ⟨y, hyS, ?_⟩
    have hyU : y ∈ U := connectedComponentIn_nonempty_iff.mp ⟨x, hxy⟩
    have h1 : connectedComponentIn U (c j) = connectedComponentIn U x := connectedComponentIn_eq hx_in
    have h2 : connectedComponentIn U y = connectedComponentIn U x := connectedComponentIn_eq hxy
    have h3 : connectedComponentIn U y = pc i := h2.trans (h1.symm.trans hj)
    rw [← h3]
    exact mem_connectedComponentIn hyU
  refine ⟨m, fun i => idxOf (pc i), fun i => Classical.choose (hy i), ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => (Classical.choose_spec (hy i)).1
  · intro i
    exact (hpiece (pc i) (hpc_mem i)) ▸ (Classical.choose_spec (hy i)).2
  · intro i
    rw [← hpiece (pc i) (hpc_mem i)]
    exact hconn (pc i) (hpc_mem i)
  · intro i j' hij
    rw [← hpiece (pc i) (hpc_mem i), ← hpiece (pc j') (hpc_mem j')]
    exact hdisjT (pc i) (hpc_mem i) (pc j') (hpc_mem j')
      (fun h => hij (e.symm.injective (Subtype.ext h)))
  · apply le_antisymm
    · intro x hx
      obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      rw [← hpiece (pc i) (hpc_mem i)] at hx
      rw [← hpc_union]
      exact Set.mem_iUnion.mpr ⟨i, hx⟩
    · intro x hx
      rw [← hpc_union] at hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨i, by
        show x ∈ ⋃ j ∈ idxOf (pc i), Metric.closedBall (c j) (r j)
        rw [hpiece (pc i) (hpc_mem i)] at hxi
        exact hxi⟩

end Work.Cohomology
