import Mathlib
import Submission.Work.Cells.Connell.Defs
import Submission.Work.Cells.Connell.Basic
import Submission.Work.Cells.Connell.cubeChart_injOn
import Submission.Work.Cells.Connell.cubeChart_isOpen_image_openCube
import Submission.Work.Cells.Connell.cubeChart_isCompact_image_closedCube
import Submission.Work.Cells.Connell.cubeChart_homeoOn
import Submission.Work.Cells.Connell.cubeChart_homeoOn_apply
import Submission.Work.Cells.Connell.cubeChart_of_isOpenCell
import Submission.Work.Cells.Connell.exists_cubeChart_subcube
import Submission.Work.Cells.Connell.exists_notMem_image_of_thinFamily
import Submission.Work.Cells.Connell.exists_thinFamily_of_domDim
import Submission.Work.Cells.Connell.meshLT_dist_lt
import Submission.Work.Cells.Connell.extOverDisc_of_homeomorph
import Submission.Work.Cells.Connell.cellCover_of_two_more
import Submission.Work.Cells.Connell.exists_isCompact_subset_covering
import Submission.Work.Cells.Connell.exists_closedCube_subset_of_isCompact_subset_openCube
import Submission.Work.Cells.Connell.exists_closedCube_of_isCompact_subset_image_openCube
import Submission.Work.Cells.Connell.exists_mesh_of_chart_cover
import Submission.Work.Cells.Connell.engulf_skel
import Submission.Work.Cells.Connell.stretch_step
import Submission.Work.Cells.Connell.connell_aux

namespace Work.Cells.Connell

open Set Metric

theorem connell_step {n : ℕ} (hn : 5 ≤ n) {M : Type*} [MetricSpace M] [CompactSpace M]
    (A : Assumptions n M) (hloc : PL.LocCube n M)
    (hconn : ∀ j, j + 1 ≤ n → PL.ExtOverDisc M j) (k : ℕ) :
    PL.CellCover n M (k + 3) → PL.CellCover n M (k + 2) := by
  intro h
  obtain ⟨W, hW, hWcov⟩ := h
  -- compact cores
  obtain ⟨K, hK, hKcov⟩ := exists_isCompact_subset_covering W (fun i => (hW i).1) hWcov
  -- the three distinguished indices
  let iA : Fin (k + 3) := ⟨k, by omega⟩
  let iB : Fin (k + 3) := ⟨k + 1, by omega⟩
  let iC : Fin (k + 3) := ⟨k + 2, by omega⟩
  -- charts for the three distinguished cells
  obtain ⟨cA, hcA⟩ := cubeChart_of_isOpenCell (hW iA)
  obtain ⟨cB, hcB⟩ := cubeChart_of_isOpenCell (hW iB)
  obtain ⟨cC, hcC⟩ := cubeChart_of_isOpenCell (hW iC)
  -- shrink the cores into closed sub-cubes
  obtain ⟨αA, hαA0, hαA1, hαAsub⟩ :=
    exists_closedCube_of_isCompact_subset_image_openCube cA (hK iA).1 (by rw [hcA]; exact (hK iA).2)
  obtain ⟨αB, hαB0, hαB1, hαBsub⟩ :=
    exists_closedCube_of_isCompact_subset_image_openCube cB (hK iB).1 (by rw [hcB]; exact (hK iB).2)
  obtain ⟨αC, hαC0, hαC1, hαCsub⟩ :=
    exists_closedCube_of_isCompact_subset_image_openCube cC (hK iC).1 (by rw [hcC]; exact (hK iC).2)
  let α : ℝ := max (max αA αB) αC
  have hαAle : αA ≤ α := le_trans (le_max_left αA αB) (le_max_left _ _)
  have hαBle : αB ≤ α := le_trans (le_max_right αA αB) (le_max_left _ _)
  have hαCle : αC ≤ α := le_max_right _ _
  have hα0 : 0 < α := lt_of_lt_of_le hαA0 hαAle
  have hα1 : α < 1 := max_lt (max_lt hαA1 hαB1) hαC1
  let β₀ : ℝ := (α + 1) / 2
  have hαβ₀ : α < β₀ := by simp only [β₀]; linarith
  have hβ₀0 : 0 < β₀ := by simp only [β₀]; linarith
  have hβ₀1 : β₀ < 1 := by simp only [β₀]; linarith
  let β : ℝ := (β₀ + 1) / 2
  have hβ₀β : β₀ < β := by simp only [β]; linarith
  have hβ0 : 0 < β := by simp only [β]; linarith
  have hβ1 : β < 1 := by simp only [β]; linarith
  -- the Lebesgue number and the triangulation of the closed cube
  obtain ⟨δ, hδ0, hδmesh⟩ := exists_mesh_of_chart_cover cA cC hα0 hαβ₀ hβ₀β hβ1
  obtain ⟨P, hPfin, hPspace, hPmesh⟩ := A.triangulation β δ hβ0 hδ0
  -- the two skeletons
  have hLowsub : A.skeleton.Low P 2 ⊆ PL.closedCube (n := n) β := by
    rw [← hPspace]; exact A.skeleton.low_sub P 2
  have hHighsub : A.skeleton.High P 2 ⊆ PL.closedCube (n := n) β := by
    rw [← hPspace]; exact A.skeleton.high_sub P 2
  -- engulf the low skeleton into cell A
  have hLowcomp : IsCompact (A.skeleton.Low P 2) :=
    IsCompact.of_isClosed_subset (isCompact_closedCube n β) (A.skeleton.low_closed P 2) hLowsub
  obtain ⟨HA, hHAlow, hHAfix⟩ :=
    engulf_skel A hloc hconn hβ₀0 hβ₀β hβ1 (p := 2) (by omega)
      (A.skeleton.Low P 2) hLowcomp hLowsub (A.skeleton.low_dom P 2)
  let UA : Set M := HA '' (cA.toFun '' PL.openCube (n := n) 1)
  have hUAeq : UA = HA '' (W iA) := by
    show HA '' (cA.toFun '' PL.openCube (n := n) 1) = HA '' (W iA)
    rw [hcA]
  have hUAopen : IsOpen UA :=
    HA.isOpenMap _ (cubeChart_isOpen_image_openCube cA (by norm_num) le_rfl)
  have hUAlow : cC.toFun '' (A.skeleton.Low P 2) ⊆ UA := hHAlow
  have hUAclosed : cA.toFun '' PL.closedCube (n := n) β₀ ⊆ UA := by
    rintro y ⟨z, hz, rfl⟩
    have hz1 : z ∈ PL.openCube (n := n) 1 := fun i => lt_of_le_of_lt (hz i) hβ₀1
    exact ⟨cA.toFun z, ⟨z, hz1, rfl⟩, hHAfix (cA.toFun z) ⟨z, hz, rfl⟩⟩
  -- engulf the high skeleton into cell B
  have hHighcomp : IsCompact (A.skeleton.High P 2) :=
    IsCompact.of_isClosed_subset (isCompact_closedCube n β) (A.skeleton.high_closed P 2) hHighsub
  have hHighdom : PL.DomDim (A.skeleton.High P 2) ((n - 3 : ℕ) : ℤ) := by
    have h1 : (n - 2 - 1 : ℕ) = n - 3 := by rw [Nat.sub_sub]
    simpa [h1] using A.skeleton.high_dom P 2
  obtain ⟨HB, hHBhigh, hHBfix⟩ :=
    engulf_skel A hloc hconn hβ₀0 hβ₀β hβ1 (p := n - 3) (by omega)
      (A.skeleton.High P 2) hHighcomp hHighsub hHighdom
  let UB : Set M := HB '' (cB.toFun '' PL.openCube (n := n) 1)
  have hUBopen : IsOpen UB :=
    HB.isOpenMap _ (cubeChart_isOpen_image_openCube cB (by norm_num) le_rfl)
  have hUBhigh : cC.toFun '' (A.skeleton.High P 2) ⊆ UB := hHBhigh
  have hUBclosed : cB.toFun '' PL.closedCube (n := n) β₀ ⊆ UB := by
    rintro y ⟨z, hz, rfl⟩
    have hz1 : z ∈ PL.openCube (n := n) 1 := fun i => lt_of_le_of_lt (hz i) hβ₀1
    exact ⟨cB.toFun z, ⟨z, hz1, rfl⟩, hHBfix (cB.toFun z) ⟨z, hz, rfl⟩⟩
  -- the mesh condition (every small simplex meeting `cA '' closedCube α` maps into `UA`)
  have hmesh : ∀ s ∈ P.faces,
      (∃ x, x ∈ cC.toFun '' PL.simp s ∧ x ∈ cA.toFun '' PL.closedCube (n := n) α) →
      cC.toFun '' PL.simp s ⊆ UA := by
    intro s hs hmeet
    have hsP : PL.simp s ⊆ PL.closedCube (n := n) β := by
      intro w hw
      rw [← hPspace]
      exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨s, hs, hw⟩
    have hdiam : ∀ y ∈ PL.simp s, ∀ z ∈ PL.simp s, dist y z < δ :=
      fun y hy z hz => meshLT_dist_lt hPmesh hs hy hz
    obtain ⟨x, hxs, hxA⟩ := hmeet
    obtain ⟨z, hz, hzx⟩ := hxs
    have hmem : ∃ w ∈ PL.simp s, cC.toFun w ∈ cA.toFun '' PL.closedCube (n := n) α :=
      ⟨z, hz, by rw [hzx]; exact hxA⟩
    exact subset_trans (fun w hw => by
        obtain ⟨z', hz', hzw⟩ := hδmesh (PL.simp s) hsP hmem hdiam hw
        exact ⟨z', fun i => le_of_lt (hz' i), hzw⟩) hUAclosed
  -- the stretch
  have hLowN : A.skeleton.Low P 2 ⊆
      {z : PL.E n | z ∈ PL.openCube (n := n) 1 ∧ cC.toFun z ∈ UA} := by
    intro z hz
    exact ⟨fun i => lt_of_le_of_lt (hLowsub hz i) hβ1, hUAlow ⟨z, hz, rfl⟩⟩
  have hHighN : A.skeleton.High P 2 ⊆
      {z : PL.E n | z ∈ PL.openCube (n := n) 1 ∧ cC.toFun z ∈ UB} := by
    intro z hz
    exact ⟨fun i => lt_of_le_of_lt (hHighsub hz i) hβ1, hUBhigh ⟨z, hz, rfl⟩⟩
  have hKiAα : K iA ⊆ cA.toFun '' PL.closedCube (n := n) α := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hαAsub hy
    exact ⟨z, closedCube_mono hαAle hz, hzy⟩
  have hKiCα : K iC ⊆ cC.toFun '' PL.closedCube (n := n) α := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hαCsub hy
    exact ⟨z, closedCube_mono hαCle hz, hzy⟩
  obtain ⟨H, hHKA, hHKC⟩ :=
    stretch_step (by omega : 3 ≤ n) A hα0 hαβ₀ hβ₀β hβ1 P hPfin hPspace
      UA UB hUAopen hUBopen hUAclosed hmesh hLowN hHighN (K iA) (K iC) hKiAα hKiCα
  -- the core of cell B lies in `UB`
  have hKiB : K iB ⊆ UB := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hαBsub hy
    exact hUBclosed ⟨z, closedCube_mono (le_of_lt (lt_of_le_of_lt hαBle hαβ₀)) hz, hzy⟩
  -- assemble the (k+2)-cover {H '' UA, UB, W_3, ..., W_{k+2}}
  refine cellCover_of_two_more (W := fun j : Fin k => W (Fin.castLE (by omega : k ≤ k + 3) j))
    (fun j => hW _) (H '' UA) UB ?_ ?_ ?_
  · rw [hUAeq]
    exact isOpenCell_image_homeomorph H (isOpenCell_image_homeomorph HA (hW iA))
  · rw [show UB = HB '' (W iB) from by
      show HB '' (cB.toFun '' PL.openCube (n := n) 1) = HB '' (W iB)
      rw [hcB]]
    exact isOpenCell_image_homeomorph HB (hW iB)
  · -- the cover condition
    intro x
    have hxK : x ∈ ⋃ i, K i := by rw [hKcov]; exact mem_univ x
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxK
    by_cases hk : i.1 < k
    · right; right
      refine ⟨⟨i.1, hk⟩, ?_⟩
      have hidx : (Fin.castLE (by omega : k ≤ k + 3) (⟨i.1, hk⟩ : Fin k) : Fin (k + 3)) = i :=
        Fin.ext rfl
      rw [hidx]
      exact (hK i).2 hi
    · have hi3 : i.1 = k ∨ i.1 = k + 1 ∨ i.1 = k + 2 := by omega
      rcases hi3 with hh | hh | hh
      · left
        have hii : i = iA := Fin.ext (by simpa [iA] using hh)
        rw [hii] at hi
        exact hHKA hi
      · right; left
        have hii : i = iB := Fin.ext (by simp only [iB]; omega)
        rw [hii] at hi
        exact hKiB hi
      · rcases hHKC (by
          have hii : i = iC := Fin.ext (by simp only [iC]; omega)
          rwa [hii] at hi) with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')

end Work.Cells.Connell
