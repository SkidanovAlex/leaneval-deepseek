import Mathlib
import Submission.Work.Cells.Connell.connell_aux
import Submission.Work.Cells.Connell.Defs
import Submission.Work.PL.Defs
import Submission.Work.Cells.Connell.cubeChart_isCompact_image_closedCube
import Submission.Work.Cells.Connell.cubeChart_homeoOn_apply
import Submission.Work.Cells.Connell.stretch_homeo

namespace Work.Cells.Connell

theorem stretch_step {n : ℕ} (hn : 3 ≤ n) {M : Type*} [MetricSpace M]
    (A : Assumptions n M)
    {cA cC : PL.CubeChart n M} {α β₀ β : ℝ}
    (hα0 : 0 < α) (hαβ₀ : α < β₀) (hβ₀β : β₀ < β) (hβ1 : β < 1)
    (P : PL.Cx n) (hPfin : P.faces.Finite) (hPspace : P.space = PL.closedCube (n := n) β)
    (UA UB : Set M) (hUAopen : IsOpen UA) (hUBopen : IsOpen UB)
    (hUAclosed : cA.toFun '' PL.closedCube (n := n) β₀ ⊆ UA)
    (hmesh : ∀ s ∈ P.faces,
        (∃ x, x ∈ cC.toFun '' PL.simp s ∧ x ∈ cA.toFun '' PL.closedCube (n := n) α) →
        cC.toFun '' PL.simp s ⊆ UA)
    (hLow : A.skeleton.Low P 2 ⊆ {z : PL.E n | z ∈ PL.openCube (n := n) 1 ∧ cC.toFun z ∈ UA})
    (hHigh : A.skeleton.High P 2 ⊆ {z : PL.E n | z ∈ PL.openCube (n := n) 1 ∧ cC.toFun z ∈ UB})
    (KA KC : Set M) (hKA : KA ⊆ cA.toFun '' PL.closedCube (n := n) α)
    (hKC : KC ⊆ cC.toFun '' PL.closedCube (n := n) α) :
    ∃ H : M ≃ₜ M, KA ⊆ H '' UA ∧ KC ⊆ H '' UA ∪ UB := by
  have hp : 2 < n := by omega
  have hβ0 : 0 < β := lt_trans hα0 (lt_trans hαβ₀ hβ₀β)
  have hαβ : α < β := lt_trans hαβ₀ hβ₀β
  -- The two open neighbourhoods of the skeleta, viewed in `ℝⁿ` through the chart.
  obtain ⟨h, hfix, hfaces, hcover⟩ :=
    A.skeleton.dual_stretch 2 β α hp hα0 hαβ P hPfin hPspace
      {z : PL.E n | z ∈ PL.openCube (n := n) 1 ∧ cC.toFun z ∈ UA}
      {z : PL.E n | z ∈ PL.openCube (n := n) 1 ∧ cC.toFun z ∈ UB}
      (isOpen_setOf_openCube_and_chart_mem cC hUAopen)
      (isOpen_setOf_openCube_and_chart_mem cC hUBopen)
      hLow hHigh
  -- Conjugate `h` by the chart to a self-homeomorphism `g` of the chart's open cell.
  obtain ⟨g, hgapp, hgfix⟩ := chart_conj cC (le_of_lt hβ0) hβ1 h hfix
  -- The chart's open cell, and the compact set outside which `g` is the identity.
  have hOopen : IsOpen (cC.toFun '' PL.openCube (n := n) 1) :=
    cubeChart_isOpen_image_openCube cC zero_lt_one le_rfl
  have hKs : cC.toFun '' PL.closedCube (n := n) β ⊆ cC.toFun '' PL.openCube (n := n) 1 := by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, fun i => lt_of_le_of_lt (hx i) hβ1, rfl⟩
  have hCcomp : IsCompact {x : ↥(cC.toFun '' PL.openCube (n := n) 1) |
      (x : M) ∈ cC.toFun '' PL.closedCube (n := n) β} :=
    isCompact_subtype_preimage_of_subset (cubeChart_isCompact_image_closedCube cC hβ1) hKs
  have hCfix : ∀ x : ↥(cC.toFun '' PL.openCube (n := n) 1),
      x ∉ {y : ↥(cC.toFun '' PL.openCube (n := n) 1) |
        (y : M) ∈ cC.toFun '' PL.closedCube (n := n) β} → g x = x :=
    fun x hx => hgfix x (by simpa using hx)
  -- Extend `g` by the identity to a self-homeomorphism of `M`.
  obtain ⟨H, hHO, hHout⟩ :=
    A.extHomeo M (cC.toFun '' PL.openCube (n := n) 1) hOopen g
      {x : ↥(cC.toFun '' PL.openCube (n := n) 1) |
        (x : M) ∈ cC.toFun '' PL.closedCube (n := n) β} hCcomp hCfix
  -- On the chart cell, `H` acts as `cC ∘ h ∘ cC⁻¹`.
  have key : ∀ w, w ∈ PL.openCube (n := n) 1 → H (cC.toFun w) = cC.toFun (h w) := by
    intro w hw1
    have h1 : cC.toFun w ∈ cC.toFun '' PL.openCube (n := n) 1 := ⟨w, hw1, rfl⟩
    calc H (cC.toFun w) = g ⟨cC.toFun w, h1⟩ := hHO ⟨cC.toFun w, h1⟩
      _ = cC.toFun (h w) := hgapp w hw1
  refine ⟨H, ?_, ?_⟩
  · -- `KA ⊆ H '' UA`
    intro k hk
    have hkUA : k ∈ UA :=
      hUAclosed (Set.image_mono (closedCube_mono (le_of_lt hαβ₀)) (hKA hk))
    by_cases hxcell : k ∈ cC.toFun '' PL.openCube (n := n) 1
    · obtain ⟨z, hz1, hzk⟩ := hxcell
      by_cases hzβ : z ∈ PL.openCube (n := n) β
      · -- `z` lies in a face of `P`; `hmesh` puts its `cC`-image into `UA`.
        have hzspace : z ∈ P.space := by
          rw [hPspace]
          exact openCube_subset_closedCube hzβ
        obtain ⟨s, hsP, hzs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hzspace
        have hzs' : z ∈ PL.simp s := hzs
        have hUAs : cC.toFun '' PL.simp s ⊆ UA :=
          hmesh s hsP ⟨k, ⟨z, hzs', hzk⟩, hKA hk⟩
        have hwss : h.symm z ∈ PL.simp s := by
          have hzimg : z ∈ h '' PL.simp s := by rw [hfaces s hsP]; exact hzs'
          obtain ⟨w, hw, hwz⟩ := hzimg
          rwa [← hwz, h.symm_apply_apply]
        have hw1 : h.symm z ∈ PL.openCube (n := n) 1 := by
          have hspace : h.symm z ∈ P.space :=
            (Geometry.SimplicialComplex.convexHull_subset_space hsP) hwss
          rw [hPspace] at hspace
          exact closedCube_subset_openCube_lt_one hβ1 hspace
        exact ⟨cC.toFun (h.symm z), hUAs ⟨h.symm z, hwss, rfl⟩,
          by rw [key (h.symm z) hw1, h.apply_symm_apply, hzk]⟩
      · -- `h` fixes `z`, so `H` fixes `k = cC z ∈ UA`.
        have hzfix : h z = z := hfix z hzβ
        exact ⟨k, hkUA, by rw [← hzk, key z hz1, hzfix]⟩
    · -- `k` lies outside the chart cell, where `H` is the identity.
      exact ⟨k, hkUA, hHout k hxcell⟩
  · -- `KC ⊆ H '' UA ∪ UB`
    rintro k hk
    obtain ⟨z, hz, rfl⟩ := hKC hk
    rcases hcover hz with ⟨w, hw, hwz⟩ | hzN2
    · exact Or.inl ⟨cC.toFun w, hw.2, by rw [key w hw.1, hwz]⟩
    · exact Or.inr hzN2.2

end Work.Cells.Connell
