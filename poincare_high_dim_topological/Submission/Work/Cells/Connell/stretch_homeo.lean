import Mathlib
import Submission.Work.Cells.Connell.connell_aux
import Submission.Work.Cells.Connell.Defs
import Submission.Work.PL.Defs
import Submission.Work.Cells.Connell.cubeChart_isCompact_image_closedCube
import Submission.Work.Cells.Connell.cubeChart_homeoOn_apply

namespace Work.Cells.Connell

/--
**Connell's stretch homeomorphism** (blueprint `G7`, used by `connell_step`).

Given a chart `cC`, a triangulation `P` of the closed `β`-cube (`β < 1`), open neighbourhoods
`UA` of the low (`p`-)skeleton and `UB` of the high (dual) skeleton of `P` (pulled back to the
open unit cube by `cC`), and a compact-ish set `K` lying in the chart image of the smaller closed
cube `closedCube α` (`α < β`), there is a self-homeomorphism `H` of `M` with `K ⊆ H '' UA ∪ UB`.

The point is that the geometry happens on `ℝⁿ`: the dual-stretch homeomorphism `h` supplied by
`A.skeleton.dual_stretch` fixes everything outside `openCube β` and carries `closedCube α` into
`h '' N₁ ∪ N₂`, where `N₁`, `N₂` are the preimages in the open unit cube of `UA`, `UB`.  Pulling
`h` back along the chart (`chart_conj`) gives a homeomorphism of the chart's open cell supported
in the compact chart image of `closedCube β`, which `A.extHomeo` extends by the identity to all
of `M`. -/
theorem stretch_homeo {n : ℕ} {M : Type*} [MetricSpace M]
    (A : Assumptions n M)
    {cC : PL.CubeChart n M} {α β : ℝ} (hα0 : 0 < α) (hαβ : α < β) (hβ1 : β < 1)
    (P : PL.Cx n) (hPfin : P.faces.Finite) (hPspace : P.space = PL.closedCube (n := n) β)
    {p : ℕ} (hp : p < n)
    (UA UB : Set M) (hUAopen : IsOpen UA) (hUBopen : IsOpen UB)
    (hLow : A.skeleton.Low P p ⊆ {z : PL.E n | z ∈ PL.openCube (n := n) 1 ∧ cC.toFun z ∈ UA})
    (hHigh : A.skeleton.High P p ⊆ {z : PL.E n | z ∈ PL.openCube (n := n) 1 ∧ cC.toFun z ∈ UB})
    (K : Set M) (hK : K ⊆ cC.toFun '' PL.closedCube (n := n) α) :
    ∃ H : M ≃ₜ M, K ⊆ H '' UA ∪ UB := by
  have hβ0 : 0 < β := lt_trans hα0 hαβ
  -- The two open neighbourhoods of the skeleta, viewed in `ℝⁿ` through the chart.
  obtain ⟨h, hfix, _hfaces, hcover⟩ :=
    A.skeleton.dual_stretch p β α hp hα0 hαβ P hPfin hPspace
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
  obtain ⟨H, hHO, _hHout⟩ :=
    A.extHomeo M (cC.toFun '' PL.openCube (n := n) 1) hOopen g
      {x : ↥(cC.toFun '' PL.openCube (n := n) 1) |
        (x : M) ∈ cC.toFun '' PL.closedCube (n := n) β} hCcomp hCfix
  refine ⟨H, ?_⟩
  -- On the chart cell, `H` acts as `cC ∘ h ∘ cC⁻¹`.
  have key : ∀ w, w ∈ PL.openCube (n := n) 1 → H (cC.toFun w) = cC.toFun (h w) := by
    intro w hw1
    have h1 : cC.toFun w ∈ cC.toFun '' PL.openCube (n := n) 1 := ⟨w, hw1, rfl⟩
    calc H (cC.toFun w) = g ⟨cC.toFun w, h1⟩ := hHO ⟨cC.toFun w, h1⟩
      _ = cC.toFun (h w) := hgapp w hw1
  rintro k hk
  obtain ⟨z, hz, rfl⟩ := hK hk
  rcases hcover hz with ⟨w, hw, hwz⟩ | hzN2
  · -- `z = h w` for some `w` in the preimage of `UA`: then `cC z = H (cC w)`.
    exact Or.inl ⟨cC.toFun w, hw.2, by rw [key w hw.1, hwz]⟩
  · -- `z` lies in the preimage of `UB`.
    exact Or.inr hzN2.2

end Work.Cells.Connell
