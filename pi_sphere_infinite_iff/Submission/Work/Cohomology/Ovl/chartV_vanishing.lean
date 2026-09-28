import Mathlib
import Submission.Work.Cohomology.Ovl.chartU_vanishing

/-!
# Vanishing of `H⁵(↥vkV, ovlWV)`

The second-chart mirror of `Work.Cohomology.Ovl.chartU_vanishing`: the trace `ovlWV` of
`W = (U ∩ V) ∪ collar(-2)` on the second chart of `Vk(-2)` satisfies `H⁵(vkV, ovlWV) = 0`.

Under the chart homeomorphism `chartY : ℝ⁴ × ℍ ≅ ↥vkV` the trace `ovlWV` is again the complement of
the closed disc `ovlDisc = {0} × B̄(1/2)`, which is homotopy equivalent to `S⁷`; `H⁴(S⁷) = 0`, and
the chart `vkV` is contractible, so the long exact sequence of the pair gives the result.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.Cohomology.Ovl

noncomputable section

/-- The chart `chartY` of the second chart of `Vk (-2)` sends `p` to `ιY p`. -/
lemma chartY_coe_local (p : Submission.Milnor.MSpace8) :
    ((Work.Cohomology.Endgame.chartY p : ↥(Work.Cohomology.Crux.vkV)) :
        Work.Cohomology.vkPairX) = (Submission.Milnor.vData (-2)).ιY p := rfl

/-- The image of the second chart meets the first chart exactly over the gluing region
`{x ≠ 0} ⊆ ℝ⁴ × ℍ`. -/
lemma ιY_mem_vkU_iff_local (p : Submission.Milnor.MSpace8) :
    (Submission.Milnor.vData (-2)).ιY p ∈ Work.Cohomology.Crux.vkU ↔ p.1 ≠ 0 := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := h
    obtain ⟨hx, hy⟩ := (Submission.Milnor.vData (-2)).ιX_eq_ιY_iff.mp hq
    rw [← hy]
    exact Submission.Milnor.invBase_ne_zero hx
  · intro h
    refine ⟨Submission.Milnor.vMapInv (-2) p, ?_⟩
    rw [(Submission.Milnor.vData (-2)).ιX_eq_ιY_iff]
    exact ⟨Submission.Milnor.invBase_ne_zero h, (Work.Milnor.vMap_inv (-2) h).2⟩

/-- In the second chart of `Vk (-2)`, the collar `{1/2 < ν}` is the condition `1/2 < ‖p.2‖`. -/
lemma ιY_mem_collar_iff_local (p : Submission.Milnor.MSpace8) :
    (Submission.Milnor.vData (-2)).ιY p ∈ Work.Milnor.collar (-2) ↔ 1/2 < ‖p.2‖ := by
  rw [Work.Milnor.mem_collar, Work.Milnor.fibreNormFun_ιY]

/-- **The trace of `W` on the second chart is the complement of the closed disc `ovlDisc`.** -/
lemma ovlWV_chartY_preimage_local :
    Work.Cohomology.Endgame.chartY ⁻¹' Work.Cohomology.Endgame.ovlWV =
      (Work.Cohomology.Endgame.ovlDisc)ᶜ := by
  ext p
  rw [Set.mem_preimage, Set.mem_compl_iff]
  show ((Work.Cohomology.Endgame.chartY p : ↥(Work.Cohomology.Crux.vkV)) :
      Work.Cohomology.vkPairX) ∈ Work.Cohomology.Endgame.ovlW ↔
    ¬ (p.1 = 0 ∧ ‖p.2‖ ≤ 1/2)
  rw [Work.Cohomology.Endgame.ovlW, chartY_coe_local]
  simp only [Set.mem_union, Set.mem_inter_iff]
  rw [ιY_mem_vkU_iff_local, ιY_mem_collar_iff_local]
  simp only [Work.Cohomology.Crux.vkV, Set.mem_range_self, true_and]
  simp only [not_and_or, not_le]
  tauto

/-- **`H⁴` of the trace `ovlWV` vanishes.** -/
theorem isZero_ovlWV_cohomology_four :
    IsZero (Work.Cohomology.singularCohomology ℤ 4
      (TopCat.of ↥(Work.Cohomology.Endgame.ovlWV))) := by
  have hchart : ↥(Work.Cohomology.Endgame.ovlWV) ≃ₜ
      ↥(Work.Cohomology.Endgame.ovlDisc)ᶜ :=
    ((Homeomorph.subtype Work.Cohomology.Endgame.chartY (fun x => Iff.rfl)).symm).trans
      (Homeomorph.setCongr ovlWV_chartY_preimage_local)
  obtain ⟨heS⟩ := Work.Cohomology.Duality.convex_compl_homotopyEquiv_sphere ovlDisc8
    isCompact_ovlDisc8 convex_ovlDisc8 nonempty_ovlDisc8
  obtain ⟨iso⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
    (hchart.toHomotopyEquiv.trans
      ((homeomorph_ovlDisc_compl.trans (Homeomorph.refl _)).toHomotopyEquiv.trans heS)) 4
  refine IsZero.of_iso ?_ iso
  exact Work.Cohomology.sphereCohomologyZero 7 4 (by norm_num) (by norm_num) (by norm_num)

/-- **`H⁵(vkV, ovlWV) = 0`.** -/
theorem chartV_vanishing :
    Subsingleton (Work.Cohomology.relCohomology ℤ (TopCat.of ↥(Work.Cohomology.Crux.vkV))
      Work.Cohomology.Endgame.ovlWV 5) := by
  haveI hcontr : ContractibleSpace ↥(Work.Cohomology.Crux.vkV) :=
    Work.Milnor.contractibleSpace_range_ιY (-2)
  have hV : IsZero (Work.Cohomology.singularCohomology ℤ 5
      (TopCat.of ↥(Work.Cohomology.Crux.vkV))) :=
    Work.Cohomology.contractible ℤ (TopCat.of ↥(Work.Cohomology.Crux.vkV)) 4
  have hA : IsZero (Work.Cohomology.singularCohomology ℤ 4
      (TopCat.of ↥(Work.Cohomology.Endgame.ovlWV))) := isZero_ovlWV_cohomology_four
  have hz : IsZero (Work.Cohomology.relCohomology ℤ (TopCat.of ↥(Work.Cohomology.Crux.vkV))
      Work.Cohomology.Endgame.ovlWV 5) :=
    Work.Cohomology.isZero_of_exact_of_isZero_of_isZero
      (Work.Cohomology.pair_exact₁ ℤ (TopCat.of ↥(Work.Cohomology.Crux.vkV))
        Work.Cohomology.Endgame.ovlWV 4) hA hV
  exact ModuleCat.isZero_iff_subsingleton.mp hz

end

end Work.Cohomology.Ovl
