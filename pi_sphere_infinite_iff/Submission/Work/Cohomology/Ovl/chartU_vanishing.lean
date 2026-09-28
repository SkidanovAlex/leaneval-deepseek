import Mathlib
import Submission.Work.Cohomology.Endgame.ovlUnionCollarDefs
import Submission.Work.Milnor.Model8
import Submission.Work.Cohomology.Duality.convex_compl_sphere

set_option synthInstance.maxHeartbeats 400000

/-!
# Vanishing of `H⁵(↥vkU, ovlWU)`

`Work.Cohomology.Endgame.ovlWU` is the trace on the first chart `U = range ιX ⊆ Vk(-2)` of the set
`W = (U ∩ V) ∪ collar(-2)`.  This file proves

  `H⁵(U, ovlWU; ℤ) = 0`,

the first-chart input of the relative Mayer–Vietoris computation of `H⁵(Vk(-2), W)`.

The argument:

* `U ≅ ℝ⁴ × ℍ` is contractible, so `H⁵(U) = 0` and `H⁴(U) = 0`; the long exact sequence of the
  pair `(U, ovlWU)` (`Work.Cohomology.pair_exact₁`) therefore identifies `H⁵(U, ovlWU)` with
  `H⁴(ovlWU)`, and it suffices to show `H⁴(ovlWU) = 0`.
* Under the chart homeomorphism `chartX : ℝ⁴ × ℍ ≅ ↥vkU`, the trace `ovlWU` is the complement of
  the closed disc `ovlDisc = {0} × B̄(1/2)` (`ovlWU_chartX_preimage_local` below).
* The continuous linear equivalence `vkModelIso : ℝ⁴ × ℍ ≅ ℝ⁸` carries `ovlDisc` onto a nonempty
  compact convex subset `K ⊆ ℝ⁸`, and the complement of such a set is homotopy equivalent to the
  unit sphere `S⁷` (`Work.Cohomology.Duality.convex_compl_homotopyEquiv_sphere`).
* `H⁴(S⁷) = 0` (`Work.Cohomology.sphereCohomologyZero`), and homotopy equivalences induce
  isomorphisms on singular cohomology (`Work.Cohomology.cohomologyIso_of_homotopyEquiv`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.Cohomology.Ovl

noncomputable section

/-! ## The chart description of the trace `ovlWU`

The three lemmas below are the pointwise description of the trace of `W` in the first chart; they
are self-contained (their proofs only use the gluing datum `vData (-2)` and the fibre norm). -/

/-- The chart `chartX` of the first chart of `Vk (-2)` sends a point `p : ℝ⁴ × ℍ` to `ιX p`, seen
as an element of the ambient space `Vk (-2)`. -/
lemma chartX_coe_local (p : Submission.Milnor.MSpace8) :
    ((Work.Cohomology.Endgame.chartX p : ↥(Work.Cohomology.Crux.vkU)) :
        Work.Cohomology.vkPairX) = (Submission.Milnor.vData (-2)).ιX p := rfl

/-- The image of the first chart meets the second chart exactly over the gluing region
`{x ≠ 0} ⊆ ℝ⁴ × ℍ`. -/
lemma ιX_mem_vkV_iff_local (p : Submission.Milnor.MSpace8) :
    (Submission.Milnor.vData (-2)).ιX p ∈ Work.Cohomology.Crux.vkV ↔ p.1 ≠ 0 := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := h
    exact ((Submission.Milnor.vData (-2)).ιY_eq_ιX_iff.mp hy).choose
  · intro h
    exact ⟨(Submission.Milnor.vData (-2)).φ p,
      ((Submission.Milnor.vData (-2)).ιX_eq_ιY_iff.mpr ⟨h, rfl⟩).symm⟩

/-- In the first chart of `Vk (-2)`, the collar `{1/2 < ν}` is the condition `1/2 < ‖p.2‖`. -/
lemma ιX_mem_collar_iff_local (p : Submission.Milnor.MSpace8) :
    (Submission.Milnor.vData (-2)).ιX p ∈ Work.Milnor.collar (-2) ↔ 1/2 < ‖p.2‖ := by
  rw [Work.Milnor.mem_collar, Work.Milnor.fibreNormFun_ιX]

/-- **The trace of `W` on the first chart is the complement of the closed disc
`ovlDisc = {0} × B̄(1/2)`.** -/
lemma ovlWU_chartX_preimage_local :
    Work.Cohomology.Endgame.chartX ⁻¹' Work.Cohomology.Endgame.ovlWU =
      (Work.Cohomology.Endgame.ovlDisc)ᶜ := by
  ext p
  rw [Set.mem_preimage, Set.mem_compl_iff]
  show ((Work.Cohomology.Endgame.chartX p : ↥(Work.Cohomology.Crux.vkU)) :
      Work.Cohomology.vkPairX) ∈ Work.Cohomology.Endgame.ovlW ↔
    ¬ (p.1 = 0 ∧ ‖p.2‖ ≤ 1/2)
  rw [Work.Cohomology.Endgame.ovlW, chartX_coe_local]
  simp only [Set.mem_union, Set.mem_inter_iff]
  rw [ιX_mem_vkV_iff_local, ιX_mem_collar_iff_local]
  simp only [Work.Cohomology.Crux.vkU, Set.mem_range_self, true_and]
  simp only [not_and_or, not_le]

/-! ## The disc `ovlDisc` in the model space -/

/-- The closed disc `ovlDisc = {0} × B̄(1/2)` is the product of the origin and a closed ball. -/
lemma ovlDisc_eq_prod :
    Work.Cohomology.Endgame.ovlDisc =
      ({0} : Set (EuclideanSpace ℝ (Fin 4))) ×ˢ
        Metric.closedBall (0 : Quaternion ℝ) (1/2) := by
  ext p
  simp only [Work.Cohomology.Endgame.ovlDisc, Set.mem_setOf_eq, Set.mem_prod,
    Set.mem_singleton_iff, Metric.mem_closedBall, dist_eq_norm, sub_zero]

/-- The disc `ovlDisc` is convex. -/
lemma convex_ovlDisc : Convex ℝ Work.Cohomology.Endgame.ovlDisc := by
  rw [ovlDisc_eq_prod]
  exact (convex_singleton (0 : EuclideanSpace ℝ (Fin 4))).prod
    (convex_closedBall (0 : Quaternion ℝ) (1/2))

/-- The disc `ovlDisc` is compact. -/
lemma isCompact_ovlDisc : IsCompact Work.Cohomology.Endgame.ovlDisc := by
  rw [ovlDisc_eq_prod]
  exact isCompact_singleton.prod (isCompact_closedBall (0 : Quaternion ℝ) (1/2))

/-- The image of the disc under the model identification `ℝ⁴ × ℍ ≅ ℝ⁸`. -/
def ovlDisc8 : Set (EuclideanSpace ℝ (Fin 8)) :=
  Work.Milnor.vkModelIso '' Work.Cohomology.Endgame.ovlDisc

/-- The image of the disc is convex. -/
lemma convex_ovlDisc8 : Convex ℝ ovlDisc8 :=
  convex_ovlDisc.linear_image (Work.Milnor.vkModelIso : Submission.Milnor.MSpace8 →ₗ[ℝ]
    EuclideanSpace ℝ (Fin 8))

/-- The image of the disc is compact. -/
lemma isCompact_ovlDisc8 : IsCompact ovlDisc8 :=
  isCompact_ovlDisc.image (Work.Milnor.vkModelIso.continuous)

/-- The image of the disc is nonempty. -/
lemma nonempty_ovlDisc8 : ovlDisc8.Nonempty :=
  ⟨Work.Milnor.vkModelIso (0, 0), (0, 0), ⟨rfl, by norm_num⟩, rfl⟩

/-! ## The vanishing of `H⁴(ovlWU)` -/

/-- The model identification `ℝ⁴ × ℍ ≅ ℝ⁸` carries the complement of `ovlDisc` homeomorphically onto
the complement of its image. -/
def homeomorph_ovlDisc_compl :
    ↥(Work.Cohomology.Endgame.ovlDisc)ᶜ ≃ₜ ↥(ovlDisc8)ᶜ :=
  Homeomorph.subtype Work.Milnor.vkModelIso.toHomeomorph (fun p => by
    constructor
    · intro hp hmem
      obtain ⟨q, hq, hqp⟩ := hmem
      exact hp (by rw [← (Work.Milnor.vkModelIso.injective hqp)]; exact hq)
    · intro hp hmem
      exact hp ⟨p, hmem, rfl⟩)

/-- **`H⁴` of the trace `ovlWU` vanishes.** -/
theorem isZero_ovlWU_cohomology_four :
    IsZero (Work.Cohomology.singularCohomology ℤ 4
      (TopCat.of ↥(Work.Cohomology.Endgame.ovlWU))) := by
  -- the trace of `W` on the first chart is the complement of the closed disc
  have hchart : ↥(Work.Cohomology.Endgame.ovlWU) ≃ₜ
      ↥(Work.Cohomology.Endgame.ovlDisc)ᶜ :=
    ((Homeomorph.subtype Work.Cohomology.Endgame.chartX (fun x => Iff.rfl)).symm).trans
      (Homeomorph.setCongr ovlWU_chartX_preimage_local)
  -- the complement of the compact convex disc is homotopy equivalent to `S⁷`
  obtain ⟨heS⟩ := Work.Cohomology.Duality.convex_compl_homotopyEquiv_sphere ovlDisc8
    isCompact_ovlDisc8 convex_ovlDisc8 nonempty_ovlDisc8
  obtain ⟨iso⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
    (hchart.toHomotopyEquiv.trans
      ((homeomorph_ovlDisc_compl.trans (Homeomorph.refl _)).toHomotopyEquiv.trans heS)) 4
  refine IsZero.of_iso ?_ iso
  exact Work.Cohomology.sphereCohomologyZero 7 4 (by norm_num) (by norm_num) (by norm_num)

/-! ## The target -/

theorem chartU_vanishing : Subsingleton (Work.Cohomology.relCohomology ℤ (TopCat.of ↥(Work.Cohomology.Crux.vkU)) Work.Cohomology.Endgame.ovlWU 5) := by
  haveI hcontr : ContractibleSpace ↥(Work.Cohomology.Crux.vkU) :=
    Work.Milnor.contractibleSpace_range_ιX (-2)
  -- `H⁵(U) = 0` since `U` is contractible
  have hU : IsZero (Work.Cohomology.singularCohomology ℤ 5
      (TopCat.of ↥(Work.Cohomology.Crux.vkU))) :=
    Work.Cohomology.contractible ℤ (TopCat.of ↥(Work.Cohomology.Crux.vkU)) 4
  -- `H⁴(ovlWU) = 0` by the previous theorem
  have hA : IsZero (Work.Cohomology.singularCohomology ℤ 4
      (TopCat.of ↥(Work.Cohomology.Endgame.ovlWU))) := isZero_ovlWU_cohomology_four
  -- the long exact sequence of the pair `(U, ovlWU)` in degree `4`
  have hz : IsZero (Work.Cohomology.relCohomology ℤ (TopCat.of ↥(Work.Cohomology.Crux.vkU))
      Work.Cohomology.Endgame.ovlWU 5) :=
    Work.Cohomology.isZero_of_exact_of_isZero_of_isZero
      (Work.Cohomology.pair_exact₁ ℤ (TopCat.of ↥(Work.Cohomology.Crux.vkU))
        Work.Cohomology.Endgame.ovlWU 4) hA hU
  exact ModuleCat.isZero_iff_subsingleton.mp hz

end

end Work.Cohomology.Ovl
