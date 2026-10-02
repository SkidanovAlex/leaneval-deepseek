import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Orient.Closed
import Submission.Work.ThomBordism.sourceCoord

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# THOM: the two assembly steps of the boundary coordination

`Work.ThomBordism.SourceBoundaryCoord D0` is the vanishing
`i_* ῆ = 0` of the class `ῆ = sourceBoundaryClass D0` of the pieces under the inclusion of the
boundary part of the level set.  This file records the two reductions that turn it into a
*local* statement about the level set:

* `Work.ThomBordism.sourceBoundaryCoord_of_hPairδ` — the long-exact-sequence step: if `ῆ` is the
  boundary `hPairδ w` of a relative class `w` of the pair `(level set, boundary part)`, then the
  coordination holds (`i_* ∘ hPairδ = 0`).
* `Work.ThomBordism.eq_zero_of_locClass_eq_zero_of_component` — the localisation step: a class of
  `H_n` of a compact charted `n`-manifold vanishes as soon as the set where its local class vanishes
  meets **every connected component** (no connectedness hypothesis on the manifold is needed, which is
  what the source construction requires: the pieces of a `Work.ThomBordism.Man8` need not be
  connected).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

namespace Work.ThomBordism

open Work.PTGeometric

noncomputable section

variable {k mU m : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}

/-- **The long-exact-sequence step of the boundary coordination.**

If the class `ῆ` of the pieces is the image under the connecting map `hPairδ` of a relative class of
the pair `(level set, boundary part)`, then it dies under the inclusion of the boundary part — since
`hPairδ` followed by that inclusion is zero (`Work.Cohomology.hPairδ_comp`). -/
theorem sourceBoundaryCoord_of_hPairδ
    (D0 : RawAmbientData (k + mU) k (Fin m × ι) (fun a => Fam a.2))
    (w : (Work.Cohomology.relChains (TopCat.of ↥(sourceLevelSet D0))
      (sourceLevelBdry D0)).homology 9)
    (h : (Work.Cohomology.hPairδ (TopCat.of ↥(sourceLevelSet D0)) (sourceLevelBdry D0)
        8).hom w = sourceBoundaryClass D0) :
    SourceBoundaryCoord D0 := by
  show (HomologicalComplex.homologyMap (Work.Cohomology.inclChains
      (TopCat.of ↥(sourceLevelSet D0)) (sourceLevelBdry D0)) 8).hom (sourceBoundaryClass D0) = 0
  have h0 : (HomologicalComplex.homologyMap (Work.Cohomology.inclChains
      (TopCat.of ↥(sourceLevelSet D0)) (sourceLevelBdry D0)) 8).hom
        ((Work.Cohomology.hPairδ (TopCat.of ↥(sourceLevelSet D0))
          (sourceLevelBdry D0) 8).hom w) = 0 := by
    have hc := Work.Cohomology.hPairδ_comp (TopCat.of ↥(sourceLevelSet D0))
      (sourceLevelBdry D0) 8
    rw [← ModuleCat.comp_apply, hc]
    simp
  rw [← h]
  exact h0

/-- **The localisation step of the boundary coordination.**

A class of `H_n` of a compact charted `n`-manifold is zero as soon as, in **every connected
component**, there is a point at which its local class vanishes.  (The set where the local class
vanishes is clopen by `Work.Orient.relClass_eq_zero_iff_locClass_eq_zero`, hence a union of connected
components, and it meets each of them.)

This is the form in which the source construction consumes the per-piece comparison of the boundary
sign (`Work.ThomBordism.sign_of_piecewise_locClass`): the pieces are `Work.ThomBordism.Man8`s, whose
underlying spaces are *not* assumed connected, so a single point per *piece* does not suffice — one
point per connected component of the boundary does. -/
theorem eq_zero_of_locClass_eq_zero_of_component
    {n : ℕ} (hn : 1 ≤ n) (M : TopCat) [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (c : (Work.Cohomology.singularChains ℤ M).homology n)
    (h : ∀ y : M, ∃ z ∈ connectedComponent y, Work.Orient.locClass M n c z = 0) : c = 0 := by
  have hclopen : IsClopen {y : M | Work.Orient.locClass M n c y = 0} := by
    constructor
    · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro y hy
      obtain ⟨K, hK, hyK, hKn⟩ := Work.Orient.exists_isCoordBall_mem_nhds n M y
      filter_upwards [hKn] with z hz
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
      intro hz0
      exact hy ((Work.Orient.relClass_eq_zero_iff_locClass_eq_zero hn hK hyK).mp
        ((Work.Orient.relClass_eq_zero_iff_locClass_eq_zero hn hK hz).mpr hz0))
    · rw [isOpen_iff_mem_nhds]
      intro y hy
      obtain ⟨K, hK, hyK, hKn⟩ := Work.Orient.exists_isCoordBall_mem_nhds n M y
      filter_upwards [hKn] with z hz
      exact (Work.Orient.relClass_eq_zero_iff_locClass_eq_zero hn hK hz).mp
        ((Work.Orient.relClass_eq_zero_iff_locClass_eq_zero hn hK hyK).mpr hy)
  refine Work.Orient.eq_zero_of_locClass_eq_zero n hn M c (fun y => ?_)
  obtain ⟨z, hz, hz0⟩ := h y
  have hsub : connectedComponent z ⊆ {y : M | Work.Orient.locClass M n c y = 0} :=
    hclopen.connectedComponent_subset hz0
  have hsub' : connectedComponent y ⊆ {y : M | Work.Orient.locClass M n c y = 0} := by
    rw [connectedComponent_eq hz]
    exact hsub
  exact hsub' mem_connectedComponent

end

end Work.ThomBordism
