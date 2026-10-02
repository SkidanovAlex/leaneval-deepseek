import Mathlib
import Submission.Work.ThomBordism.valuePmOneV2Defs
import Submission.Work.ThomBordism.localGenDefs
import Submission.Work.Cohomology.homologyTwoCover
import Submission.Work.Cohomology.localCohomology
import Submission.Work.Cohomology.Duality.euclidean_convex_local_cohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.ThomBordism

noncomputable section

open CategoryTheory

/-- **The relative singular homology of the punctured closed tube is degreewise free.**

`Work.ThomBordism.tubePtSet E C x` is the complement of the point `E.e x` in the closed tube
`C.U`, and `E.e x` lies in the *interior* of the tube (`TubeChart.mem_openTube`).  Hence the pair
`(C.U, C.U ∖ {E.e x})` is, by excision, the same as the local pair `(ℝ^{8+k}, ℝ^{8+k} ∖ {E.e x})`,
whose relative homology is free in every degree (`Work.Cohomology.Duality.free_relChains_compl`,
the local homology of `ℝ^{8+k}` at a point: `ℤ` in degree `8+k` and `0` otherwise).

The excision is applied twice, in the two-open-set form `Work.Cohomology.homologyTwoCover`:

* on `↥C.U`, with the open cover by the preimage of the open tube `C.openTube` and the punctured
  set: this shrinks the ambient space from the closed tube to the open subset
  `U' = (Subtype.val) ⁻¹' C.openTube`, and the induced pair `(U', U' ∖ {pt})` is identified with
  `(C.openTube, C.openTube ∖ {pt})` by the canonical homeomorphism of subtypes
  (`Work.Cohomology.relChains_homeomorph`);
* on `ℝ^{8+k}`, with the open cover by `C.openTube` and `{E.e x}ᶜ`, which identifies the
  Euclidean local pair `(ℝ^{8+k}, ℝ^{8+k} ∖ {E.e x})` with `(C.openTube, C.openTube ∖ {pt})`.

Freeness is then transported back along the composite isomorphism of relative homology groups.
-/
theorem tubePtSet_relChains_free {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    ∀ j, Module.Free ℤ ↥((Work.Cohomology.relChains (TopCat.of ↥C.U)
      (Work.ThomBordism.tubePtSet E C x)).homology j) := by
  intro j
  have hN : 1 ≤ 8 + k := by omega
  let U' : Set ↥C.U := {y : ↥C.U | (y : Work.Tubular.Euc (8 + k)) ∈ C.openTube}
  have hU'open : IsOpen U' := C.openTube_isOpen.preimage continuous_subtype_val
  have hVopen : IsOpen (Work.ThomBordism.tubePtSet E C x) := by
    rw [Work.ThomBordism.tubePtSet, Set.preimage_compl]
    exact (isClosed_singleton.preimage continuous_subtype_val).isOpen_compl
  have hcov : U' ∪ Work.ThomBordism.tubePtSet E C x = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      by_cases h : (y : Work.Tubular.Euc (8 + k)) = E.e x
      · left
        show (y : Work.Tubular.Euc (8 + k)) ∈ C.openTube
        rw [h]; exact C.mem_openTube x
      · right
        show (y : Work.Tubular.Euc (8 + k)) ≠ E.e x
        exact h
  obtain ⟨e1⟩ := Work.Cohomology.homologyTwoCover (TopCat.of ↥C.U) U'
    (Work.ThomBordism.tubePtSet E C x) hU'open hVopen hcov j
  let φ : ↥U' ≃ₜ ↥C.openTube :=
    { toFun := fun y => ⟨(y.1 : Work.Tubular.Euc (8 + k)), y.2⟩
      invFun := fun z => ⟨⟨(z.1 : Work.Tubular.Euc (8 + k)), C.openTube_subset_U z.2⟩, z.2⟩
      left_inv := fun y => by ext; rfl
      right_inv := fun z => by ext; rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk (fun y => y.2)
      continuous_invFun := (continuous_subtype_val.subtype_mk
        (fun z : ↥C.openTube => C.openTube_subset_U z.2)).subtype_mk (fun z => z.2) }
  have he : ∀ y : ↥U', y ∈ {y : ↥U' | (y : ↥C.U) ∈ Work.ThomBordism.tubePtSet E C x} ↔
      φ y ∈ {z : ↥C.openTube |
        (z : Work.Tubular.Euc (8 + k)) ∈ ({E.e x} : Set (Work.Tubular.Euc (8 + k)))ᶜ} := by
    intro y
    exact Iff.rfl
  obtain ⟨e2⟩ := Work.Cohomology.relChains_homeomorph ↥U' ↥C.openTube
    {y : ↥U' | (y : ↥C.U) ∈ Work.ThomBordism.tubePtSet E C x}
    {z : ↥C.openTube |
      (z : Work.Tubular.Euc (8 + k)) ∈ ({E.e x} : Set (Work.Tubular.Euc (8 + k)))ᶜ} φ he j
  have hcov3 : C.openTube ∪ ({E.e x} : Set (Work.Tubular.Euc (8 + k)))ᶜ = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      by_cases h : y = E.e x
      · left; rw [h]; exact C.mem_openTube x
      · right; exact h
  obtain ⟨e3⟩ := Work.Cohomology.homologyTwoCover (TopCat.of (Work.Tubular.Euc (8 + k)))
    C.openTube (({E.e x} : Set (Work.Tubular.Euc (8 + k)))ᶜ) C.openTube_isOpen
    isOpen_compl_singleton hcov3 j
  have hbase : Module.Free ℤ ↥((Work.Cohomology.relChains (TopCat.of (Work.Tubular.Euc (8 + k)))
      (({E.e x} : Set (Work.Tubular.Euc (8 + k)))ᶜ)).homology j) :=
    Work.Cohomology.Duality.free_relChains_compl (8 + k) hN {E.e x} isCompact_singleton
      (convex_singleton _) ⟨E.e x, rfl⟩ j
  exact Module.Free.of_equiv' hbase
    (Work.Cohomology.moduleIsoToLinearEquiv' (e1 ≪≫ e2 ≪≫ e3.symm)).symm

end

end Work.ThomBordism
