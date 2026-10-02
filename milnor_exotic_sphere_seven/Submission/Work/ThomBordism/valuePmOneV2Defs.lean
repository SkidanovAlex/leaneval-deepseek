import Mathlib
import Submission.Work.ThomBordism.ambientClassDefs
import Submission.Work.ThomBordism.chartModelClassDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Work.ThomBordism

noncomputable section

open CategoryTheory

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The translation `y ↦ y - E.e x` on the closed tube. -/
noncomputable def tubeTransMap (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt) : C(↥C.U, Work.Tubular.Euc (8 + k)) :=
  ⟨fun y : ↥C.U => (y : Work.Tubular.Euc (8 + k)) - E.e x,
    continuous_subtype_val.sub continuous_const⟩

/-- The complement of the point `E.e x` inside the closed tube. -/
def tubePtSet (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) : Set ↥C.U :=
  (Subtype.val : ↥C.U → Work.Tubular.Euc (8 + k)) ⁻¹' ({E.e x}ᶜ : Set (Work.Tubular.Euc (8 + k)))

theorem mem_tubePtSet (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) {y : ↥C.U} :
    y ∈ tubePtSet E C x ↔ (y : Work.Tubular.Euc (8 + k)) ≠ E.e x := Iff.rfl

theorem tubePtSet_subset (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    Work.ThomBordism.tubeInvPunct E C ⊆ tubePtSet E C x :=
  fun y hy => Work.ThomBordism.tubeInvPunct_sub E C x hy

/-- **The point `E.e x` is in the interior of the closed tube.** -/
theorem mem_interior_U (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    E.e x ∈ interior C.U :=
  interior_mono C.openTube_subset_U
    ((C.openTube_isOpen).interior_eq.symm ▸ C.mem_openTube x)

/-- The inclusion of the closed tube in the ambient space. -/
def tubeIncl (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) : C(↥C.U, Work.Tubular.Euc (8 + k)) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem tubeIncl_mem (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    ∀ y ∈ tubePtSet E C x, tubeIncl E C y ∈ ({E.e x}ᶜ : Set (Work.Tubular.Euc (8 + k))) :=
  fun y hy => hy

/-- The translation `z ↦ z - E.e x` on the ambient Euclidean space. -/
def eucTrans (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    C(Work.Tubular.Euc (8 + k), Work.Tubular.Euc (8 + k)) :=
  ⟨fun z => z - E.e x, continuous_id.sub continuous_const⟩

theorem eucTrans_mem (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    ∀ z ∈ ({E.e x}ᶜ : Set (Work.Tubular.Euc (8 + k))),
      eucTrans E x z ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) := by
  intro z hz
  simpa [eucTrans, Set.mem_compl_iff, Set.mem_singleton_iff] using sub_ne_zero.mpr hz

theorem tubeTransMap_eq_comp (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    tubeTransMap E C x = (eucTrans E x).comp (tubeIncl E C) := by
  apply ContinuousMap.ext
  intro y
  rfl

theorem tubeTransMap_mem (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    ∀ y ∈ tubePtSet E C x,
      tubeTransMap E C x y ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) :=
  fun y hy => eucTrans_mem E x _ (tubeIncl_mem E C x y hy)

/-- The same pair condition, read on the *punctured core* `tubeInvPunct`, with the exact form of
`Work.ThomBordism.ambientStandardClass`. -/
theorem tubeTransMap_mem_inv (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    ∀ y ∈ Work.ThomBordism.tubeInvPunct E C,
      tubeTransMap E C x y ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) :=
  fun y hy => Set.mem_compl_singleton_iff.mpr
    (sub_ne_zero.mpr (Work.ThomBordism.tubeInvPunct_sub E C x hy))

/-- The tube inverse as a map of the punctured parts. -/
noncomputable def tubeInvSub (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) :
    TopCat.of ↥(Work.ThomBordism.tubeInvPunct E C) ⟶
      TopCat.of (Work.Tubular.normalNonzero E) :=
  TopCat.ofHom
    ⟨fun y => ⟨Work.ThomBordism.tubeInvMap E C y.1,
        show Work.ThomBordism.tubeInvMap E C y.1 ∈ Work.Tubular.normalNonzero E from y.2⟩,
      Continuous.subtype_mk
        ((Work.ThomBordism.tubeInvMap E C).continuous.comp continuous_subtype_val)
        (fun y => (show Work.ThomBordism.tubeInvMap E C y.1 ∈ Work.Tubular.normalNonzero E
          from y.2))⟩

theorem tubeInv_compat (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) :
    Work.Cohomology.subtypeIncl (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C)
        ≫ (TopCat.ofHom (Work.ThomBordism.tubeInvMap E C))
      = tubeInvSub E C ≫ Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E) := by
  apply TopCat.ext
  intro a
  rfl

theorem tubeInvHomology_eq (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) :
    Work.ThomBordism.tubeInvHomology E C
      = (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMapOf (TopCat.of ↥C.U)
          (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.ThomBordism.tubeInvPunct E C) (Work.Tubular.normalNonzero E)
          (TopCat.ofHom (Work.ThomBordism.tubeInvMap E C)) (tubeInvSub E C)
          (tubeInv_compat E C)) (k + 8)).hom := rfl

end

end Work.ThomBordism
