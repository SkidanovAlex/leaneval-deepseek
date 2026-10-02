import Submission.Work.ThomBordism.value_eq_chartModelClass
import Submission.Work.ThomBordism.KeyLocal.tubeSets

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory

namespace Work.ThomBordism.KeyLocal

noncomputable section

open Work.Tubular

/-- **The relative Kronecker pairing of an arbitrary tube-pulled-back class.**

For any degree-`(8+k)` class `X` of the Thom pair `(ν, ν∖0)` and any lift `δ` of the collapse class to
the tube, the pairing of the pullback of `X` along the tube inverse with `δ` equals the pairing of
`X` with the collapse class.  This is the general form of the PROVED
`Work.ThomBordism.value_eq_chartModelClass` (which is the case `X = chartModelClass`), and it is the
"back to ν" step of the last-mile assembly: it converts the tube-level comparison into a pairing
statement with `collapseRelK8`, which `collapseRelK8_pairing_injective` then upgrades to a class
equality.

Proof: the naturality of the relative Kronecker pairing `Work.Tubular.relKronH_natural` under the map
of pairs `(C.U, tubeInvPunct) → (ν, ν∖0)` induced by `C.inv`, plus the definition of
`tubeInvHomology` and the degree bookkeeping `8 + k ↔ k + 8`. -/
theorem tubePairingConvert {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : TubeChart E ε)
    (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
    (δ : (Work.Cohomology.relChains (TopCat.of ↥C.U)
        (Work.ThomBordism.tubeInvPunct E C)).homology (k + 8))
    (hδ : Work.ThomBordism.tubeInvHomology E C δ
      = Work.Tubular.collapseRelK8 C g hg hR hbox)
    (X : Work.Thom.RelCoh ℤ (8 + k) (TopCat.of (NormalTotal E)) (normalNonzero E)) :
    Work.Tubular.relKronH (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C) (k + 8)
        ((Nat.add_comm 8 k) ▸ (Work.Thom.relCohMap (Work.ThomBordism.tubeInvMap E C)
          (Work.ThomBordism.tubeInvPunct E C) (normalNonzero E) (fun y hy => hy) ℤ (8 + k)).hom X) δ
      = Work.Tubular.relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
          ((Nat.add_comm 8 k) ▸ X) (Work.Tubular.collapseRelK8 C g hg hR hbox) := by
  -- the induced map on the punctured parts, copied from the definition of `tubeInvHomology`
  let G : TopCat.of (Work.ThomBordism.tubeInvPunct E C) ⟶
      TopCat.of (normalNonzero E) :=
    TopCat.ofHom ⟨fun y : ↥(Work.ThomBordism.tubeInvPunct E C) =>
        ⟨C.inv y.1.1, y.2⟩,
      Continuous.subtype_mk
        (((Work.ThomBordism.tubeInvMap E C).continuous).comp continuous_subtype_val)
        (fun y => (show C.inv (↑(y : ↥C.U) : Euc (8 + k)) ∈
          normalNonzero E from y.2))⟩
  let W : CategoryTheory.CategoryStruct.comp
        (Work.Cohomology.subtypeIncl (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C))
        (TopCat.ofHom (Work.ThomBordism.tubeInvMap E C))
      = CategoryTheory.CategoryStruct.comp G
        (Work.Cohomology.subtypeIncl (TopCat.of (NormalTotal E))
          (normalNonzero E)) := by
    apply TopCat.ext; intro a; rfl
  let φh : Work.Cohomology.relChains (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C) ⟶
      Work.Cohomology.relChains (TopCat.of (NormalTotal E)) (normalNonzero E) :=
    Work.Cohomology.relChainsMapOf (TopCat.of ↥C.U) (TopCat.of (NormalTotal E))
      (Work.ThomBordism.tubeInvPunct E C) (normalNonzero E)
      (TopCat.ofHom (Work.ThomBordism.tubeInvMap E C)) G W
  have hkey : (HomologicalComplex.homologyMap φh (k + 8)).hom δ
      = Work.Tubular.collapseRelK8 C g hg hR hbox := by
    rw [show (HomologicalComplex.homologyMap φh (k + 8)).hom δ
        = Work.ThomBordism.tubeInvHomology E C δ from rfl]
    exact hδ
  have hnat := Work.Tubular.relKronH_natural
    (X := TopCat.of ↥C.U) (Y := TopCat.of (NormalTotal E))
    (A := Work.ThomBordism.tubeInvPunct E C) (B := normalNonzero E)
    (TopCat.ofHom (Work.ThomBordism.tubeInvMap E C)) G (fun y hy => hy) W
    (8 + k) X
    (Work.ThomBordism.chainsHomologyCast (K := Work.Cohomology.relChains (TopCat.of ↥C.U)
      (Work.ThomBordism.tubeInvPunct E C)) (Nat.add_comm 8 k).symm δ)
  rw [Work.ThomBordism.relKronH_cast_snd (Nat.add_comm 8 k)
    ((Work.Thom.relCohMap (Work.ThomBordism.tubeInvMap E C)
      (Work.ThomBordism.tubeInvPunct E C) (normalNonzero E) (fun y hy => hy) ℤ (8 + k)).hom X) δ]
  rw [hnat]
  rw [Work.ThomBordism.homologyMap_chainsCast φh (Nat.add_comm 8 k).symm δ]
  rw [hkey]
  rw [← Work.ThomBordism.relKronH_cast_snd (Nat.add_comm 8 k) X
    (Work.Tubular.collapseRelK8 C g hg hR hbox)]

end

end Work.ThomBordism.KeyLocal
