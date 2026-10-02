import Mathlib
import Submission.Work.ThomBordism.tubeThomRepOfEmbeddingOdd

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open CategoryTheory Limits
open scoped Topology

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom
open Work.Tubular

/-- **The ν-side pairing, keeping the collapse.**

`Work.Tubular.tubeThomRep_of_nuPairing` produces a `TubeThomRep` from the two ν-side pairing
identities, but returns only `Nonempty`; here the same calculation is re-run and the witness is kept
*and* its collapse identified with `alphaV C hR hbox D.t₀ J hJ g hg`, which is what the consumer
needs. -/
theorem tubeThomRepOfNuPairing {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {V : Work.ThomBordism.Man8}
    {N : Work.ThomBordism.PontryaginThom.NormalBundlData V}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (J : C(OnePoint (Work.Tubular.NormalTotal E), D.T)) (hJ : J OnePoint.infty = D.t₀)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hν1 : Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (k + 8)
        (Work.Tubular.compPull E (k + 8) (Work.Tubular.relCoh_of_abs E ((Nat.add_comm 8 k) ▸
          ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸ D.p1sqU)))))
        (Work.Tubular.collapseRelK8 C g hg hR hbox) = N.normalP1Sq)
    (hν2 : Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (k + 8)
        (Work.Tubular.compPull E (k + 8) (Work.Tubular.relCoh_of_abs E ((Nat.add_comm 8 k) ▸
          ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸ D.p2U)))))
        (Work.Tubular.collapseRelK8 C g hg hR hbox) = N.normalP2) :
    ∃ rep : Work.Tubular.TubeThomRep k D V N,
      rep.collapse = GenLoop.congr D.t₀ (finCongr (Nat.add_comm 8 k))
        (Work.Tubular.alphaV C hR hbox D.t₀ J hJ g hg) := by
  classical
  set α := Work.Tubular.alphaV C hR hbox D.t₀ J hJ g hg with hα
  have hre : hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀
        (Quotient.mk _ (GenLoop.congr D.t₀ (finCongr (Nat.add_comm 8 k)) α))
      = (Nat.add_comm 8 k) ▸ hurewiczClassOf (8 + k) (by omega) D.t₀ (Quotient.mk _ α) :=
    (hurewiczClassOf_proof_irrel (one_le_add_eight k) (by omega) D.t₀ _).trans
      (hurewiczClassOf_add_comm D.t₀ α)
  have h1 : Work.Cohomology.kronH ℤ (ssetOf D.T) (k + 8) D.p1sqU
        (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀
          (Quotient.mk _ (GenLoop.congr D.t₀ (finCongr (Nat.add_comm 8 k)) α))) = N.normalP1Sq := by
    calc Work.Cohomology.kronH ℤ (ssetOf D.T) (k + 8) D.p1sqU
          (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀
            (Quotient.mk _ (GenLoop.congr D.t₀ (finCongr (Nat.add_comm 8 k)) α)))
        = Work.Cohomology.kronH ℤ (ssetOf D.T) (k + 8) D.p1sqU
            ((Nat.add_comm 8 k) ▸ hurewiczClassOf (8 + k) (by omega) D.t₀ (Quotient.mk _ α)) := by
          rw [hre]
      _ = Work.Cohomology.kronH ℤ (ssetOf D.T) (8 + k) ((Nat.add_comm 8 k).symm ▸ D.p1sqU)
            (hurewiczClassOf (8 + k) (by omega) D.t₀ (Quotient.mk _ α)) :=
          kronH_bridge1 (Nat.add_comm 8 k) D.p1sqU _
      _ = Work.Cohomology.kronH ℤ (ssetOf (OnePoint (NormalTotal E))) (8 + k)
            ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸ D.p1sqU))
            (hurewiczClassOf (8 + k) (by omega) OnePoint.infty
              (Quotient.mk _ (tubeGenLoopOnePoint C g hg hR hbox))) :=
          kronH_hurewiczChain_alphaV C hR hbox D.t₀ J hJ g hg
            ((Nat.add_comm 8 k).symm ▸ D.p1sqU)
      _ = Work.Cohomology.kronH ℤ (ssetOf (OnePoint (NormalTotal E))) (k + 8)
            ((Nat.add_comm 8 k) ▸ ((Work.Thom.CohMap J ℤ (8 + k)).hom
              ((Nat.add_comm 8 k).symm ▸ D.p1sqU)))
            ((Nat.add_comm 8 k) ▸ (hurewiczClassOf (8 + k) (by omega) OnePoint.infty
              (Quotient.mk _ (tubeGenLoopOnePoint C g hg hR hbox)))) :=
          kronH_bridge2 (Nat.add_comm 8 k)
            ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸ D.p1sqU)) _
      _ = relKronH (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E) (k + 8)
            (relCoh_of_abs E ((Nat.add_comm 8 k) ▸ ((Work.Thom.CohMap J ℤ (8 + k)).hom
              ((Nat.add_comm 8 k).symm ▸ D.p1sqU))))
            ((HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
              (Work.Cohomology.inclChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E))) (k + 8)).hom
              ((Nat.add_comm 8 k) ▸ (hurewiczClassOf (8 + k) (by omega) OnePoint.infty
                (Quotient.mk _ (tubeGenLoopOnePoint C g hg hR hbox))))) :=
          kronH_eq_relKronH_onePoint' E _ _
      _ = relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
            (compPull E (k + 8) (relCoh_of_abs E ((Nat.add_comm 8 k) ▸
              ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸ D.p1sqU)))))
            (collapseRelK8 C g hg hR hbox) :=
          relKronH_collapseRelK8 C g hg hR hbox _
      _ = N.normalP1Sq := hν1
  have h2 : Work.Cohomology.kronH ℤ (ssetOf D.T) (k + 8) D.p2U
        (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀
          (Quotient.mk _ (GenLoop.congr D.t₀ (finCongr (Nat.add_comm 8 k)) α))) = N.normalP2 := by
    calc Work.Cohomology.kronH ℤ (ssetOf D.T) (k + 8) D.p2U
          (hurewiczClassOf (k + 8) (one_le_add_eight k) D.t₀
            (Quotient.mk _ (GenLoop.congr D.t₀ (finCongr (Nat.add_comm 8 k)) α)))
        = Work.Cohomology.kronH ℤ (ssetOf D.T) (k + 8) D.p2U
            ((Nat.add_comm 8 k) ▸ hurewiczClassOf (8 + k) (by omega) D.t₀ (Quotient.mk _ α)) := by
          rw [hre]
      _ = Work.Cohomology.kronH ℤ (ssetOf D.T) (8 + k) ((Nat.add_comm 8 k).symm ▸ D.p2U)
            (hurewiczClassOf (8 + k) (by omega) D.t₀ (Quotient.mk _ α)) :=
          kronH_bridge1 (Nat.add_comm 8 k) D.p2U _
      _ = Work.Cohomology.kronH ℤ (ssetOf (OnePoint (NormalTotal E))) (8 + k)
            ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸ D.p2U))
            (hurewiczClassOf (8 + k) (by omega) OnePoint.infty
              (Quotient.mk _ (tubeGenLoopOnePoint C g hg hR hbox))) :=
          kronH_hurewiczChain_alphaV C hR hbox D.t₀ J hJ g hg
            ((Nat.add_comm 8 k).symm ▸ D.p2U)
      _ = Work.Cohomology.kronH ℤ (ssetOf (OnePoint (NormalTotal E))) (k + 8)
            ((Nat.add_comm 8 k) ▸ ((Work.Thom.CohMap J ℤ (8 + k)).hom
              ((Nat.add_comm 8 k).symm ▸ D.p2U)))
            ((Nat.add_comm 8 k) ▸ (hurewiczClassOf (8 + k) (by omega) OnePoint.infty
              (Quotient.mk _ (tubeGenLoopOnePoint C g hg hR hbox)))) :=
          kronH_bridge2 (Nat.add_comm 8 k)
            ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸ D.p2U)) _
      _ = relKronH (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E) (k + 8)
            (relCoh_of_abs E ((Nat.add_comm 8 k) ▸ ((Work.Thom.CohMap J ℤ (8 + k)).hom
              ((Nat.add_comm 8 k).symm ▸ D.p2U))))
            ((HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
              (Work.Cohomology.inclChains (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E))) (k + 8)).hom
              ((Nat.add_comm 8 k) ▸ (hurewiczClassOf (8 + k) (by omega) OnePoint.infty
                (Quotient.mk _ (tubeGenLoopOnePoint C g hg hR hbox))))) :=
          kronH_eq_relKronH_onePoint' E _ _
      _ = relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
            (compPull E (k + 8) (relCoh_of_abs E ((Nat.add_comm 8 k) ▸
              ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸ D.p2U)))))
            (collapseRelK8 C g hg hR hbox) :=
          relKronH_collapseRelK8 C g hg hR hbox _
      _ = N.normalP2 := hν2
  exact ⟨⟨GenLoop.congr D.t₀ (finCongr (Nat.add_comm 8 k)) α, h1, h2⟩, rfl⟩

end Work.ThomBordism
