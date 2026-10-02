import Mathlib
import Submission.Work.ThomBordism.genuineTubeData
import Submission.Work.ThomBordism.tubeConnForm
import Submission.Work.ThomBordism.tubeThomRepOfEmbeddingOdd
import Submission.Work.ThomBordism.tubeNumberStep
import Submission.Work.ThomBordism.tubeCastStep
import Submission.Work.ThomBordism.chainABridge
import Submission.Work.ThomBordism.absThomCompareUniversal
import Submission.Work.ThomBordism.gaussClassifyingNDPad
import Submission.Work.Tubular.Gauss
import Submission.Work.Tubular.Interface
import Submission.Work.Tubular.ThomRepOfLocalDegree
import Submission.Work.Tubular.LocalDegreeAll

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open CategoryTheory Limits
open scoped Topology

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom
open Work.Tubular

/-! ## The nu-side pairing, keeping the collapse

`Work.Tubular.tubeThomRep_of_nuPairing` produces a `TubeThomRep` from the two nu-side pairing
identities, but returns only `Nonempty`: the collapse of its witness is *definitionally* the
loop `GenLoop.congr D.t0 (finCongr (Nat.add_comm 8 k)) (alphaV C hR hbox D.t0 J hJ g hg)`.  The
structure `Work.ThomBordism.GenuineTubeData` pins that collapse (`isGeom`), so we re-run the same
calculation below (the `calc` blocks are verbatim from `tubeThomRep_of_nuPairing`) and keep the
witness *and* the identification. -/

theorem tubeThomRep_collapse_of_nuPairing {k : ℕ} {D : ThomTarget k}
    {V : Work.ThomBordism.Man8} {N : NormalBundlData V}
    (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : Work.Tubular.TubeChart E ε)
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (J : C(OnePoint (NormalTotal E), D.T)) (hJ : J OnePoint.infty = D.t₀)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hν1 : relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
        (compPull E (k + 8) (relCoh_of_abs E ((Nat.add_comm 8 k) ▸
          ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸ D.p1sqU)))))
        (collapseRelK8 C g hg hR hbox) = N.normalP1Sq)
    (hν2 : relKronH (TopCat.of (NormalTotal E)) (normalNonzero E) (k + 8)
        (compPull E (k + 8) (relCoh_of_abs E ((Nat.add_comm 8 k) ▸
          ((Work.Thom.CohMap J ℤ (8 + k)).hom ((Nat.add_comm 8 k).symm ▸ D.p2U)))))
        (collapseRelK8 C g hg hR hbox) = N.normalP2) :
    ∃ r : Work.Tubular.TubeThomRep k D V N,
      r.collapse = GenLoop.congr D.t₀ (finCongr (Nat.add_comm 8 k))
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

/-! ## The target -/

theorem nonempty_genuineTubeData {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 11 ≤ k) (hodd : Odd k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (N : Work.ThomBordism.PontryaginThom.NormalBundlData V) :
    Nonempty (Work.ThomBordism.GenuineTubeData V k
      (Work.ThomBordism.connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega))) N) := by
  classical
  haveI : Nonempty V.pt := inferInstance
  obtain ⟨ε, hε, ⟨C⟩⟩ := Work.Tubular.hasTubularNeighbourhood E
  haveI : CompactSpace (Work.Tubular.NormalDiscSub E ε) :=
    Work.Tubular.compactSpace_normalDiscSub E ε
  obtain ⟨q⟩ := Work.Tubular.nonempty_normalSphSub E hε (by omega : 8 < 8 + k)
  have hU : IsCompact C.U := C.isCompact_U
  obtain ⟨g, hg2, hg, -⟩ := Work.Tubular.collapseToOnePoint E C q hU
  obtain ⟨R, hR, hbox⟩ := C.exists_box
  obtain ⟨J, hJ, hpair1, hpair2⟩ :=
    nuPairingExistsOdd (V := V) hk hodd E N C q hU hR.le hbox g hg hg2
  obtain ⟨rep, hrep⟩ :=
    tubeThomRep_collapse_of_nuPairing
      (D := Work.ThomBordism.connTarget k (by omega) (Work.ThomBordism.PhiG k (by omega)))
      E C hR.le hbox J hJ g hg hpair1 hpair2
  exact ⟨{ emb := E
           ε := ε
           hε := hε
           chart := C
           q := q
           R := R
           hR := hR.le
           hbox := hbox
           J := J
           hJ := hJ
           g := g
           hg := hg
           rep := rep
           isGeom := hrep }⟩

end Work.ThomBordism
