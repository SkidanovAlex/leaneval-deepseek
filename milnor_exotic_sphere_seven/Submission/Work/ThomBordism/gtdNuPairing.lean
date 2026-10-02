import Mathlib
import Submission.Work.ThomBordism._gtd.P5

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

noncomputable section

theorem gtdNuPairing {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 11 ≤ k) (hodd : Odd k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (N : Work.ThomBordism.PontryaginThom.NormalBundlData V)
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
    (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    (gauss : C(V.pt, Work.ThomBordism.Grassmann.OG k 10))
    (e : Work.Thom.BundleIso
      (Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle k 10) gauss)
      (Work.Tubular.normalBundle E ND))
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
    (hbp : ∀ p : (Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p) = gauss p.1)
    (J : C(OnePoint (Work.Tubular.normalBundle E ND).TotalSpace,
      OnePoint (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hJ : ∀ p, J (OnePoint.some p) = OnePoint.some (G p))
    (hJinf : J OnePoint.infty = OnePoint.infty)
    (hld : ∀ x : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)),
      Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (k + 8)
        ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup
          (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k x
          (Work.ThomBordism.gtdU E ND G hgm)))
        (Work.Tubular.collapseRelK8 C g hg hR hbox)
      = Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
          ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom x) V.c) :
    (Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (k + 8)
        (Work.Tubular.compPull E (k + 8) (Work.Tubular.relCoh_of_abs E ((Nat.add_comm 8 k) ▸
          ((Work.Thom.CohMap (J.comp ↑(Homeomorph.onePointCongr
              (Work.Tubular.eucNormalHomeomorph E ND)).symm) ℤ (8 + k)).hom
            ((Nat.add_comm 8 k).symm ▸
              (Work.ThomBordism.connTarget k (by omega)
                (Work.ThomBordism.PhiG k (by omega))).p1sqU)))))
        (Work.Tubular.collapseRelK8 C g hg hR hbox) = N.normalP1Sq) ∧
    (Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (k + 8)
        (Work.Tubular.compPull E (k + 8) (Work.Tubular.relCoh_of_abs E ((Nat.add_comm 8 k) ▸
          ((Work.Thom.CohMap (J.comp ↑(Homeomorph.onePointCongr
              (Work.Tubular.eucNormalHomeomorph E ND)).symm) ℤ (8 + k)).hom
            ((Nat.add_comm 8 k).symm ▸
              (Work.ThomBordism.connTarget k (by omega)
                (Work.ThomBordism.PhiG k (by omega))).p2U)))))
        (Work.Tubular.collapseRelK8 C g hg hR hbox) = N.normalP2) := by
  classical
  have hEucl : Work.Thom.IsEuclidean (Work.Tubular.normalBundle E ND) :=
    Work.Tubular.isEuclidean_normalBundle E ND
  let NZnu : NormLike (Work.Tubular.normalBundle E ND) :=
    Classical.choice (nonempty_normLike_of_isEuclidean (Work.Tubular.normalBundle E ND) hEucl)
  have hproj : ∀ p : (Work.Tubular.normalBundle E ND).TotalSpace,
      Work.Tubular.NormalTotal.proj ((Work.Tubular.eucNormalHomeomorph E ND) p) = p.1 :=
    fun p => rfl
  have hbproj : ∀ p : (Work.Tubular.normalBundle E ND).TotalSpace,
      Work.Thom.bundleProj (Grassmann.tautologicalBundle k 10) (G p)
        = gauss (Work.Thom.bundleProj (Work.Tubular.normalBundle E ND) p) := fun p => hbp p
  let y1 : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)) :=
    (Work.Thom.CohMap ((Work.Tubular.eucNormalHomeomorph E ND).symm :
        C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace)) ℤ 8).hom
      ((Work.Thom.CohMap (Work.Thom.bundleProj (Work.Tubular.normalBundle E ND)) ℤ 8).hom
        ((Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p1Sq k 10)))
  let y2 : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)) :=
    (Work.Thom.CohMap ((Work.Tubular.eucNormalHomeomorph E ND).symm :
        C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace)) ℤ 8).hom
      ((Work.Thom.CohMap (Work.Thom.bundleProj (Work.Tubular.normalBundle E ND)) ℤ 8).hom
        ((Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p2 k 10)))
  let Uen : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E) :=
    (Work.Thom.relCohMap ((Work.Tubular.eucNormalHomeomorph E ND).symm :
        C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace))
      (Work.Tubular.normalNonzero E)
      (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND)) (gtd_mem E ND) ℤ k).hom
      ((Work.Thom.relCohMap G (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
        (Work.Thom.zeroComplement (Grassmann.tautologicalBundle k 10)) hgm ℤ k).hom
        (Grassmann.tautologicalThomClass k 10).τ)
  have hUen : Uen = gtdU E ND G hgm := rfl
  have hnum1 : (Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom y1
      = (Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p1Sq k 10) := by
    show (Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom
      ((Work.Thom.CohMap ((Work.Tubular.eucNormalHomeomorph E ND).symm :
          C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace)) ℤ 8).hom
        ((Work.Thom.CohMap (Work.Thom.bundleProj (Work.Tubular.normalBundle E ND)) ℤ 8).hom
          ((Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p1Sq k 10)))) = _
    rw [Work.Thom.CohMap_comp_apply (Work.Tubular.zeroSectionNormal E)
      ((Work.Tubular.eucNormalHomeomorph E ND).symm :
        C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace)) ℤ 8
      ((Work.Thom.CohMap (Work.Thom.bundleProj (Work.Tubular.normalBundle E ND)) ℤ 8).hom
        ((Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p1Sq k 10)))]
    rw [Work.Thom.CohMap_comp_apply
      (((Work.Tubular.eucNormalHomeomorph E ND).symm :
        C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace)).comp
        (Work.Tubular.zeroSectionNormal E))
      (Work.Thom.bundleProj (Work.Tubular.normalBundle E ND)) ℤ 8
      ((Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p1Sq k 10))]
    have hz : (Work.Thom.bundleProj (Work.Tubular.normalBundle E ND)).comp
        (((Work.Tubular.eucNormalHomeomorph E ND).symm :
          C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace)).comp
          (Work.Tubular.zeroSectionNormal E)) = ContinuousMap.id V.pt := by
      ext x
      show ((Work.Tubular.eucNormalHomeomorph E ND).symm
        (Work.Tubular.zeroSectionNormal E x)).1 = x
      rw [← hproj ((Work.Tubular.eucNormalHomeomorph E ND).symm
          (Work.Tubular.zeroSectionNormal E x)),
        (Work.Tubular.eucNormalHomeomorph E ND).apply_symm_apply]
      rfl
    rw [hz, Work.Thom.CohMap_id, ModuleCat.hom_id]
    rfl
  have hnum2 : (Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom y2
      = (Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p2 k 10) := by
    show (Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom
      ((Work.Thom.CohMap ((Work.Tubular.eucNormalHomeomorph E ND).symm :
          C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace)) ℤ 8).hom
        ((Work.Thom.CohMap (Work.Thom.bundleProj (Work.Tubular.normalBundle E ND)) ℤ 8).hom
          ((Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p2 k 10)))) = _
    rw [Work.Thom.CohMap_comp_apply (Work.Tubular.zeroSectionNormal E)
      ((Work.Tubular.eucNormalHomeomorph E ND).symm :
        C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace)) ℤ 8
      ((Work.Thom.CohMap (Work.Thom.bundleProj (Work.Tubular.normalBundle E ND)) ℤ 8).hom
        ((Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p2 k 10)))]
    rw [Work.Thom.CohMap_comp_apply
      (((Work.Tubular.eucNormalHomeomorph E ND).symm :
        C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace)).comp
        (Work.Tubular.zeroSectionNormal E))
      (Work.Thom.bundleProj (Work.Tubular.normalBundle E ND)) ℤ 8
      ((Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p2 k 10))]
    have hz : (Work.Thom.bundleProj (Work.Tubular.normalBundle E ND)).comp
        (((Work.Tubular.eucNormalHomeomorph E ND).symm :
          C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace)).comp
          (Work.Tubular.zeroSectionNormal E)) = ContinuousMap.id V.pt := by
      ext x
      show ((Work.Tubular.eucNormalHomeomorph E ND).symm
        (Work.Tubular.zeroSectionNormal E x)).1 = x
      rw [← hproj ((Work.Tubular.eucNormalHomeomorph E ND).symm
          (Work.Tubular.zeroSectionNormal E x)),
        (Work.Tubular.eucNormalHomeomorph E ND).apply_symm_apply]
      rfl
    rw [hz, Work.Thom.CohMap_id, ModuleCat.hom_id]
    rfl
  have hclassdesc1 : (Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (k + 8)
        (Work.Tubular.compPull E (k + 8) (Work.Tubular.relCoh_of_abs E ((Nat.add_comm 8 k) ▸
          ((Work.Thom.CohMap (J.comp ↑(Homeomorph.onePointCongr
              (Work.Tubular.eucNormalHomeomorph E ND)).symm) ℤ (8 + k)).hom
            ((Nat.add_comm 8 k).symm ▸
              (Work.ThomBordism.connTarget k (by omega)
                (Work.ThomBordism.PhiG k (by omega))).p1sqU)))))
        (Work.Tubular.collapseRelK8 C g hg hR hbox))
      = (Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E) (k + 8)
          ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup
            (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k y1 Uen))
          (Work.Tubular.collapseRelK8 C g hg hR hbox)) := by
    have hA : (Nat.add_comm 8 k).symm ▸
        (Work.ThomBordism.connTarget k (by omega)
          (Work.ThomBordism.PhiG k (by omega))).p1sqU
        = uThomGen k (Grassmann.p1Sq k 10) := by
      rw [show (Work.ThomBordism.connTarget k (by omega)
            (Work.ThomBordism.PhiG k (by omega))).p1sqU
          = Work.ThomBordism.PhiG k (by omega)
              (Work.Thom.thomMap (Grassmann.tautologicalBundle k 10) k
                (Grassmann.tautologicalThomClass k 10).τ 8 (Grassmann.p1Sq k 10)) from rfl]
      exact PhiG_cast_symm k (by omega) _
    rw [hA]
    rw [nuClassDescriptionGen (E := E) (gauss := gauss)
      (Work.Tubular.normalBundle E ND) NZnu (Work.Tubular.eucNormalHomeomorph E ND)
      (gtd_mem E ND) G hbproj hgm J hJ hJinf (Grassmann.p1Sq k 10)]
    rw [Work.Thom.mixedCupC_pairNatural
      ((Work.Tubular.eucNormalHomeomorph E ND).symm :
        C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace))
      (Work.Tubular.normalNonzero E)
      (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND)) (gtd_mem E ND) 8 k
      ((Work.Thom.CohMap (Work.Thom.bundleProj (Work.Tubular.normalBundle E ND)) ℤ 8).hom
        ((Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p1Sq k 10)))
      ((Work.Thom.relCohMap G (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
        (Work.Thom.zeroComplement (Grassmann.tautologicalBundle k 10)) hgm ℤ k).hom
        (Grassmann.tautologicalThomClass k 10).τ)]
    rw [← Work.Tubular.mixedCup_topCatOf_eq_mixedCupC]
  have hclassdesc2 : (Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) (k + 8)
        (Work.Tubular.compPull E (k + 8) (Work.Tubular.relCoh_of_abs E ((Nat.add_comm 8 k) ▸
          ((Work.Thom.CohMap (J.comp ↑(Homeomorph.onePointCongr
              (Work.Tubular.eucNormalHomeomorph E ND)).symm) ℤ (8 + k)).hom
            ((Nat.add_comm 8 k).symm ▸
              (Work.ThomBordism.connTarget k (by omega)
                (Work.ThomBordism.PhiG k (by omega))).p2U)))))
        (Work.Tubular.collapseRelK8 C g hg hR hbox))
      = (Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E) (k + 8)
          ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup
            (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E) 8 k y2 Uen))
          (Work.Tubular.collapseRelK8 C g hg hR hbox)) := by
    have hA : (Nat.add_comm 8 k).symm ▸
        (Work.ThomBordism.connTarget k (by omega)
          (Work.ThomBordism.PhiG k (by omega))).p2U
        = uThomGen k (Grassmann.p2 k 10) := by
      rw [show (Work.ThomBordism.connTarget k (by omega)
            (Work.ThomBordism.PhiG k (by omega))).p2U
          = Work.ThomBordism.PhiG k (by omega)
              (Work.Thom.thomMap (Grassmann.tautologicalBundle k 10) k
                (Grassmann.tautologicalThomClass k 10).τ 8 (Grassmann.p2 k 10)) from rfl]
      exact PhiG_cast_symm k (by omega) _
    rw [hA]
    rw [nuClassDescriptionGen (E := E) (gauss := gauss)
      (Work.Tubular.normalBundle E ND) NZnu (Work.Tubular.eucNormalHomeomorph E ND)
      (gtd_mem E ND) G hbproj hgm J hJ hJinf (Grassmann.p2 k 10)]
    rw [Work.Thom.mixedCupC_pairNatural
      ((Work.Tubular.eucNormalHomeomorph E ND).symm :
        C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace))
      (Work.Tubular.normalNonzero E)
      (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND)) (gtd_mem E ND) 8 k
      ((Work.Thom.CohMap (Work.Thom.bundleProj (Work.Tubular.normalBundle E ND)) ℤ 8).hom
        ((Work.Thom.CohMap gauss ℤ 8).hom (Grassmann.p2 k 10)))
      ((Work.Thom.relCohMap G (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
        (Work.Thom.zeroComplement (Grassmann.tautologicalBundle k 10)) hgm ℤ k).hom
        (Grassmann.tautologicalThomClass k 10).τ)]
    rw [← Work.Tubular.mixedCup_topCatOf_eq_mixedCupC]
  constructor
  · rw [hclassdesc1, hUen, hld y1, hnum1]
    exact gauss_p1Sq_pairing E ND gauss e N
  · rw [hclassdesc2, hUen, hld y2, hnum2]
    exact gauss_p2_pairing E ND gauss e N

end

end Work.ThomBordism
