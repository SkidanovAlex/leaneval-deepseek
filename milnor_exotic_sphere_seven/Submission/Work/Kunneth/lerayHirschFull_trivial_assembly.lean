import Mathlib
import Submission.Work.Kunneth.zetaBridgeDefs
import Submission.Work.Kunneth.kunnethCoh_value
import Submission.Work.Kunneth.lerayHirschFull_point
import Submission.Work.Kunneth.zeta_qTriv
import Submission.Work.Kunneth.Assembly.kunnethCoh_value_full
import Submission.Work.Kunneth.Assembly.homeo
import Submission.Work.Kunneth.Assembly.pointFactsQb
import Submission.Work.Kunneth.Assembly.kunnethHypQb
import Submission.Work.Kunneth.Assembly.theta
import Submission.Work.Kunneth.Assembly.thetaOdd
import Submission.Work.Kunneth.Assembly.naturality
import Submission.Work.Kunneth.Assembly.bridgeFam

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false

namespace Work.Kunneth

open CategoryTheory CategoryTheory.Limits Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization MonoidalCategory TensorProduct

noncomputable section

theorem lerayHirschFull_trivial_assembly
    (hK : ∀ (X Y : SSet) (n : ℕ),
      (∀ q, Module.Projective ℤ ↥((Work.Kunneth.sChain Y).X q)) →
      (∀ q, Module.Free ℤ ↥((Work.Kunneth.sChain Y).homology q)) →
      (∀ q, Module.Finite ℤ ↥((Work.Kunneth.sChain Y).homology q)) →
      ∃ e : ((Work.Cohomology.cochainC ℤ (Work.Kunneth.sProd X Y)).homology n)
          ≅ Work.Kunneth.kunnethTarget X Y n,
        ∀ (p q : ℕ) (hpq : p + q = n)
          (a : ↥((Work.Cohomology.cochainC ℤ X).homology p))
          (b : ↥((Work.Cohomology.cochainC ℤ Y).homology q)),
          e.hom.hom (CategoryTheory.eqToHom (congrArg (fun k => (Work.Cohomology.cochainC ℤ
              (Work.Kunneth.sProd X Y)).homology k) hpq) (Work.Kunneth.crossH X Y p q a b))
            ⟨(p, q), hpq⟩ = a ⊗ₜ[ℤ] b)
    (hzc : ∀ (m : ℕ) (B : Type) [TopologicalSpace B],
      (Work.Thom.CohMap (Work.Kunneth.qTriv m B) ℤ 2).hom
          (Work.LerayHirsch.zeta (Work.LerayHirsch.trivCore m))
        = Work.LerayHirsch.zeta
            (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit))
    (m : ℕ) (B : Type) [TopologicalSpace B] [Nonempty B] :
    Work.LerayHirsch.LerayHirschFull
      (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit) := by
  classical
  rcases m with _ | n
  · -- the zero bundle: the projectivisation is empty and both sides are subsingletons
    haveI hEmp : IsEmpty (Work.LerayHirsch.ProjSpace (Work.Kunneth.Asm.Zb 0 B)) := by
      haveI h : IsEmpty ↥(Work.Thom.zeroComplement
          (Work.Thom.realification (Work.Kunneth.Asm.Zb 0 B))) :=
        ⟨fun p => by
          have h0 : (show EuclideanSpace ℂ (Fin 0) from p.1.2) = 0 := Subsingleton.elim _ _
          exact p.2 h0⟩
      exact ⟨fun x => Quotient.inductionOn x (fun p => isEmptyElim p)⟩
    refine ⟨fun k => ?_, fun k => ?_⟩
    · haveI : Subsingleton ((i : {i : Fin 0 // (i : ℕ) ≤ k}) →
          Coh ℤ (2 * (k - (i : ℕ))) B) := Work.Kunneth.subsingleton_pi_of_isEmpty
      haveI : Subsingleton (Coh ℤ (2 * k)
          (Work.LerayHirsch.ProjSpace (Work.Kunneth.Asm.Zb 0 B))) :=
        Work.LerayHirsch.subsingleton_cohomology_of_isEmpty (2 * k)
      exact Work.Kunneth.bijective_of_subsingleton _ (fun i => isEmptyElim i.1)
    · haveI : Subsingleton ((i : {i : Fin 0 // (i : ℕ) ≤ k}) →
          Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B) := Work.Kunneth.subsingleton_pi_of_isEmpty
      haveI : Subsingleton (Coh ℤ (2 * k + 1)
          (Work.LerayHirsch.ProjSpace (Work.Kunneth.Asm.Zb 0 B))) :=
        Work.LerayHirsch.subsingleton_cohomology_of_isEmpty (2 * k + 1)
      exact Work.Kunneth.bijective_of_subsingleton _ (fun i => isEmptyElim i.1)
  · -- the main case `m = n + 1`
    have hQ := Work.Kunneth.Asm.pointFactsQb (n + 1)
    have hHyp := Work.Kunneth.Asm.kunnethHypQb n
    obtain ⟨eH, heH⟩ := Work.Kunneth.Asm.nonempty_homeo_hMap (n + 1) B
    have heq : Work.Kunneth.Asm.hMap (n + 1) B
        = (↑eH : C(Work.Kunneth.Asm.Pb (n + 1) B, B × Work.Kunneth.Asm.Qb (n + 1))) :=
      ContinuousMap.ext (fun x => (congrFun heH x).symm)
    refine ⟨fun k => ?_, fun k => ?_⟩
    · have hCohMap : Function.Bijective
          (Work.Thom.CohMap (Work.Kunneth.Asm.hMap (n + 1) B) ℤ (2 * k)).hom := by
        rw [heq]
        exact Work.LerayHirsch.bijective_CohMap_of_homeomorph eH (2 * k)
      obtain ⟨E, hE⟩ := Work.Kunneth.Asm.kunnethCoh_value_full (Work.Kunneth.Asm.ssB B)
        (Work.Kunneth.Asm.ssB (Work.Kunneth.Asm.Qb (n + 1))) (2 * k)
        hHyp.1 hHyp.2.1 hHyp.2.2
      have htheta := Work.Kunneth.Asm.theta_bijective (n + 1) B k hQ.1 hQ.2
      have hEfam : ∀ xf, E.hom.hom (Work.Kunneth.Asm.sqFam (n + 1) B k xf)
          = Work.Kunneth.Asm.theta (n + 1) B k xf := by
        intro xf
        rw [Work.Kunneth.Asm.sqFam, Work.Kunneth.Asm.theta, map_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Work.Kunneth.Asm.sqTerm, Work.Kunneth.Asm.thetaTerm,
          ← Work.Kunneth.Asm.eqToHom_homology_eq_rec]
        have hks : Work.Kunneth.Asm.kSingle (Work.Kunneth.Asm.ssB B)
            (Work.Kunneth.Asm.ssB (Work.Kunneth.Asm.Qb (n + 1))) (2 * k)
            ⟨(2 * (k - (i : ℕ)), 2 * (i : ℕ)), by have := i.2; omega⟩
            (xf i ⊗ₜ[ℤ] Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) (i : ℕ))
            = Work.Kunneth.Asm.kSingle (Work.Kunneth.Asm.ssB B)
              (Work.Kunneth.Asm.ssB (Work.Kunneth.Asm.Qb (n + 1))) (2 * k)
              ⟨(2 * (k - (i : ℕ)), 2 * (i : ℕ)), by omega⟩
              (xf i ⊗ₜ[ℤ] Work.LerayHirsch.zetaPow
                (Work.LerayHirsch.trivCore (n + 1)) (i : ℕ)) := by
          congr 1
        rw [hks]
        exact hE (2 * (k - (i : ℕ))) (2 * (i : ℕ)) (by omega) (xf i)
          (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) (i : ℕ))
      have hEsymm : Function.Bijective E.symm.hom :=
        ⟨Work.Kunneth.injective_of_iso E.symm, Work.Kunneth.surjective_of_iso E.symm⟩
      have hpull := Work.Kunneth.Asm.pullIso_bijective (n + 1) B (2 * k)
      have hmain : ∀ xf, Work.LerayHirsch.lhMap (Work.Kunneth.Asm.Zb (n + 1) B) k xf
          = (Work.Thom.CohMap (Work.Kunneth.Asm.hMap (n + 1) B) ℤ (2 * k)).hom
              (Work.Kunneth.Asm.pullIso (n + 1) B (2 * k)
                (E.symm.hom (Work.Kunneth.Asm.theta (n + 1) B k xf))) := by
        intro xf
        rw [Work.Kunneth.Asm.lhMap_eq_CohMap_crFam]
        have hsymm : E.symm.hom (Work.Kunneth.Asm.theta (n + 1) B k xf)
            = Work.Kunneth.Asm.sqFam (n + 1) B k xf := by
          rw [← hEfam xf]
          exact CategoryTheory.Iso.hom_inv_id_apply E _
        rw [hsymm, Work.Kunneth.Asm.pullIso_sqFam]
      have hfun : Work.LerayHirsch.lhMap (Work.Kunneth.Asm.Zb (n + 1) B) k
          = ((Work.Thom.CohMap (Work.Kunneth.Asm.hMap (n + 1) B) ℤ (2 * k)).hom
              ∘ Work.Kunneth.Asm.pullIso (n + 1) B (2 * k) ∘ E.symm.hom)
            ∘ Work.Kunneth.Asm.theta (n + 1) B k := by
        funext xf
        exact (hmain xf).trans rfl
      rw [hfun]
      exact (hCohMap.comp (hpull.comp hEsymm)).comp htheta
    · have hCohMapOdd : Function.Bijective
          (Work.Thom.CohMap (Work.Kunneth.Asm.hMap (n + 1) B) ℤ (2 * k + 1)).hom := by
        rw [heq]
        exact Work.LerayHirsch.bijective_CohMap_of_homeomorph eH (2 * k + 1)
      obtain ⟨E, hE⟩ := Work.Kunneth.Asm.kunnethCoh_value_full (Work.Kunneth.Asm.ssB B)
        (Work.Kunneth.Asm.ssB (Work.Kunneth.Asm.Qb (n + 1))) (2 * k + 1)
        hHyp.1 hHyp.2.1 hHyp.2.2
      have htheta := Work.Kunneth.Asm.thetaOdd_bijective (n + 1) B k hQ.1 hQ.2
      have hEfam : ∀ xf, E.hom.hom (Work.Kunneth.Asm.sqFamOdd (n + 1) B k xf)
          = Work.Kunneth.Asm.thetaOdd (n + 1) B k xf := by
        intro xf
        rw [Work.Kunneth.Asm.sqFamOdd, Work.Kunneth.Asm.thetaOdd, map_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Work.Kunneth.Asm.sqTermOdd, Work.Kunneth.Asm.thetaTermOdd,
          ← Work.Kunneth.Asm.eqToHom_homology_eq_rec]
        have hks : Work.Kunneth.Asm.kSingle (Work.Kunneth.Asm.ssB B)
            (Work.Kunneth.Asm.ssB (Work.Kunneth.Asm.Qb (n + 1))) (2 * k + 1)
            ⟨(2 * k + 1 - 2 * (i : ℕ), 2 * (i : ℕ)), by have := i.2; omega⟩
            (xf i ⊗ₜ[ℤ] Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) (i : ℕ))
            = Work.Kunneth.Asm.kSingle (Work.Kunneth.Asm.ssB B)
              (Work.Kunneth.Asm.ssB (Work.Kunneth.Asm.Qb (n + 1))) (2 * k + 1)
              ⟨(2 * k + 1 - 2 * (i : ℕ), 2 * (i : ℕ)), by omega⟩
              (xf i ⊗ₜ[ℤ] Work.LerayHirsch.zetaPow
                (Work.LerayHirsch.trivCore (n + 1)) (i : ℕ)) := by
          congr 1
        rw [hks]
        exact hE (2 * k + 1 - 2 * (i : ℕ)) (2 * (i : ℕ)) (by omega) (xf i)
          (Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) (i : ℕ))
      have hEsymm : Function.Bijective E.symm.hom :=
        ⟨Work.Kunneth.injective_of_iso E.symm, Work.Kunneth.surjective_of_iso E.symm⟩
      have hpull := Work.Kunneth.Asm.pullIso_bijective (n + 1) B (2 * k + 1)
      have hmain : ∀ xf, Work.LerayHirsch.lhMapOdd (Work.Kunneth.Asm.Zb (n + 1) B) k xf
          = (Work.Thom.CohMap (Work.Kunneth.Asm.hMap (n + 1) B) ℤ (2 * k + 1)).hom
              (Work.Kunneth.Asm.pullIso (n + 1) B (2 * k + 1)
                (E.symm.hom (Work.Kunneth.Asm.thetaOdd (n + 1) B k xf))) := by
        intro xf
        rw [Work.Kunneth.Asm.lhMapOdd_eq_CohMap_crFamOdd]
        have hsymm : E.symm.hom (Work.Kunneth.Asm.thetaOdd (n + 1) B k xf)
            = Work.Kunneth.Asm.sqFamOdd (n + 1) B k xf := by
          rw [← hEfam xf]
          exact CategoryTheory.Iso.hom_inv_id_apply E _
        rw [hsymm, Work.Kunneth.Asm.pullIso_sqFamOdd]
      have hfun : Work.LerayHirsch.lhMapOdd (Work.Kunneth.Asm.Zb (n + 1) B) k
          = ((Work.Thom.CohMap (Work.Kunneth.Asm.hMap (n + 1) B) ℤ (2 * k + 1)).hom
              ∘ Work.Kunneth.Asm.pullIso (n + 1) B (2 * k + 1) ∘ E.symm.hom)
            ∘ Work.Kunneth.Asm.thetaOdd (n + 1) B k := by
        funext xf
        exact (hmain xf).trans rfl
      rw [hfun]
      exact (hCohMapOdd.comp (hpull.comp hEsymm)).comp htheta

end

end Work.Kunneth
