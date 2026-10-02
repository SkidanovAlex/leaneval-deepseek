import Mathlib
import Submission.Work.Thom.realThomClassOf_natural
import Submission.Work.ThomBordism.tautologicalClassSensitivity
import Submission.Work.ThomBordism.TubeLocalDegree
import Submission.Work.ThomBordism.gtdU_span_top

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory Limits
open scoped Topology

namespace Work.ThomBordism

noncomputable section

open Work.TangentClasses

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-!
# The Gauss/classifying pullback of an *arbitrary* Thom class of the tautological bundle
  generates the Thom pair of the normal bundle

`Submission/Work/ThomBordism/gtdU_span_top.lean` proves the spanning statement for the fixed
`Classical.choice`-witness `Grassmann.tautologicalThomClass k 10`.  Nothing in that argument uses
the particular choice: the only input about the class is `thomClass_fibreGenerator`, which holds for
every Thom class of the bundle at the rank degree.  This module re-runs the same proof for a
*variable* Thom class `U` of the tautological bundle (`gtdUWith` is `gtdU` with the tautological
class replaced by `U`), which is what the canonical, orientation-compatible
`Work.Thom.realThomClassOf` needs.

The spanning statement is *sign-insensitive* (`Submodule.span ℤ {c • x} = Submodule.span ℤ {x}` for
a unit `c`), so it holds for the canonical Thom class although its sign — unlike that of the opaque
`tautologicalThomClass` — is pinned by construction.
-/

/-- **The pullback of an arbitrary Thom class of the tautological bundle along the
Gauss/classifying map `G` generates `H^k(ν, ν∖0)`.** -/
theorem gtdUWith_span_top_aux {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (U : Work.Thom.ThomClass (Work.ThomBordism.Grassmann.tautologicalBundle k 10) k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
      = Work.ThomBordism.Grassmann.padGaussFun E ND p.proj)
    (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) :
    Submodule.span ℤ ({((Work.Thom.relCohMap G
        (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
        (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) hgm ℤ k).hom
      U.τ)} : Set _) = ⊤ := by
  classical
  haveI : PathConnectedSpace V.pt := Work.Tubular.pathConnectedSpace_of_man8 V
  set σ : Work.Thom.OpenThom (Work.Tubular.normalBundle E ND) k :=
    (Work.Thom.relCohMap G (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
      (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) hgm ℤ k).hom
      U.τ with hσ
  have hgen : IsFibreGenerator (Work.Tubular.normalBundle E ND) k σ := by
    intro x
    let efib : ↥(Work.ThomBordism.fibre (Work.Tubular.normalBundle E ND) x) ≃ₜ
        ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
          (Work.ThomBordism.Grassmann.padGaussFun E ND x)) :=
      (fibreModelHomeomorph (Work.Tubular.normalBundle E ND) x).trans
        ((gtdThetaHomeomorph E ND x).trans
          (fibreModelHomeomorph (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
            (Work.ThomBordism.Grassmann.padGaussFun E ND x)).symm)
    have hval : ∀ p : ↥(Work.ThomBordism.fibre (Work.Tubular.normalBundle E ND) x),
        (show Work.ThomBordism.Grassmann.Amb k from
            ((efib p : ↥(Work.ThomBordism.fibre
              (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
              (Work.ThomBordism.Grassmann.padGaussFun E ND x))) :
              (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace).snd)
          = gtdThetaCLM E ND x (show Work.Tubular.Euc k from
              (p : (Work.Tubular.normalBundle E ND).TotalSpace).snd) := by
      intro p
      rfl
    have he : ∀ p, ((efib p : ↥(Work.ThomBordism.fibre
          (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
          (Work.ThomBordism.Grassmann.padGaussFun E ND x))) :
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace)
        = G (p : (Work.Tubular.normalBundle E ND).TotalSpace) := by
      intro p
      refine totalSpace_eq_of ?_ ?_
      · exact (((hbp (p : (Work.Tubular.normalBundle E ND).TotalSpace)).trans
          (congrArg (Work.ThomBordism.Grassmann.padGaussFun E ND) (p.2))).symm)
      · exact ((hval p).trans
          (gtdG_snd hbp hvec x (p : (Work.Tubular.normalBundle E ND).TotalSpace) p.2).symm)
    have hpe : ∀ p, p ∈ Work.ThomBordism.fibrePunctSub (Work.Tubular.normalBundle E ND) x ↔
        efib p ∈ Work.ThomBordism.fibrePunctSub
          (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
          (Work.ThomBordism.Grassmann.padGaussFun E ND x) := by
      intro p
      rw [mem_fibrePunctSub, mem_fibrePunctSub, hval p]
      constructor
      · intro h
        intro h0
        exact h ((gtdThetaCLM_bijective E ND x).1 (by rw [h0, map_zero]))
      · intro h h0
        exact h (by rw [h0, map_zero])
    -- the restriction of the pullback to the fibre
    have hres : Work.ThomBordism.fibreRes (Work.Tubular.normalBundle E ND) x k σ
        = (Work.Thom.relCohMap (efib : C(↥(Work.ThomBordism.fibre
              (Work.Tubular.normalBundle E ND) x),
            ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
              (Work.ThomBordism.Grassmann.padGaussFun E ND x))))
            (Work.ThomBordism.fibrePunctSub (Work.Tubular.normalBundle E ND) x)
            (Work.ThomBordism.fibrePunctSub (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
              (Work.ThomBordism.Grassmann.padGaussFun E ND x))
            (fun p hp => (hpe p).mp hp) ℤ k).hom
          (Work.ThomBordism.fibreRes (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
            (Work.ThomBordism.Grassmann.padGaussFun E ND x) k
            U.τ) := by
      rw [hσ]
      set A := Work.ThomBordism.fibrePunctSub (Work.Tubular.normalBundle E ND) x with hA
      set Bs := Work.ThomBordism.fibrePunctSub
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
        (Work.ThomBordism.Grassmann.padGaussFun E ND x) with hBs
      set zν := Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND) with hzν
      set zγ := Work.Thom.zeroComplement
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10) with hzγ
      show (Work.Thom.relCohMap (Work.ThomBordism.fibreIncl (Work.Tubular.normalBundle E ND) x)
            A zν (Work.ThomBordism.fibreIncl_mem _ x) ℤ k).hom
          ((Work.Thom.relCohMap G zν zγ hgm ℤ k).hom
            U.τ)
        = (Work.Thom.relCohMap (efib : C(↥(Work.ThomBordism.fibre
              (Work.Tubular.normalBundle E ND) x),
            ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
              (Work.ThomBordism.Grassmann.padGaussFun E ND x)))) A Bs
            (fun p hp => (hpe p).mp hp) ℤ k).hom
          ((Work.Thom.relCohMap
              (Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND x))
              Bs zγ (Work.ThomBordism.fibreIncl_mem _ _) ℤ k).hom
            U.τ)
      have hcomp : ∀ y ∈ A, G ((Work.ThomBordism.fibreIncl (Work.Tubular.normalBundle E ND) x) y)
          ∈ zγ :=
        fun y hy => hgm _ (Work.ThomBordism.fibreIncl_mem _ x y hy)
      have hcomp' : ∀ y ∈ A,
          (Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
            (Work.ThomBordism.Grassmann.padGaussFun E ND x)) (efib y) ∈ zγ := by
        intro y hy
        rw [show (Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
              (Work.ThomBordism.Grassmann.padGaussFun E ND x)) (efib y)
            = G ((Work.ThomBordism.fibreIncl (Work.Tubular.normalBundle E ND) x) y) from he y]
        exact hcomp y hy
      have hmap : ((Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
            (Work.ThomBordism.Grassmann.padGaussFun E ND x)).comp
            (efib : C(↥(Work.ThomBordism.fibre (Work.Tubular.normalBundle E ND) x),
              ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND x)))))
          = (G.comp (Work.ThomBordism.fibreIncl (Work.Tubular.normalBundle E ND) x)) := by
        apply ContinuousMap.ext
        intro y
        exact he y
      have hAstep : CategoryTheory.CategoryStruct.comp
            (Work.Thom.relCohMap G zν zγ hgm ℤ k)
            (Work.Thom.relCohMap (Work.ThomBordism.fibreIncl (Work.Tubular.normalBundle E ND) x)
              A zν (Work.ThomBordism.fibreIncl_mem _ x) ℤ k)
          = Work.Thom.relCohMap
              ((Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND x)).comp
                (efib : C(↥(Work.ThomBordism.fibre (Work.Tubular.normalBundle E ND) x),
                  ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                    (Work.ThomBordism.Grassmann.padGaussFun E ND x))))) A zγ hcomp' ℤ k :=
        (Work.Thom.relCohMap_compA A zν zγ
          (Work.ThomBordism.fibreIncl (Work.Tubular.normalBundle E ND) x) G
          (Work.ThomBordism.fibreIncl_mem _ x) hgm hcomp ℤ k).trans
        (Work.Thom.relCohMap_congrA A zγ hmap.symm hcomp hcomp' ℤ k)
      have hBstep : CategoryTheory.CategoryStruct.comp
            (Work.Thom.relCohMap
              (Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND x)) Bs zγ
              (Work.ThomBordism.fibreIncl_mem _ _) ℤ k)
            (Work.Thom.relCohMap (efib : C(↥(Work.ThomBordism.fibre
                (Work.Tubular.normalBundle E ND) x),
              ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND x)))) A Bs
              (fun p hp => (hpe p).mp hp) ℤ k)
          = Work.Thom.relCohMap
              ((Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND x)).comp
                (efib : C(↥(Work.ThomBordism.fibre (Work.Tubular.normalBundle E ND) x),
                  ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                    (Work.ThomBordism.Grassmann.padGaussFun E ND x))))) A zγ hcomp' ℤ k :=
        Work.Thom.relCohMap_compA A Bs zγ
          (efib : C(↥(Work.ThomBordism.fibre (Work.Tubular.normalBundle E ND) x),
            ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
              (Work.ThomBordism.Grassmann.padGaussFun E ND x))))
          (Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
            (Work.ThomBordism.Grassmann.padGaussFun E ND x))
          (fun p hp => (hpe p).mp hp) (Work.ThomBordism.fibreIncl_mem _ _) hcomp' ℤ k
      have lhs_eq : (Work.Thom.relCohMap
              (Work.ThomBordism.fibreIncl (Work.Tubular.normalBundle E ND) x) A zν
              (Work.ThomBordism.fibreIncl_mem _ x) ℤ k).hom
            ((Work.Thom.relCohMap G zν zγ hgm ℤ k).hom
              U.τ)
          = (Work.Thom.relCohMap
              ((Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND x)).comp
                (efib : C(↥(Work.ThomBordism.fibre (Work.Tubular.normalBundle E ND) x),
                  ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                    (Work.ThomBordism.Grassmann.padGaussFun E ND x))))) A zγ hcomp' ℤ k).hom
            U.τ := by
        rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp
            (Work.Thom.relCohMap G zν zγ hgm ℤ k)
            (Work.Thom.relCohMap (Work.ThomBordism.fibreIncl (Work.Tubular.normalBundle E ND) x)
              A zν (Work.ThomBordism.fibreIncl_mem _ x) ℤ k), hAstep]
      have rhs_eq : (Work.Thom.relCohMap (efib : C(↥(Work.ThomBordism.fibre
                (Work.Tubular.normalBundle E ND) x),
              ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND x)))) A Bs
              (fun p hp => (hpe p).mp hp) ℤ k).hom
            ((Work.Thom.relCohMap
                (Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                  (Work.ThomBordism.Grassmann.padGaussFun E ND x)) Bs zγ
                (Work.ThomBordism.fibreIncl_mem _ _) ℤ k).hom
              U.τ)
          = (Work.Thom.relCohMap
              ((Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND x)).comp
                (efib : C(↥(Work.ThomBordism.fibre (Work.Tubular.normalBundle E ND) x),
                  ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                    (Work.ThomBordism.Grassmann.padGaussFun E ND x))))) A zγ hcomp' ℤ k).hom
            U.τ := by
        rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp
            (Work.Thom.relCohMap
              (Work.ThomBordism.fibreIncl (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND x)) Bs zγ
              (Work.ThomBordism.fibreIncl_mem _ _) ℤ k)
            (Work.Thom.relCohMap (efib : C(↥(Work.ThomBordism.fibre
                (Work.Tubular.normalBundle E ND) x),
              ↥(Work.ThomBordism.fibre (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
                (Work.ThomBordism.Grassmann.padGaussFun E ND x)))) A Bs
              (fun p hp => (hpe p).mp hp) ℤ k), hBstep]
      rw [lhs_eq, rhs_eq]
    -- the span
    rw [hres]
    have hbij := Work.Thom.bijective_relCohMap_of_homeomorphA
      (Work.ThomBordism.fibrePunctSub (Work.Tubular.normalBundle E ND) x)
      (Work.ThomBordism.fibrePunctSub (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
        (Work.ThomBordism.Grassmann.padGaussFun E ND x))
      efib hpe ℤ k
    have hgenx : Submodule.span ℤ ({(Work.ThomBordism.fibreRes
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
        (Work.ThomBordism.Grassmann.padGaussFun E ND x) k
        U.τ)} : Set _) = ⊤ :=
      thomClass_fibreGenerator (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
        U
        (by simp) (Work.ThomBordism.Grassmann.padGaussFun E ND x)
    exact span_singleton_map_eq_top_of_surjective' _ hbij.2 hgenx
  have hrank : k = (Work.Tubular.normalBundle E ND).rank := (rank_euc _).symm
  exact fibreGenerator_span_top' (Work.Tubular.normalBundle E ND) σ hrank hgen

theorem gtdUWith_span_top {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (U : Work.Thom.ThomClass (Work.ThomBordism.Grassmann.tautologicalBundle k 10) k)
    (hk : 1 ≤ k)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
      = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
    (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) :
    Submodule.span ℤ ({Work.ThomBordism.gtdUWith E ND G hgm U} : Set
      (Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E))) = ⊤ := by
  classical
  set σ : Work.Thom.OpenThom (Work.Tubular.normalBundle E ND) k :=
    (Work.Thom.relCohMap G (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
      (Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)) hgm ℤ k).hom
      U.τ with hσ
  have hspan : Submodule.span ℤ ({σ} : Set (Work.Thom.OpenThom (Work.Tubular.normalBundle E ND) k))
      = ⊤ :=
    gtdUWith_span_top_aux U E ND G hbp hvec hgm
  have he : ∀ x : Work.Tubular.NormalTotal E, x ∈ Work.Tubular.normalNonzero E ↔
      (Work.Tubular.eucNormalHomeomorph E ND).symm x
        ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND) :=
    gtd_mem_iff E ND
  have hbij := Work.Thom.bijective_relCohMap_of_homeomorphA (Work.Tubular.normalNonzero E)
    (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND))
    (Work.Tubular.eucNormalHomeomorph E ND).symm he ℤ k
  have hbij' : Function.Surjective (Work.Thom.relCohMap
      ((Work.Tubular.eucNormalHomeomorph E ND).symm : C(Work.Tubular.NormalTotal E,
        (Work.Tubular.normalBundle E ND).TotalSpace)) (Work.Tubular.normalNonzero E)
      (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND)) (gtd_mem E ND) ℤ k).hom := by
    rw [Work.Thom.relCohMap_congrA (Work.Tubular.normalNonzero E)
      (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND)) rfl (gtd_mem E ND)
      (fun x hx => (he x).mp hx) ℤ k]
    exact hbij.2
  have hgtdU : Work.ThomBordism.gtdUWith E ND G hgm U = (Work.Thom.relCohMap
      ((Work.Tubular.eucNormalHomeomorph E ND).symm : C(Work.Tubular.NormalTotal E,
        (Work.Tubular.normalBundle E ND).TotalSpace)) (Work.Tubular.normalNonzero E)
      (Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND)) (gtd_mem E ND) ℤ k).hom σ := rfl
  rw [hgtdU]
  refine span_singleton_map_eq_top_of_surjective' _ hbij' ?_
  exact hspan

/-! ## The requested statement -/

/-- **The requested lemma.**  The canonical (orientation-compatible) Thom class
`Work.Thom.realThomClassOf` of the tautological bundle in place of the opaque
`Grassmann.tautologicalThomClass`: the pullback of `gtdUWith` along the Gauss/classifying data still
generates the relative cohomology of the normal Thom pair. -/
theorem gtdUWith_realThomClassOf_span_top (k : ℕ) (hk : 1 ≤ k)
    (horiO : ∀ (i j : Work.ThomBordism.Grassmann.ChartIdx k 10)
      (x : ↥((Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet i
        ∩ (Work.ThomBordism.Grassmann.tautologicalBundle k 10).baseSet j)),
      0 < LinearMap.det (((Work.ThomBordism.Grassmann.tautologicalBundle k 10).coordChange i j
        (x : Work.ThomBordism.Grassmann.OG k 10)).toLinearMap)) :
    ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
      (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
        G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
      (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
        = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
      (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
        = Work.PTGeometric.padEuc k 10 (by norm_num)
            (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p))),
      Submodule.span ℤ ({(Work.ThomBordism.gtdUWith E ND G hgm
        (Work.Thom.realThomClassOf hk
          (Work.ThomBordism.Grassmann.tautologicalBundle k 10) horiO))} : Set
        (Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E))) = ⊤ := by
  intro V _ E ND G hgm hbp hvec
  exact gtdUWith_span_top (Work.Thom.realThomClassOf hk
    (Work.ThomBordism.Grassmann.tautologicalBundle k 10) horiO) hk E ND G hbp hvec hgm

end

end Work.ThomBordism
