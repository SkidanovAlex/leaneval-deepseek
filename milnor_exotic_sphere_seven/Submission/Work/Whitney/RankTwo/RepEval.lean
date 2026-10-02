import Mathlib
import Submission.Work.Whitney.RankTwo.RepCapMain
import Submission.Work.Whitney.RankTwo.RepSph2Rep
import Submission.Work.Whitney.RankTwo.RepChain
import Submission.Work.Whitney.RankTwo.RepGeom
import Submission.Work.Whitney.RankTwo.RepEta
import Submission.Work.Whitney.RankTwo.EvalAB
import Submission.Work.Sph3Disc.pairDelta_mixedCup_general
import Submission.Work.Cohomology.MVcapSquares

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.Whitney.RankTwo

open Work.Thom Work.Cohomology Work.Thom.Orientation
open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

noncomputable section

variable (Y : Type) [TopologicalSpace Y]

/-- Proof irrelevance for the cohomology class of a cocycle. -/
theorem cohomologyClassOf_proof_irrel {X : SSet} {n : ℕ} (α : Cochain ℤ X n)
    (h h' : cochainDiff ℤ X α = 0) :
    cohomologyClassOf ℤ X α h = cohomologyClassOf ℤ X α h' :=
  congrArg (fun h'' => cohomologyClassOf ℤ X α h'') (Subsingleton.elim h h')

/-- A representative of the transfer `stepSph Y 1 (Mn 1 Y)`, together with the plain-cochain form
of its cocycle condition. -/
theorem sph2_rep_data :
    ∃ (ψ : ↥(relKern ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) 1))
      (hψrel : relDiffLM ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) 1 ψ = 0),
      relClassOf ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) ψ hψrel = stepSph Y 1 (Mn 1 Y) ∧
      cochainDiff ℤ (ssMSph2 Y) ψ.1 = 0 := by
  obtain ⟨ψ, hψrel, hψclass⟩ :=
    exists_relClassOf ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) 1 (stepSph Y 1 (Mn 1 Y))
  exact ⟨ψ, hψrel, hψclass,
    cochainDiff_of_relDiffLM (X := TopCat.of (Y × MSph 2)) (SphB Y 1) ψ hψrel⟩

/-- The pullback of the representative along `homeoSymm` is a cocycle. -/
theorem pullCM_homeoSymm_coc (ψ : ↥(relKern ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) 1))
    (hψcoc : cochainDiff ℤ (ssMSph2 Y) ψ.1 = 0) :
    cochainDiff ℤ (ssSph2 Y) (pullCM (homeoSymm Y) ψ.1) = 0 := by
  rw [cochainDiff_pullCM (homeoSymm Y), hψcoc]
  exact map_zero _

/-- The class of that pullback. -/
theorem pullCM_homeoSymm_class (ψ : ↥(relKern ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) 1))
    (hψrel : relDiffLM ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) 1 ψ = 0)
    (hψclass : relClassOf ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) ψ hψrel
      = stepSph Y 1 (Mn 1 Y)) :
    cohomologyClassOf ℤ (ssSph2 Y) (pullCM (homeoSymm Y) ψ.1)
        (pullCM_homeoSymm_coc Y ψ
          (cochainDiff_of_relDiffLM (X := TopCat.of (Y × MSph 2)) (SphB Y 1) ψ hψrel))
      = (CohMap (homeoSymm Y) ℤ 1).hom
          ((relToAbs ℤ (SphB Y 1) 1).hom (stepSph Y 1 (Mn 1 Y))) := by
  have hψcoc : cochainDiff ℤ (ssMSph2 Y) ψ.1 = 0 :=
    cochainDiff_of_relDiffLM (X := TopCat.of (Y × MSph 2)) (SphB Y 1) ψ hψrel
  have h2 : (CohMap (homeoSymm Y) ℤ 1).hom
      (cohomologyClassOf ℤ (ssMSph2 Y) ψ.1
        (relClassOf_cochainDiff ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) ψ hψrel))
      = cohomologyClassOf ℤ (ssSph2 Y) (pullCM (homeoSymm Y) ψ.1)
          (by rw [cochainDiff_pullCM (homeoSymm Y), hψcoc]; exact map_zero _) :=
    CohMap_classOf_pullCM (homeoSymm Y) ψ.1 hψcoc
  calc cohomologyClassOf ℤ (ssSph2 Y) (pullCM (homeoSymm Y) ψ.1)
          (pullCM_homeoSymm_coc Y ψ hψcoc)
      = cohomologyClassOf ℤ (ssSph2 Y) (pullCM (homeoSymm Y) ψ.1)
          (by rw [cochainDiff_pullCM (homeoSymm Y), hψcoc]; exact map_zero _) :=
        cohomologyClassOf_proof_irrel _ _ _
    _ = (CohMap (homeoSymm Y) ℤ 1).hom
          (cohomologyClassOf ℤ (ssMSph2 Y) ψ.1
            (relClassOf_cochainDiff ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) ψ hψrel)) := h2.symm
    _ = (CohMap (homeoSymm Y) ℤ 1).hom
          ((relToAbs ℤ (SphB Y 1) 1).hom
            (relClassOf ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) ψ hψrel)) := by
        rw [← relToAbs_classOf_relKern (Z := Y × MSph 2) (SphB Y 1) ψ hψrel]
    _ = (CohMap (homeoSymm Y) ℤ 1).hom
          ((relToAbs ℤ (SphB Y 1) 1).hom (stepSph Y 1 (Mn 1 Y))) := by rw [hψclass]

/-- The pullback along `homeoSymm` vanishes on the lower band. -/
theorem pullCM_homeoSymm_vanish
    (ψ : ↥(relKern ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) 1))
    (hψmem : ψ.1 ∈ relKern ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) 1)
    (σ : (ssSph2 Y) _⦋1⦌)
    (hσ : ∀ q : stdSimplex ℝ (Fin 2),
      (((eSph2 Y 1) σ q : ↥(Sph Y 2)) : R2 Y).2 ∈ mLower 1) :
    genEval ℤ (ssSph2 Y) (pullCM (homeoSymm Y) ψ.1) σ = 0 := by
  rw [genEval_pullCM]
  have hrange : Set.range (fun q : stdSimplex ℝ (Fin 2) =>
      (TopCat.toSSetObjEquivOld (TopCat.of (Y × MSph 2))
        (Opposite.op (SimplexCategory.mk 1)))
        ((TopCat.toSSet.map (TopCat.ofHom (homeoSymm Y))).app
          (Opposite.op (SimplexCategory.mk 1)) σ) q) ⊆ SphB Y 1 := by
    rintro p ⟨q, rfl⟩
    show ((TopCat.toSSetObjEquivOld (TopCat.of (Y × MSph 2))
        (Opposite.op (SimplexCategory.mk 1)))
        ((TopCat.toSSet.map (TopCat.ofHom (homeoSymm Y))).app
          (Opposite.op (SimplexCategory.mk 1)) σ)) q ∈ SphB Y 1
    rw [toSSetObjEquiv_app_eq]
    change ((homeoSymm Y) ((eSph2 Y 1) σ q)).2.1 ∈ mLower 1
    exact hσ q
  obtain ⟨τ', hτ'⟩ := exists_lift_of_range_subset (X := TopCat.of (Y × MSph 2)) (SphB Y 1)
    ((TopCat.toSSet.map (TopCat.ofHom (homeoSymm Y))).app
      (Opposite.op (SimplexCategory.mk 1)) σ)
      (by rw [← TopCat.range_toSSetObjEquivOld]; exact hrange)
  rw [← hτ']
  exact genEval_eq_zero_of_mem_relKern ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) ψ.1 hψmem τ'

/-- The evaluation of a cochain on the chain of straight segments. -/
theorem kronecker_segChain (y : Y) (γ : Cochain ℤ (ssBall Y) 1) :
    kronecker ℤ (ssBall Y) γ (segChain Y y)
      = ∑ k ∈ Finset.range 3, genEval ℤ (ssBall Y) γ (segSimp Y y k) := by
  show γ (segChain Y y) = _
  rw [segChain, map_sum]
  exact Finset.sum_congr rfl fun k _ => kronecker_gen ℤ (ssBall Y) γ (segSimp Y y k)

/-- A relative cochain of the sphere pair vanishes on the pushforward of a simplex of the sphere. -/
theorem genEval_relKern_incl (y : Y) (v : Cochain ℤ (ssR2 Y) 1)
    (hv : v ∈ relKern ℤ (TopCat.of (R2 Y)) (Sph Y 2) 1) (k : ℕ) :
    genEval ℤ (ssR2 Y) v (arcUSimp Y y k) = 0 := by
  rw [← incl_arcSSimp Y y k]
  rw [← genEval_pullback (subtypeIncl (TopCat.of (R2 Y)) (Sph Y 2)) v (arcSSimp Y y k)]
  have hv0 : ((restr ℤ (TopCat.of (R2 Y)) (Sph Y 2)).f 1).hom v = 0 := by
    rw [relKern, LinearMap.mem_ker] at hv
    exact hv
  rw [show ((dualChainMap ℤ (TopCat.of ↥(Sph Y 2)) (TopCat.of (R2 Y))
      (subtypeIncl (TopCat.of (R2 Y)) (Sph Y 2))).f 1).hom v
      = ((restr ℤ (TopCat.of (R2 Y)) (Sph Y 2)).f 1).hom v from rfl, hv0]
  rfl

/-- The lower arcs contribute nothing to the sum. -/
theorem arcSSimp_sum_lower (y : Y)
    (ψ : ↥(relKern ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) 1)) :
    (∑ k ∈ Finset.range 3,
        genEval ℤ (ssSph2 Y) (pullCM (homeoSymm Y) ψ.1) (arcSSimp Y y (3 + k))) = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finset.mem_range] at hk
  exact pullCM_homeoSymm_vanish Y ψ ψ.2 (arcSSimp Y y (3 + k))
    (arc_lower_geom Y y (by omega))

/-- The upper arcs are the cap images of the straight segments. -/
theorem arcSSimp_sum_upper (y : Y)
    (ψ : ↥(relKern ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) 1)) :
    (∑ k ∈ Finset.range 3,
        genEval ℤ (ssSph2 Y) (pullCM (homeoSymm Y) ψ.1) (arcSSimp Y y k))
      = (pullCM (capMapPairSph Y 1) ψ.1) (segChain Y y) := by
  have h3 : ∀ k ∈ Finset.range 3,
      genEval ℤ (ssSph2 Y) (pullCM (homeoSymm Y) ψ.1) (arcSSimp Y y k)
        = genEval ℤ (ssBall Y) (pullCM (capMapPairSph Y 1) ψ.1) (segSimp Y y k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [arc_cap_geom Y y (by omega)]
    rw [← genEval_pullCM (capHomeo Y) (pullCM (homeoSymm Y) ψ.1) (segSimp Y y k),
      pullCM_capHomeo_eq]
  rw [Finset.sum_congr rfl h3, ← kronecker_segChain Y y (pullCM (capMapPairSph Y 1) ψ.1)]
  rfl

/-- **The number `-1` on the chain of straight segments.** -/
theorem pullCM_capPairSph_segChain (y : Y)
    (ψ : ↥(relKern ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) 1))
    (hψrel : relDiffLM ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) 1 ψ = 0)
    (hψclass : relClassOf ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) ψ hψrel
      = stepSph Y 1 (Mn 1 Y)) :
    (pullCM (capMapPairSph Y 1) ψ.1) (segChain Y y) = -1 := by
  obtain ⟨h, hh⟩ := cap_rep_eq_eta Y ψ hψrel hψclass
  have heq : pullCM (capMapPairSph Y 1) ψ.1 = eta Y + cochainDiff ℤ (ssBall Y) h.1 := by
    rw [← hh]; abel
  have hvan : ∀ (p : BBall Y) (hp : p ∈ DiscB Y 1),
      genEval ℤ (ssBall Y) h.1 (ptBall Y p) = 0 := by
    intro p hp
    have hrange : Set.range (fun z : stdSimplex ℝ (Fin 1) =>
        (eBall Y 0) (ptBall Y p) z) ⊆ DiscB Y 1 := by
      rintro _ ⟨z, rfl⟩
      simp only [eBall_ptBall, ContinuousMap.const_apply]
      exact hp
    obtain ⟨τ, hτ⟩ := exists_lift_of_range_subset (X := TopCat.of (BBall Y)) (DiscB Y 1)
      (ptBall Y p) (by rw [← TopCat.range_toSSetObjEquivOld]; exact hrange)
    rw [← hτ]
    exact genEval_eq_zero_of_mem_relKern ℤ (TopCat.of (BBall Y)) (DiscB Y 1) h.1 h.2 τ
  have hpt : ∀ (p : BBall Y) (hp : p ∈ DiscB Y 1),
      kronecker ℤ (ssBall Y) h.1
        (((ssBall Y).ιChainComplex (R := zR) (ptBall Y p)).hom 1) = 0 := by
    intro p hp
    rw [kronecker_gen]
    exact hvan p hp
  have hminus : (y, ⟨sphMinus, sphMinus_mem_ball⟩) ∈ DiscB Y 1 :=
    show sphMinus ∈ mSph 1 from sphMinus_mem
  have hplus : (y, ⟨sphPlus, sphPlus_mem_ball⟩) ∈ DiscB Y 1 :=
    show sphPlus ∈ mSph 1 from sphPlus_mem
  have hd : kronecker ℤ (ssBall Y) (cochainDiff ℤ (ssBall Y) h.1) (segChain Y y) = 0 := by
    rw [show kronecker ℤ (ssBall Y) (cochainDiff ℤ (ssBall Y) h.1) (segChain Y y)
        = kronecker ℤ (ssBall Y) h.1
            (((ssBall Y).chainComplex zR).d 1 0 (segChain Y y)) from rfl]
    rw [segChain_boundary Y y]
    rw [show kronecker ℤ (ssBall Y) h.1
          (((ssBall Y).ιChainComplex (R := zR) (ballMinus Y y)).hom 1
            - ((ssBall Y).ιChainComplex (R := zR) (ballPlus Y y)).hom 1)
        = kronecker ℤ (ssBall Y) h.1
            (((ssBall Y).ιChainComplex (R := zR) (ballMinus Y y)).hom 1)
          - kronecker ℤ (ssBall Y) h.1
            (((ssBall Y).ιChainComplex (R := zR) (ballPlus Y y)).hom 1) from
        LinearMap.map_sub (h.1 : Cochain ℤ (ssBall Y) 0) _ _]
    rw [show ballMinus Y y = ptBall Y (y, ⟨sphMinus, sphMinus_mem_ball⟩) from rfl,
      show ballPlus Y y = ptBall Y (y, ⟨sphPlus, sphPlus_mem_ball⟩) from rfl]
    rw [hpt _ hminus, hpt _ hplus, sub_self]
  have he : kronecker ℤ (ssBall Y) (eta Y) (segChain Y y) = -1 := by
    rw [show (eta Y) = cochainDiff ℤ (ssBall Y) (sgBall Y) from rfl]
    rw [show kronecker ℤ (ssBall Y) (cochainDiff ℤ (ssBall Y) (sgBall Y)) (segChain Y y)
        = kronecker ℤ (ssBall Y) (sgBall Y)
            (((ssBall Y).chainComplex zR).d 1 0 (segChain Y y)) from rfl]
    rw [segChain_boundary Y y]
    rw [show kronecker ℤ (ssBall Y) (sgBall Y)
          (((ssBall Y).ιChainComplex (R := zR) (ballMinus Y y)).hom 1
            - ((ssBall Y).ιChainComplex (R := zR) (ballPlus Y y)).hom 1)
        = kronecker ℤ (ssBall Y) (sgBall Y)
            (((ssBall Y).ιChainComplex (R := zR) (ballMinus Y y)).hom 1)
          - kronecker ℤ (ssBall Y) (sgBall Y)
            (((ssBall Y).ιChainComplex (R := zR) (ballPlus Y y)).hom 1) from
        LinearMap.map_sub (sgBall Y) _ _]
    rw [show kronecker ℤ (ssBall Y) (sgBall Y)
          (((ssBall Y).ιChainComplex (R := zR) (ballMinus Y y)).hom 1)
        = genEval ℤ (ssBall Y) (sgBall Y) (ballMinus Y y) from rfl,
      genEval_sgBall_ballMinus Y y,
      show kronecker ℤ (ssBall Y) (sgBall Y)
          (((ssBall Y).ιChainComplex (R := zR) (ballPlus Y y)).hom 1)
        = genEval ℤ (ssBall Y) (sgBall Y) (ballPlus Y y) from rfl,
      genEval_sgBall_ballPlus Y y]
    norm_num
  rw [show (pullCM (capMapPairSph Y 1) ψ.1) (segChain Y y)
      = kronecker ℤ (ssBall Y) (pullCM (capMapPairSph Y 1) ψ.1) (segChain Y y) from rfl, heq]
  rw [show kronecker ℤ (ssBall Y) (eta Y + cochainDiff ℤ (ssBall Y) h.1) (segChain Y y)
      = kronecker ℤ (ssBall Y) (eta Y) (segChain Y y)
        + kronecker ℤ (ssBall Y) (cochainDiff ℤ (ssBall Y) h.1) (segChain Y y) from
    kronecker_add ℤ (ssBall Y) (eta Y) (cochainDiff ℤ (ssBall Y) h.1) (segChain Y y)]
  rw [hd, he]
  norm_num

/-- **The evaluation of the pullback along `tcmF` of the lift.** -/
theorem pullCM_tcmF_bt_c (y : Y) (bt : Cochain ℤ (ssR2 Y) 1)
    (ψ : ↥(relKern ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) 1))
    (hψrel : relDiffLM ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) 1 ψ = 0)
    (hψclass : relClassOf ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) ψ hψrel
      = stepSph Y 1 (Mn 1 Y))
    (hbt : ((restr ℤ (TopCat.of (R2 Y)) (Sph Y 2)).f 1).hom bt
      = pullCM (homeoSymm Y) ψ.1) :
    (pullCM (tcmF Y 1 1) bt) (c Y y) = -1 := by
  have h1 : (pullCM (tcmF Y 1 1) bt) (c Y y)
      = ∑ k ∈ Finset.range 6, genEval ℤ (ssR2 Y) bt (arcUSimp Y y k) := by
    rw [show (pullCM (tcmF Y 1 1) bt) (c Y y)
        = kronecker ℤ (ssX Y) (pullCM (tcmF Y 1 1) bt) (c Y y) from rfl, kronecker_c_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [genEval_pullCM, tcmF_arcSimp Y y k]
  rw [h1]
  have h2 : ∀ k ∈ Finset.range 6,
      genEval ℤ (ssR2 Y) bt (arcUSimp Y y k)
        = genEval ℤ (ssSph2 Y) (pullCM (homeoSymm Y) ψ.1) (arcSSimp Y y k) := by
    intro k _
    rw [← incl_arcSSimp Y y k]
    rw [← genEval_pullback (subtypeIncl (TopCat.of (R2 Y)) (Sph Y 2)) bt (arcSSimp Y y k)]
    rw [show ((dualChainMap ℤ (TopCat.of ↥(Sph Y 2)) (TopCat.of (R2 Y))
        (subtypeIncl (TopCat.of (R2 Y)) (Sph Y 2))).f 1).hom bt
        = ((restr ℤ (TopCat.of (R2 Y)) (Sph Y 2)).f 1).hom bt from rfl]
    rw [hbt]
  rw [Finset.sum_congr rfl h2]
  rw [show (∑ k ∈ Finset.range 6,
        genEval ℤ (ssSph2 Y) (pullCM (homeoSymm Y) ψ.1) (arcSSimp Y y k))
      = (∑ k ∈ Finset.range 3,
            genEval ℤ (ssSph2 Y) (pullCM (homeoSymm Y) ψ.1) (arcSSimp Y y k))
        + ∑ k ∈ Finset.range 3,
            genEval ℤ (ssSph2 Y) (pullCM (homeoSymm Y) ψ.1) (arcSSimp Y y (3 + k)) from
      Finset.sum_range_add _ 3 3]
  rw [arcSSimp_sum_lower Y y ψ, add_zero]
  rw [arcSSimp_sum_upper Y y ψ]
  exact pullCM_capPairSph_segChain Y y ψ hψrel hψclass

end

end Work.Whitney.RankTwo
