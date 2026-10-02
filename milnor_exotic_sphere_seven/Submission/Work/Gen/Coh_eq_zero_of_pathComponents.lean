import Mathlib
import Submission.Work.Gen.PathCompDefs
import Submission.Work.Gen.cochainAssembly
import Submission.Work.Gen.cochain_homologypi_eq_zero
import Submission.Work.Thom.Coh_zero_cover_injective
import Submission.Work.Thom.isOrientedOver_of_det_pos

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Gen

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- **Degree zero case of the component patching.**  A degree zero cohomology class of a space
`X` whose pullback to every path component of `X` vanishes is zero.  A class of `H⁰(X;ℤ)` is
determined by its evaluations `Work.Cohomology.h0Ev` at the points of `X`
(`Work.Thom.h0Ev_eq_zero`); a `0`-simplex `s` of `X` lies in the path component
`c := Work.Gen.pointComp (TopCat.toSSetObj₀Equiv s)` of its point, and the corresponding
`0`-simplex of that component is mapped to `s` by the inclusion, so
`Work.Thom.h0Ev_pullback` computes `h0Ev s z` as an evaluation of
`(CohMap (pathCompIncl X c)).hom z`, which is `0`. -/
theorem Coh_eq_zero_of_pathComponents_zero (z : Work.Thom.Coh ℤ 0 X)
    (h : ∀ c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X)),
      (Work.Thom.CohMap (pathCompIncl X c) ℤ 0).hom z = 0) : z = 0 := by
  refine Work.Thom.h0Ev_eq_zero z (fun s => ?_)
  set p : X := TopCat.toSSetObj₀Equiv (X := TopCat.of X) s with hp
  set c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X)) := pointComp p with hc
  have hmem : pointComp p = c := by rw [hc]
  set s' : (TopCat.toSSet.obj (pathComp X c)) _⦋0⦌ :=
    TopCat.toSSetObj₀Equiv (X := pathComp X c).symm (⟨p, hmem⟩ : ↥(pathComp X c)) with hs'
  have himg : (TopCat.toSSet.map (TopCat.ofHom (pathCompIncl X c))).app
      (Opposite.op ⦋0⦌) s' = s := by
    apply TopCat.toSSetObj₀Equiv.injective
    rw [Work.Thom.toSSetObj₀Equiv_map]
    show (pathCompIncl X c) (TopCat.toSSetObj₀Equiv (X := pathComp X c) s') =
      TopCat.toSSetObj₀Equiv (X := TopCat.of X) s
    rw [hs', Equiv.apply_symm_apply]
    exact hp
  have hnat := Work.Thom.h0Ev_pullback (pathCompIncl X c) s' z
  rw [h c, map_zero] at hnat
  rw [himg] at hnat
  exact hnat.symm

/-- **Singular cohomology is detected by the path components**: a cohomology class `z` vanishes as
soon as its pullbacks along the inclusions of all path components vanish.

The honest content is the chain-level decomposition `C_*(X) = ⊕_c C_*(X_c)` of the singular chain
complex of `X` into the direct sums of the chain complexes of its path components (every singular
simplex has path-connected image, hence lies in a path component; the faces of a simplex stay in
the same component), which dualises to `C^*(X) = ∏_c C^*(X_c)` and passes to cohomology.

`Work.Gen.pathComp X c` is the component of `c` as a subspace and `Work.Gen.pathCompIncl X c` its
inclusion (both defined in `Submission/Work/Gen/tensorLine_c1_additive.lean`).  Equivalent
formulations of the proof are welcome. -/
theorem Coh_eq_zero_of_pathComponents {X : Type} [TopologicalSpace X] {n : ℕ}
    (z : Work.Thom.Coh ℤ n X)
    (h : ∀ c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X)),
      (Work.Thom.CohMap (Work.Gen.pathCompIncl X c) ℤ n).hom z = 0) : z = 0 := by
  rcases n with _ | k
  · exact Coh_eq_zero_of_pathComponents_zero z h
  · -- every cohomology class is the class of a cocycle
    obtain ⟨α, hα, hz⟩ :=
      Work.Cohomology.exists_cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of X)) (k + 1) z
    rw [← hz] at h
    rw [← hz]
    -- on every component the pullback of `α` is a coboundary
    have hex : ∀ c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X)),
        ∃ w : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj (pathComp X c)) k,
          Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj (pathComp X c)) w =
            ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (pathCompIncl X c)))
              (ModuleCat.of ℤ ℤ)).f (k + 1)).hom.dualMap α := by
      intro c
      have hβ : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj (pathComp X c))
          (((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (pathCompIncl X c)))
            (ModuleCat.of ℤ ℤ)).f (k + 1)).hom.dualMap α) = 0 :=
        Work.Cohomology.cochainDiff_dualMap_chainComplexMap ℤ
          (TopCat.toSSet.map (TopCat.ofHom (pathCompIncl X c))) α hα
      have hclass : Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj (pathComp X c))
          (((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (pathCompIncl X c)))
            (ModuleCat.of ℤ ℤ)).f (k + 1)).hom.dualMap α)
          (Work.Cohomology.cochainDiff_dualMap_chainComplexMap ℤ
            (TopCat.toSSet.map (TopCat.ofHom (pathCompIncl X c))) α hα) = 0 := by
        rw [← Work.Cohomology.singularCohomologyMap_classOf ℤ
          (TopCat.ofHom (pathCompIncl X c)) α hα]
        exact h c
      exact exists_cochainDiff_eq_of_class_zero _ hβ hclass
    -- assemble the componentwise primitives
    let w : ∀ c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X)),
        Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj (pathComp X c)) k :=
      fun c => (hex c).choose
    have hw : ∀ c, Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj (pathComp X c)) (w c) =
        ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (pathCompIncl X c)))
          (ModuleCat.of ℤ ℤ)).f (k + 1)).hom.dualMap α := fun c => (hex c).choose_spec
    have hfinal : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of X))
        (assemble w) = α := by
      rw [cochainDiff_assemble]
      rw [show (fun c => Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj (pathComp X c))
            (w c)) =
          (fun c => ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom (pathCompIncl X c)))
            (ModuleCat.of ℤ ℤ)).f (k + 1)).hom.dualMap α) from funext hw]
      exact assemble_pullback_dualMap α
    -- `α` is a coboundary, hence its class vanishes
    exact (Work.Cohomology.cohomologyClassOf_congr ℤ (TopCat.toSSet.obj (TopCat.of X))
        hfinal.symm hα (cochainDiff_cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of X))
          (assemble w))).trans
      (cohomologyClassOf_cochainDiff_eq_zero (TopCat.toSSet.obj (TopCat.of X)) (assemble w))

end

end Work.Gen
