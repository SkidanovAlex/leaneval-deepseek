/-
# `BridgeSquare/CuspLift.lean` — lifting singular simplices through the cusp parametrisation

`Work.BridgeSquare.cuspMap : Cop → M̄` is the parametrisation of the cusped boundary `Tset ⊆ M̄`
by the boundary of the filling pieces (the gluing homeomorphism `glue` inverted, in the
cusp-major coordinates).  This file records the consequences that make the surjectivity of
`H_k(cuspMap)` provable:

* `cuspLift_glue` — on `Tset`, the inverse of `cuspMap` is `z ↦ homeoBdrySubSig (glue ⟨z, hz⟩)`;
* `cuspLift_injective`;
* `cuspLift_exists_singularSimplex` — every singular simplex of `M̄` whose image lies in `Tset`
  is the image under `cuspMap` of a singular simplex of `Cop`;
* `cuspLift_exists_chainMap_iota` — the same at the level of the basis vectors `ιChainComplex` of
  the free modules of singular chains.

These are used by `Work.BridgeSquare.PsiM_truncCell_mem_range` (through the support statement
`Work.BridgeSquare.PsiM_truncSupported_mem_range`) and hence by
`Work.BridgeSquare.cuspMap_surjective`.
-/
import Mathlib
import Submission.Work.BridgeSquare.Data
import Submission.Work.Homology.SimplexShim

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.BridgeSquare

noncomputable section

variable [rt : Work.Space.RTData]

/-- **The cusp parametrisation, evaluated**: `cuspMap` is `tauBdry` after the canonical
homeomorphism between the glued boundary and `⊔_v (∂[-1,1]² × T²_v)`. -/
theorem cuspLift_apply (x : Cop (rt := rt)) :
    (cuspMap (rt := rt)) x
      = Work.Space.Assembly.tauBdry rt.core
          ((Work.Space.Split.homeoBdrySubSig rt.core).symm x) := rfl

/-- **The inverse of `cuspMap` on `Tset`.**  For a point `z` of the cusped boundary, the point of
`Cop` obtained by gluing `z` back into the filling pieces is a preimage of `z`. -/
theorem cuspLift_glue (z : rt.core.Mbar) (hz : z ∈ rt.core.Tset) :
    (cuspMap (rt := rt))
        (Work.Space.Split.homeoBdrySubSig rt.core (rt.core.glue ⟨z, hz⟩)) = z := by
  rw [cuspMap]
  simp only [TopCat.ofHom_comp]
  show Work.Space.Assembly.tauBdry rt.core
      ((Work.Space.Split.homeoBdrySubSig rt.core).symm
        (Work.Space.Split.homeoBdrySubSig rt.core (rt.core.glue ⟨z, hz⟩))) = z
  rw [Homeomorph.symm_apply_apply, Work.Space.Assembly.tauBdry_apply]
  exact congrArg Subtype.val (Homeomorph.symm_apply_apply rt.core.glue ⟨z, hz⟩)

/-- `tauBdry` is injective (it is the gluing homeomorphism inverted). -/
theorem cuspLift_tauBdry_injective : Function.Injective (Work.Space.Assembly.tauBdry rt.core) := by
  intro q q' h
  have h1 : ((rt.core.glue.symm q : rt.core.Tset) : rt.core.Mbar)
      = ((rt.core.glue.symm q' : rt.core.Tset) : rt.core.Mbar) := h
  have h2 : (rt.core.glue.symm q : rt.core.Tset) = rt.core.glue.symm q' := Subtype.ext h1
  have h3 : rt.core.glue (rt.core.glue.symm q) = rt.core.glue (rt.core.glue.symm q') :=
    congrArg _ h2
  rwa [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply] at h3

/-- **The cusp parametrisation is injective**: it is a bijection onto the cusped boundary. -/
theorem cuspLift_injective : Function.Injective (cuspMap (rt := rt)) := by
  intro x y hxy
  have hφ : (Work.Space.Split.homeoBdrySubSig rt.core).symm x
      = (Work.Space.Split.homeoBdrySubSig rt.core).symm y := by
    apply cuspLift_tauBdry_injective
    rw [cuspMap] at hxy
    simp only [TopCat.ofHom_comp] at hxy
    exact hxy
  exact (Work.Space.Split.homeoBdrySubSig rt.core).symm.injective hφ

/-- **Lifting a singular simplex whose image lies in the cusped boundary.**  If the singular
`k`-simplex `x` of `M̄` has image in `Tset`, then it is the image under `cuspMap` of a singular
`k`-simplex of `Cop`: the pointwise inverse of `cuspMap` on `Tset` is continuous, so it can be
composed with `x`. -/
theorem cuspLift_exists_singularSimplex (k : ℕ)
    (x : (TopCat.toSSet.obj (Mop (rt := rt))).obj (Opposite.op (SimplexCategory.mk k)))
    (hx : ∀ w : Convexity.StdSimplex ℝ (Fin (k + 1)),
        TopCat.toSSetObjEquiv (Mop (rt := rt)) (Opposite.op (SimplexCategory.mk k)) x w
          ∈ rt.core.Tset) :
    ∃ y : (TopCat.toSSet.obj (Cop (rt := rt))).obj (Opposite.op (SimplexCategory.mk k)),
      (TopCat.toSSet.map (cuspMap (rt := rt))).app (Opposite.op (SimplexCategory.mk k)) y = x := by
  have hcont : Continuous fun w : Convexity.StdSimplex ℝ (Fin (k + 1)) =>
      (Work.Space.Split.homeoBdrySubSig rt.core)
        (rt.core.glue ⟨TopCat.toSSetObjEquiv (Mop (rt := rt)) _ x w, hx w⟩) := by
    refine (Work.Space.Split.homeoBdrySubSig rt.core).continuous.comp ?_
    exact rt.core.glue.continuous.comp
      (Continuous.subtype_mk (TopCat.toSSetObjEquiv (Mop (rt := rt)) _ x).continuous hx)
  let h' : C(Convexity.StdSimplex ℝ (Fin (k + 1)), Cop (rt := rt)) :=
    ⟨fun w => (Work.Space.Split.homeoBdrySubSig rt.core)
        (rt.core.glue ⟨TopCat.toSSetObjEquiv (Mop (rt := rt)) _ x w, hx w⟩), hcont⟩
  refine ⟨(TopCat.toSSetObjEquiv (Cop (rt := rt)) _).symm h', ?_⟩
  apply (TopCat.toSSetObjEquiv (Mop (rt := rt)) _).injective
  ext w
  have hy1 : (TopCat.toSSetObjEquiv (Cop (rt := rt))
        (Opposite.op (SimplexCategory.mk k)) ((TopCat.toSSetObjEquiv (Cop (rt := rt))
          (Opposite.op (SimplexCategory.mk k))).symm h')) = h' :=
    Equiv.apply_symm_apply _ _
  have step1 : (TopCat.toSSetObjEquiv (Mop (rt := rt)) _
        ((TopCat.toSSet.map (cuspMap (rt := rt))).app _ ((TopCat.toSSetObjEquiv (Cop (rt := rt)) _).symm h'))) w
      = (cuspMap (rt := rt))
          ((TopCat.toSSetObjEquiv (Cop (rt := rt)) _ ((TopCat.toSSetObjEquiv (Cop (rt := rt)) _).symm h')) w) := rfl
  rw [step1, hy1]
  exact cuspLift_glue _ _

/-- **The chain-level form of the lift**: the basis vector `ιChainComplex x` of a singular
simplex `x` with image in `Tset` lies in the image of the singular chain map induced by
`cuspMap`. -/
theorem cuspLift_exists_chainMap_iota (k : ℕ)
    (x : (TopCat.toSSet.obj (Mop (rt := rt))).obj (Opposite.op (SimplexCategory.mk k)))
    (hx : ∀ w : Convexity.StdSimplex ℝ (Fin (k + 1)),
        TopCat.toSSetObjEquiv (Mop (rt := rt)) (Opposite.op (SimplexCategory.mk k)) x w
          ∈ rt.core.Tset) :
    ∃ y : (singCxFun.obj (Cop (rt := rt))).X k,
      (singCxFun.map (cuspMap (rt := rt))).f k y
        = ((TopCat.toSSet.obj (Mop (rt := rt))).ιChainComplex (R := ModuleCat.of ℤ ℤ) x).hom 1 := by
  obtain ⟨ysimplex, hymap⟩ := cuspLift_exists_singularSimplex k x hx
  refine ⟨((TopCat.toSSet.obj (Cop (rt := rt))).ιChainComplex (R := ModuleCat.of ℤ ℤ) ysimplex).hom 1, ?_⟩
  change (SSet.chainComplexMap (TopCat.toSSet.map (cuspMap (rt := rt))) (ModuleCat.of ℤ ℤ)).f k
      ((ConcreteCategory.hom
        ((TopCat.toSSet.obj (Cop (rt := rt))).ιChainComplex (R := ModuleCat.of ℤ ℤ) ysimplex)) (1 : ℤ))
    = (ConcreteCategory.hom
        ((TopCat.toSSet.obj (Mop (rt := rt))).ιChainComplex (R := ModuleCat.of ℤ ℤ) x)) (1 : ℤ)
  have hkey : (TopCat.toSSet.obj (Cop (rt := rt))).ιChainComplex (R := ModuleCat.of ℤ ℤ) ysimplex
      ≫ (SSet.chainComplexMap (TopCat.toSSet.map (cuspMap (rt := rt))) (ModuleCat.of ℤ ℤ)).f k
      = (TopCat.toSSet.obj (Mop (rt := rt))).ιChainComplex (R := ModuleCat.of ℤ ℤ) x := by
    rw [SSet.ι_chainComplexMap_f, hymap]
  have h2 := ConcreteCategory.congr_hom hkey (1 : ℤ)
  simpa only [ConcreteCategory.comp_apply] using h2

end

end Work.BridgeSquare
