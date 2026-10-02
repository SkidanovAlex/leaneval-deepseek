import Mathlib
import Submission.Work.Thom.chartCoeffAux
import Submission.Work.Cohomology.h0Evaluation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Every function on `π₀` is realised by a degree-zero class

For a topological space `X` the singular model of `H⁰(X;ℤ)` is the module of `0`-cocycles of the
singular simplicial set, i.e. of those functions on the vertices which are constant along edges
(paths).  Such a cocycle therefore *descends* to the set of path components `π₀ X`, and conversely
every function on `π₀ X` gives a `0`-cocycle.  This module proves that the corresponding class
realises the prescribed values:

`Work.ThomBordism.GtdFlip.exists_class_ptEv` — for every `g : π₀ X → ℤ` there is a class
`c₀ ∈ H⁰(X;ℤ)` with `ptEv x c₀ = g (π₀.mk x)` for every point `x`.

The construction is the same one that produces the indicator class of a union of components
(`Work.Thom.indicatorCochain`): the degree-zero chains are the coproduct of copies of `ℤ` indexed
by the *path components* (`SSet.π₀.fromChainComplexXZero`), so the componentwise scalar
multiplication by `g` is a legitimate cochain; it is a cocycle because it factors through `π₀`.

* `Work.ThomBordism.GtdFlip.gCochain` — the `0`-cochain with prescribed component values;
* `Work.ThomBordism.GtdFlip.gCochain_cocycle` — it is a `0`-cocycle;
* `Work.ThomBordism.GtdFlip.genEval_gCochain` — its value on the generator of a `0`-simplex;
* `Work.ThomBordism.GtdFlip.exists_class_ptEv` — the class it defines.
-/

namespace Work.ThomBordism.GtdFlip

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

noncomputable section

/-- **The `0`-cochain with prescribed values on the path components.**  The zeroth chains of the
singular complex of `X` map onto the coproduct `∐_{c ∈ π₀ X} ℤ` (`SSet.π₀.fromChainComplexXZero`),
so sending the component `c` to the scalar `g c` defines a cochain. -/
def gCochain (X : Type) [TopologicalSpace X]
    (g : (TopCat.toSSet.obj (TopCat.of X)).π₀ → ℤ) :
    Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj (TopCat.of X)) 0 :=
  ModuleCat.Hom.hom (SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj (TopCat.of X))
      (ModuleCat.of ℤ ℤ) ≫
    Sigma.desc (fun c => ModuleCat.ofHom ((g c : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))))

/-- **The cochain `gCochain X g` is a `0`-cocycle**: it factors through `π₀`, and the differential
`d 1 0` of the chain complex factors through the projection to `π₀`
(`SSet.π₀.d_fromChainComplexXZero`). -/
theorem gCochain_cocycle (X : Type) [TopologicalSpace X]
    (g : (TopCat.toSSet.obj (TopCat.of X)).π₀ → ℤ) :
    Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of X)) (gCochain X g) = 0 := by
  have h : ((TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of ℤ ℤ)).d 1 0 ≫
      (SSet.π₀.fromChainComplexXZero (TopCat.toSSet.obj (TopCat.of X))
        (ModuleCat.of ℤ ℤ) ≫
        Sigma.desc (fun c => ModuleCat.ofHom ((g c : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)))) = 0 := by
    rw [← Category.assoc, SSet.π₀.d_fromChainComplexXZero, zero_comp]
  have h2 := congrArg ModuleCat.Hom.hom h
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
  have h3 : (gCochain X g).comp
      (((TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of ℤ ℤ)).d 1 0).hom = 0 := by
    rw [gCochain]
    exact h2
  exact h3

/-- **The value of the cochain `gCochain X g` on the generator of a `0`-simplex** is `g` of the
path component of that simplex. -/
theorem genEval_gCochain (X : Type) [TopologicalSpace X]
    (g : (TopCat.toSSet.obj (TopCat.of X)).π₀ → ℤ)
    (s : (TopCat.toSSet.obj (TopCat.of X)) _⦋0⦌) :
    Work.Cohomology.genEval ℤ (TopCat.toSSet.obj (TopCat.of X)) (gCochain X g) s
      = g (SSet.π₀.mk s) := by
  have h2 : (ModuleCat.Hom.hom (SSet.π₀.fromChainComplexXZero
        (TopCat.toSSet.obj (TopCat.of X)) (ModuleCat.of ℤ ℤ)))
        (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1)
      = (ModuleCat.Hom.hom (Sigma.ι (fun _ : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X)) =>
          ModuleCat.of ℤ ℤ) (SSet.π₀.mk s))) 1 := by
    have hh := congrArg (fun k => (ModuleCat.Hom.hom k) 1)
      (SSet.π₀.comp_fromChainComplexXZero (X := TopCat.toSSet.obj (TopCat.of X))
        (ModuleCat.of ℤ ℤ) s)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  have h3 : (ModuleCat.Hom.hom (Sigma.desc (fun c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X)) =>
        ModuleCat.ofHom ((g c : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)))))
        ((ModuleCat.Hom.hom (Sigma.ι (fun _ : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X)) =>
          ModuleCat.of ℤ ℤ) (SSet.π₀.mk s))) 1)
      = g (SSet.π₀.mk s) := by
    have hh := congrArg (fun k => (ModuleCat.Hom.hom k) 1)
      (Sigma.ι_desc (fun c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X)) =>
        ModuleCat.ofHom ((g c : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ))) (SSet.π₀.mk s))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh
    rw [hh, ModuleCat.hom_ofHom, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, mul_one]
  show (gCochain X g) (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
      (R := ModuleCat.of ℤ ℤ) s).hom 1) = g (SSet.π₀.mk s)
  rw [gCochain, ModuleCat.hom_comp]
  simp only [LinearMap.comp_apply]
  rw [h2, h3]

/-- **Every function on the path components of `X` is the system of point evaluations of a
degree-zero class.**  The class is the one defined by the cocycle `gCochain X g`. -/
theorem exists_class_ptEv (X : Type) [TopologicalSpace X]
    (g : (TopCat.toSSet.obj (TopCat.of X)).π₀ → ℤ) :
    ∃ c₀ : Work.Thom.Coh ℤ 0 X, ∀ x : X,
      Work.Thom.ptEv x c₀
        = g (SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := TopCat.of X)).symm x)) := by
  let c₀ : Work.Thom.Coh ℤ 0 X := Work.Cohomology.cohomologyClassOf ℤ
    (TopCat.toSSet.obj (TopCat.of X)) (gCochain X g) (gCochain_cocycle X g)
  refine ⟨c₀, fun x => ?_⟩
  rw [Work.Thom.ptEv_apply]
  show Work.Cohomology.h0Ev (TopCat.toSSet.obj (TopCat.of X))
      ((TopCat.toSSetObj₀Equiv (X := TopCat.of X)).symm x)
      (Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of X)) (gCochain X g)
        (gCochain_cocycle X g))
    = g (SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := TopCat.of X)).symm x))
  rw [Work.Cohomology.h0Ev_classOf]
  exact genEval_gCochain X g _

end

end Work.ThomBordism.GtdFlip
