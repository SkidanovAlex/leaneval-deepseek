import Mathlib
import Submission.Work.RatHurewicz.Bridge.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Naturality and coordinates of the simplicial/cubical comparison `Sim`

* `coords_mk` : `coords` is a left inverse of `mk`;
* `coords_chainMap` : naturality of `coords` under the chain map of a continuous map;
* `simplexToCube_naturality` : `simplexToCube` is natural in the space;
* `sim_naturality` : `Sim` is natural in the space.

Together with `Bridge.sim_chainMap` these are the two properties of the comparison map
`σ ↦ (-1)^n • single (σ ∘ H n)` that the bridge `Work.RatHurewicz.cubicalBridgeDeg` consumes.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology
open scoped Simplicial
open Work.Stems.Cubical

namespace Work.RatHurewicz.Bridge

noncomputable section

/-- The generator of the chain complex attached to a simplex, as a multiple of the generator with
coefficient `1`. -/
theorem ιChainComplex_hom_zsmul (X : SSet) (n : ℕ) (a : X.obj (Opposite.op (SimplexCategory.mk n)))
    (b : ℤ) :
    (X.ιChainComplex (R := ModuleCat.of ℤ ℤ) a).hom b
      = b • (X.ιChainComplex (R := ModuleCat.of ℤ ℤ) a).hom (1 : ℤ) := by
  have h := map_zsmul (ModuleCat.Hom.hom (X.ιChainComplex (R := ModuleCat.of ℤ ℤ) a)) b (1 : ℤ)
  rw [show b • (1 : ℤ) = b by simp] at h
  exact h

/-- `coords` is a left inverse of `mk`. -/
theorem coords_mk (X : SSet) (n : ℕ) (c : X.obj (Opposite.op (SimplexCategory.mk n)) →₀ ℤ) :
    Work.Cohomology.Crux33.coords X n (Work.Cohomology.Crux33.mk X n c) = c := by
  have h1 : ∀ (a : X.obj (Opposite.op (SimplexCategory.mk n))) (b : ℤ),
      Work.Cohomology.Crux33.coords X n
        ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) a).hom b) = Finsupp.single a b := by
    intro a b
    rw [ιChainComplex_hom_zsmul, map_zsmul, Work.Cohomology.Crux33.coords_ι,
      Finsupp.smul_single', mul_one]
  refine Finsupp.induction c ?_ ?_
  · simp
  · intro a b f ha hb hf
    simp only [map_add, Work.Cohomology.Crux33.mk_single, h1, hf]

/-- Naturality of `coords` under the chain map induced by a morphism of simplicial sets. -/
theorem coords_chainComplexMap (X Y : SSet) (f : X ⟶ Y) (n : ℕ)
    (c : X.obj (Opposite.op (SimplexCategory.mk n)) →₀ ℤ) :
    Work.Cohomology.Crux33.coords Y n
        ((SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).f n (Work.Cohomology.Crux33.mk X n c))
      = Finsupp.mapDomain (⇑(f.app (Opposite.op (SimplexCategory.mk n)))) c := by
  have hcf : ∀ a : X.obj (Opposite.op (SimplexCategory.mk n)),
      (ModuleCat.Hom.hom ((SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).f n))
          ((ModuleCat.Hom.hom (X.ιChainComplex (R := ModuleCat.of ℤ ℤ) a)) (1 : ℤ))
        = (ModuleCat.Hom.hom (Y.ιChainComplex (R := ModuleCat.of ℤ ℤ)
            ((f.app (Opposite.op (SimplexCategory.mk n))) a))) (1 : ℤ) := by
    intro a
    have hh := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ (Y.chainComplex (ModuleCat.of ℤ ℤ)).X n) =>
      (ConcreteCategory.hom g) (1 : ℤ)) (SSet.ι_chainComplexMap_f X Y f (ModuleCat.of ℤ ℤ) a)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  have h1 : ∀ (a : X.obj (Opposite.op (SimplexCategory.mk n))) (b : ℤ),
      Work.Cohomology.Crux33.coords Y n
        ((ModuleCat.Hom.hom ((SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).f n))
          ((ModuleCat.Hom.hom (X.ιChainComplex (R := ModuleCat.of ℤ ℤ) a)) b))
        = Finsupp.single ((f.app (Opposite.op (SimplexCategory.mk n))) a) b := by
    intro a b
    rw [ιChainComplex_hom_zsmul X n a b, map_zsmul, hcf a, map_zsmul,
      Work.Cohomology.Crux33.coords_ι, Finsupp.smul_single', mul_one]
  refine Finsupp.induction c ?_ ?_
  · simp
  · intro a b g ha hb hg
    simp only [map_add, Work.Cohomology.Crux33.mk_single, h1, hg, Finsupp.mapDomain_add,
      Finsupp.mapDomain_single]

/-- Naturality of `coords` under the chain map induced by a continuous map. -/
theorem coords_chainMap (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (c : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)) →₀ ℤ) :
    Work.Cohomology.Crux33.coords (TopCat.toSSet.obj Y) n
        ((Work.Cohomology.chainMap ℤ X Y f).f n
          (Work.Cohomology.Crux33.mk (TopCat.toSSet.obj X) n c))
      = Finsupp.mapDomain
          (⇑((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n)))) c :=
  coords_chainComplexMap (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) ((TopCat.toSSet).map f) n c

/-- Naturality of `simplexToCube` in the space. -/
theorem simplexToCube_naturality (n : ℕ) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (g : C(X, Y))
    (a : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk n))) :
    simplexToCube n (TopCat.of Y) (((TopCat.toSSet).map (TopCat.ofHom g)).app _ a)
      = g.comp (simplexToCube n (TopCat.of X) a) := by
  ext z
  simp only [ContinuousMap.comp_apply, simplexToCube]
  rfl

/-- `simFun` sends the coordinate push-forward of a chain to the cubical push-forward: the
generator-level form of the naturality of `Sim`. -/
theorem simFun_mapDomain (n : ℕ) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (g : C(X, Y))
    (c : (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk n)) →₀ ℤ) :
    simFun n (TopCat.of Y)
        (Finsupp.mapDomain
          (⇑((TopCat.toSSet.map (TopCat.ofHom g)).app (Opposite.op (SimplexCategory.mk n)))) c)
      = cubMap n g (simFun n (TopCat.of X) c) := by
  have hgen : ∀ (a : (TopCat.toSSet.obj (TopCat.of X)).obj
        (Opposite.op (SimplexCategory.mk n))) (b : ℤ),
      simFun n (TopCat.of Y)
          (Finsupp.mapDomain
            (⇑((TopCat.toSSet.map (TopCat.ofHom g)).app (Opposite.op (SimplexCategory.mk n))))
            (Finsupp.single a b))
        = cubMap n g (simFun n (TopCat.of X) (Finsupp.single a b)) := by
    intro a b
    rw [Finsupp.mapDomain_single, simFun_single, simFun_single, map_zsmul]
    congr 1
    rw [SimGen, SimGen, map_zsmul, cubMap_single, one_smul]
    congr 1
  refine Finsupp.induction c ?_ ?_
  · simp
  · intro a b d ha hb hd
    simp only [Finsupp.mapDomain_add, map_add, hd, hgen a b]

/-- **Naturality of `Sim`**. -/
theorem sim_naturality (n : ℕ) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (g : C(X, Y)) (u : (Work.Cohomology.singularChains ℤ (TopCat.of X)).X n) :
    Sim n (TopCat.of Y)
        ((Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom g)).f n u)
      = cubMap n g (Sim n (TopCat.of X) u) := by
  have hu : u = Work.Cohomology.Crux33.mk (TopCat.toSSet.obj (TopCat.of X)) n
      (Work.Cohomology.Crux33.coords (TopCat.toSSet.obj (TopCat.of X)) n u) :=
    (LinearMap.congr_fun
      (Work.Cohomology.Crux33.mk_comp_coords (TopCat.toSSet.obj (TopCat.of X)) n) u).symm
  have hmain : ∀ c : (TopCat.toSSet.obj (TopCat.of X)).obj
        (Opposite.op (SimplexCategory.mk n)) →₀ ℤ,
      Sim n (TopCat.of Y)
          ((Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom g)).f n
            (Work.Cohomology.Crux33.mk (TopCat.toSSet.obj (TopCat.of X)) n c))
        = cubMap n g
            (Sim n (TopCat.of X) (Work.Cohomology.Crux33.mk (TopCat.toSSet.obj (TopCat.of X)) n c)) := by
    intro c
    rw [show Sim n (TopCat.of Y)
        ((Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom g)).f n
          (Work.Cohomology.Crux33.mk (TopCat.toSSet.obj (TopCat.of X)) n c))
      = simFun n (TopCat.of Y)
          (Work.Cohomology.Crux33.coords (TopCat.toSSet.obj (TopCat.of Y)) n
            ((SSet.chainComplexMap ((TopCat.toSSet).map (TopCat.ofHom g)) (ModuleCat.of ℤ ℤ)).f n
              (Work.Cohomology.Crux33.mk (TopCat.toSSet.obj (TopCat.of X)) n c))) from rfl]
    rw [coords_chainComplexMap, Sim_apply, coords_mk, simFun_mapDomain]
  rw [hu]
  exact hmain _

end

end Work.RatHurewicz.Bridge
