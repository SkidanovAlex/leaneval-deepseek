import Mathlib

/-!
# Auxiliary maps for "homology commutes with coproducts"

This file collects the canonical comparison maps used to prove that, for a family of chain
complexes `K i` over `ModuleCat R`, homology commutes with the coproduct, and more precisely that
the canonical map

`∐ i, (K i).homology m ⟶ (∐ i, K i).homology m`

is an isomorphism when `R` is a commutative ring.

* `Work.Serre.sigmaKernelMap` -- the comparison `∐ i, kernel (f i) ⟶ kernel (∐ i, f i)` for a
  family of morphisms `f i : M i ⟶ N i` in an arbitrary category with kernels and coproducts;
* `Work.Serre.sigmaKernelMap_ι`, `Work.Serre.sigmaKernelMap_comp_ι` -- its computation rules;
* `Work.Serre.sigmaDegreeMap` -- the comparison `∐ i, (K i).X n ⟶ (∐ i, K i).X n` in degree `n`
  for a family of chain complexes over `ModuleCat R`;
* `Work.Serre.sigmaDegreeMap_ι`, `Work.Serre.sigmaDegreeMap_d` -- its computation rules.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

universe u v

/-- The canonical comparison morphism `∐ i, kernel (f i) ⟶ kernel (∐ i, f i)`: it is induced, by
the universal property of the coproduct, from the maps `kernel (f i) ⟶ ∐ i, M i` obtained from
the inclusions of the kernels. -/
def sigmaKernelMap {ι : Type u} {C : Type v} [Category.{u,v} C] [HasZeroMorphisms C]
    [HasCoproductsOfShape ι C] [HasKernels C] {M N : ι → C} (f : ∀ i, M i ⟶ N i) :
    (∐ fun i => kernel (f i)) ⟶ kernel (Limits.Sigma.map f) :=
  Limits.Sigma.desc (fun i =>
    kernel.lift (Limits.Sigma.map f) (kernel.ι (f i) ≫ Limits.Sigma.ι M i) (by
      rw [Category.assoc, Limits.Sigma.ι_map]; simp))

/-- The `i`-th component of `sigmaKernelMap`. -/
theorem sigmaKernelMap_ι {ι : Type u} {C : Type v} [Category.{u,v} C] [HasZeroMorphisms C]
    [HasCoproductsOfShape ι C] [HasKernels C] {M N : ι → C} (f : ∀ i, M i ⟶ N i) (i : ι) :
    Limits.Sigma.ι (fun i => kernel (f i)) i ≫ sigmaKernelMap f
      = kernel.lift (Limits.Sigma.map f) (kernel.ι (f i) ≫ Limits.Sigma.ι M i) (by
        rw [Category.assoc, Limits.Sigma.ι_map]; simp) :=
  Limits.Sigma.ι_desc _ _

/-- The defining property of `sigmaKernelMap`: it is the coproduct of the inclusions of the
kernels. -/
theorem sigmaKernelMap_comp_ι {ι : Type u} {C : Type v} [Category.{u,v} C] [HasZeroMorphisms C]
    [HasCoproductsOfShape ι C] [HasKernels C] {M N : ι → C} (f : ∀ i, M i ⟶ N i) :
    sigmaKernelMap f ≫ kernel.ι (Limits.Sigma.map f)
      = Limits.Sigma.map (fun i => kernel.ι (f i)) := by
  apply Limits.Sigma.hom_ext
  intro i
  rw [← Category.assoc, sigmaKernelMap_ι, kernel.lift_ι, Limits.Sigma.ι_map]

/-- The canonical comparison `∐ i, (K i).X n ⟶ (∐ i, K i).X n` in degree `n`, for a family of
chain complexes over `ModuleCat R`. -/
def sigmaDegreeMap (R : Type v) [Ring R] {ι : Type u}
    (K : ι → ChainComplex (ModuleCat R) ℕ) (n : ℕ) :
    (∐ fun i => (K i).X n) ⟶ (∐ K).X n :=
  Limits.Sigma.desc (fun i => (Limits.Sigma.ι K i).f n)

/-- The `i`-th component of `sigmaDegreeMap`. -/
theorem sigmaDegreeMap_ι (R : Type v) [Ring R] {ι : Type u}
    (K : ι → ChainComplex (ModuleCat R) ℕ) (n : ℕ) (i : ι) :
    Limits.Sigma.ι (fun i => (K i).X n) i ≫ sigmaDegreeMap R K n = (Limits.Sigma.ι K i).f n :=
  Limits.Sigma.ι_desc _ _

/-- The compatibility of `sigmaDegreeMap` with the differentials. -/
theorem sigmaDegreeMap_d (R : Type v) [Ring R] {ι : Type u}
    (K : ι → ChainComplex (ModuleCat R) ℕ) (n m : ℕ) :
    sigmaDegreeMap R K n ≫ (∐ K).d n m
      = Limits.Sigma.map (fun i => (K i).d n m) ≫ sigmaDegreeMap R K m := by
  apply Limits.Sigma.hom_ext
  intro i
  simp only [← Category.assoc]
  rw [sigmaDegreeMap_ι, HomologicalComplex.Hom.comm, Limits.Sigma.ι_map, Category.assoc,
    sigmaDegreeMap_ι]

end

end Work.Serre
