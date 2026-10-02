import Mathlib
import Submission.Work.RatHurewicz.CubicalDefs
import Submission.Work.RatHurewicz.cubicalBridgeDefs
import Submission.Work.Stems.HurewiczNeutral
import Submission.Work.Cohomology.Crux33.ezBridge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The simplicial/cubical bridge: vocabulary

This file sets up the vocabulary for `Work.RatHurewicz.cubicalBridgeDeg`:

* `Work.RatHurewicz.Bridge.proj m i` — the projection `I^(m+1) → I^m` dropping the coordinate `i`
  of the source cube (its image misses `i`);
* `Work.RatHurewicz.Bridge.coface n i` — the coface `Δⁿ → Δⁿ⁺¹` inserting a zero in position `i`
  (the map induced on `stdSimplex` by the `i`-th coface of `SimplexCategory`, matching the face
  maps `SSet.δ i` of the singular simplicial set);
* `Work.RatHurewicz.Bridge.simplexToCube` — the singular `n`-simplex turned into a cube by
  precomposition with the cumulative-coordinate map `Work.RatHurewicz.H n`;
* `Work.RatHurewicz.Bridge.Sim` — the induced `ℤ`-linear map from the singular chains of `X` to the
  cubical chains, `σ ↦ (-1)^n • single (σ ∘ H n) 1`;
* `Work.RatHurewicz.Bridge.cubMap` — the push-forward of cubical chains along a continuous map.

The chain-level facts about `Sim` (that it is a chain map modulo degenerate cubical chains) and the
existence of the collapse simplex are stated separately.
-/

open scoped unitInterval Topology Simplicial
open CategoryTheory AlgebraicTopology

namespace Work.RatHurewicz.Bridge

open Work.Stems.Cubical

noncomputable section

/-- The projection `I^(m+1) → I^m` dropping the coordinate `i` of the source. -/
def proj (m : ℕ) (i : Fin (m + 1)) : C(IC (m + 1), IC m) where
  toFun t := fun j => t (Fin.succAbove i j)
  continuous_toFun := by
    apply continuous_pi
    intro j
    exact continuous_apply (Fin.succAbove i j)

@[simp]
theorem proj_apply (m : ℕ) (i : Fin (m + 1)) (t : IC (m + 1)) (j : Fin m) :
    proj m i t j = t (Fin.succAbove i j) := rfl

/-- The coface `Δⁿ → Δⁿ⁺¹` inserting a zero in position `i`. -/
def coface (n : ℕ) (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  ⟨stdSimplex.map (Fin.succAbove i), stdSimplex.continuous_map _⟩

@[simp]
theorem coface_apply (n : ℕ) (i : Fin (n + 2)) (z : stdSimplex ℝ (Fin (n + 1))) :
    coface n i z = stdSimplex.map (Fin.succAbove i) z := rfl

/-- The singular `n`-simplex `σ` of `X` turned into a cube `I^n → X` by precomposition with the
cumulative-coordinate map `H n`. -/
def simplexToCube (n : ℕ) (X : TopCat) (simplex : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌)) : C(IC n, X) :=
  (X.toSSetObjEquivOld (Opposite.op ⦋n⦌) simplex).comp (H n)

/-- The cubical chain attached to a single singular `n`-simplex: `(-1)^n` times the cube
`σ ∘ H n`. -/
def SimGen (n : ℕ) (X : TopCat) (simplex : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌)) : Cub n X :=
  (-1 : ℤ) ^ n • Finsupp.single (simplexToCube n X simplex) (1 : ℤ)

/-- The `ℤ`-linear map on chains with coordinates: `σ ↦ (-1)^n • single (σ ∘ H n) 1`. -/
def simFun (n : ℕ) (X : TopCat) :
    ((TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌) →₀ ℤ) →ₗ[ℤ] Cub n X :=
  Finsupp.linearCombination ℤ fun simplex => (-1 : ℤ) ^ n •
    Finsupp.single (simplexToCube n X simplex) 1

@[simp]
theorem simFun_single (n : ℕ) (X : TopCat) (simplex : (TopCat.toSSet.obj X).obj (Opposite.op ⦋n⦌))
    (a : ℤ) :
    simFun n X (Finsupp.single simplex a) = a • SimGen n X simplex := by
  rw [simFun, Finsupp.linearCombination_single, SimGen]

/-- The comparison map from the singular `n`-chains of `X` to the cubical `n`-chains:
a singular simplex `σ` is sent to `(-1)^n` times the cube `σ ∘ H n`. -/
def Sim (n : ℕ) (X : TopCat) :
    (Work.Cohomology.singularChains ℤ X).X n →ₗ[ℤ] Cub n X :=
  (simFun n X).comp (Work.Cohomology.Crux33.coords (TopCat.toSSet.obj X) n)

/-- The push-forward of cubical chains along a continuous map. -/
def cubMap (n : ℕ) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    Cub n X →ₗ[ℤ] Cub n Y :=
  Finsupp.linearCombination ℤ fun c => Finsupp.single (f.comp c) (1 : ℤ)

@[simp]
theorem cubMap_single (n : ℕ) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (c : C(IC n, X)) (a : ℤ) :
    cubMap n f (Finsupp.single c a) = a • Finsupp.single (f.comp c) (1 : ℤ) := by
  rw [cubMap, Finsupp.linearCombination_single]


/-- The singular `n`-simplex of `X` attached to a continuous map `Δⁿ → X`. -/
def simplexOf (n : ℕ) {X : Type} [TopologicalSpace X] (c : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op ⦋n⦌) :=
  ((TopCat.of X).toSSetObjEquivOld (Opposite.op ⦋n⦌)).symm c

@[simp]
theorem toSSetObjEquiv_simplexOf (n : ℕ) {X : Type} [TopologicalSpace X]
    (c : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    ((TopCat.of X).toSSetObjEquivOld (Opposite.op ⦋n⦌)) (simplexOf n c) = c :=
  Equiv.apply_symm_apply _ _

@[simp]
theorem simplexToCube_simplexOf (n : ℕ) {X : Type} [TopologicalSpace X]
    (c : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    simplexToCube n (TopCat.of X) (simplexOf n c) = c.comp (H n) := by
  simp [simplexToCube, simplexOf]

/-- The singular `n`-chain carried by a single simplex `Δⁿ → X`. -/
def simpChain (n : ℕ) {X : Type} [TopologicalSpace X]
    (c : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    (Work.Cohomology.singularChains ℤ (TopCat.of X)).X n :=
  Work.Cohomology.Crux33.mk (TopCat.toSSet.obj (TopCat.of X)) n
    (Finsupp.single (simplexOf n c) 1)

theorem coords_simpChain (n : ℕ) {X : Type} [TopologicalSpace X]
    (c : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    Work.Cohomology.Crux33.coords (TopCat.toSSet.obj (TopCat.of X)) n (simpChain n c)
      = Finsupp.single (simplexOf n c) 1 := by
  rw [simpChain, Work.Cohomology.Crux33.mk_single, Work.Cohomology.Crux33.coords_ι]

/-- The value of `Sim` on the chain carried by a single simplex. -/
theorem Sim_apply (n : ℕ) (X : TopCat) (u : (Work.Cohomology.singularChains ℤ X).X n) :
    Sim n X u = simFun n X (Work.Cohomology.Crux33.coords (TopCat.toSSet.obj X) n u) := rfl

@[simp]
theorem Sim_simpChain (n : ℕ) {X : Type} [TopologicalSpace X]
    (c : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    Sim n (TopCat.of X) (simpChain n c) = (-1 : ℤ) ^ n • Finsupp.single (c.comp (H n)) 1 := by
  rw [Sim_apply, coords_simpChain, simFun_single, SimGen, simplexToCube_simplexOf, one_smul]

/-- A cube which is independent of one coordinate lies in `Deg`. -/
theorem Deg_of_indep {n : ℕ} {Y : Type} [TopologicalSpace Y] (i : Fin n) {g : C(IC n, Y)}
    (hg : ∀ t t' : IC n, (∀ j : Fin n, j ≠ i → t j = t' j) → g t = g t') :
    Finsupp.single g (1 : ℤ) ∈ Deg n Y :=
  Submodule.mem_iSup_of_mem i (Submodule.subset_span ⟨g, hg, rfl⟩)

/-- A cube which factors through a projection of the cube lies in `Deg`. -/
theorem Deg_comp_proj {m : ℕ} {Y : Type} [TopologicalSpace Y] (i : Fin (m + 1))
    (g : C(IC m, Y)) : Finsupp.single (g.comp (proj m i)) (1 : ℤ) ∈ Deg (m + 1) Y := by
  refine Deg_of_indep i ?_
  intro t t' ht
  simp only [ContinuousMap.comp_apply]
  congr 1
  funext j
  exact ht (Fin.succAbove i j) (Fin.succAbove_ne i j)

/-- The constant cube lies in `Deg` in positive dimensions. -/
theorem Deg_const {m : ℕ} {Y : Type} [TopologicalSpace Y] (y : Y) :
    Finsupp.single (ContinuousMap.const (IC (m + 1)) y) (1 : ℤ) ∈ Deg (m + 1) Y := by
  have h : ContinuousMap.const (IC (m + 1)) y
      = (ContinuousMap.const (IC m) y).comp (proj m 0) := by
    ext t; rfl
  rw [h]
  exact Deg_comp_proj 0 _

/-- The push-forward of a degenerate chain is degenerate. -/
theorem Deg_cubMap {n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    {c : Cub n X} (hc : c ∈ Deg n X) : cubMap n f c ∈ Deg n Y := by
  rcases n with _ | m
  · have h : Deg 0 X = ⊥ := by rw [Deg]; exact iSup_of_empty _
    rw [h, Submodule.mem_bot] at hc
    have h' : Deg 0 Y = ⊥ := by rw [Deg]; exact iSup_of_empty _
    rw [hc, map_zero, h', Submodule.mem_bot]
  · have hle : Submodule.map (cubMap (m + 1) f) (Deg (m + 1) X) ≤ Deg (m + 1) Y := by
      simp only [Deg]
      rw [Submodule.map_iSup]
      refine iSup_le fun i => ?_
      rw [Submodule.map_span]
      refine Submodule.span_le.mpr ?_
      rintro y ⟨x, hx, rfl⟩
      obtain ⟨g, hg, rfl⟩ := hx
      rw [cubMap_single, one_smul]
      exact Deg_of_indep i fun t t' ht => by
        simp only [ContinuousMap.comp_apply]
        rw [hg t t' ht]
    exact hle ⟨c, hc, rfl⟩

end

end Work.RatHurewicz.Bridge
