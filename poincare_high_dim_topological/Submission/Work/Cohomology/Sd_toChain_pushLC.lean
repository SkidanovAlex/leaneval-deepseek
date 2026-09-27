import Mathlib
import Submission.Work.Cohomology.Mesh
import Submission.Work.Cohomology.PushChain
import Submission.Work.Cohomology.SdIter
import Submission.Work.Cohomology.Sd_comm
import Submission.Work.Cohomology.toChain_boundaryLC
import Submission.Work.Homology.SimplexShim

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- Composition of affine simplices: `affineSimplex v ∘ affineSimplex u = affineSimplex (affComp v u)`. -/
theorem affineSimplex_affComp {N k m : ℕ} (v : Fin (k + 1) → stdSimplex ℝ (Fin (N + 1)))
    (u : Fin (m + 1) → stdSimplex ℝ (Fin (k + 1))) (z : stdSimplex ℝ (Fin (m + 1))) :
    affineSimplex v (affineSimplex u z) = affineSimplex (affComp v u) z := by
  ext i
  simp only [affineSimplex_apply, affComp, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The continuous map underlying `linSimplex v` is `affineSimplex v`. -/
theorem sdMap_linSimplex {n : ℕ} (v : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1))) :
    sdMap n (linSimplex v) = TopCat.ofHom (affineSimplex v) := by
  rw [show sdMap n (linSimplex v)
      = TopCat.ofHom (Work.Homology.toSSetObjEquiv' (Delta n) (Opposite.op ⦋n⦌) (linSimplex v))
      from rfl]
  rw [toSSetObjEquiv_linSimplex]

/-- Pushing the simplex `linSimplex u` forward along the affine simplex with vertices `v` gives the
simplex with vertices `affComp v u`. -/
theorem toSSet_map_sdMap_linSimplex {n : ℕ} (v u : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1))) :
    (TopCat.toSSet.map (sdMap n (linSimplex v))).app (Opposite.op ⦋n⦌) (linSimplex u)
      = linSimplex (affComp v u) := by
  refine (Work.Homology.toSSetObjEquiv' (Delta n) (Opposite.op ⦋n⦌)).injective ?_
  apply ContinuousMap.ext
  intro z
  rw [toSSetObjEquiv_map_apply, toSSetObjEquiv_linSimplex (v := u), sdMap_linSimplex,
    toSSetObjEquiv_linSimplex (v := affComp v u)]
  exact affineSimplex_affComp v u z

/-- Naturality of `toChain` for the chain-level pushforward along an affine map of `Δⁿ`.  If a
continuous map `f : Δⁿ ⟶ Δⁿ` sends the affine simplex with vertices `u` to the one with vertices
`g u`, then pushing `toChain c` forward along `f` is `toChain` of the chain with vertex families
replaced by `g`. -/
theorem chainComplexMap_toChain {n k : ℕ} (f : Delta n ⟶ Delta n)
    (g : (Fin (k + 1) → stdSimplex ℝ (Fin (n + 1))) →
      (Fin (k + 1) → stdSimplex ℝ (Fin (n + 1))))
    (hg : ∀ u, (TopCat.toSSet.map f).app (Opposite.op ⦋k⦌) (linSimplex u) = linSimplex (g u))
    (c : LinChain n k) :
    (ModuleCat.Hom.hom ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)).f k))
        (toChain n k c)
      = toChain n k (Finsupp.mapDomain g c) := by
  refine Finsupp.induction_linear c ?_ ?_ ?_
  · simp only [Finsupp.mapDomain_zero, LinearMap.map_zero]
  · intro x y ihx ihy
    simp only [Finsupp.mapDomain_add, LinearMap.map_add, ihx, ihy]
  · intro a b
    rw [Finsupp.mapDomain_single, toChain_apply_single n k a b, toChain_apply_single n k (g a) b,
      map_zsmul, chainComplexMap_ι_apply, hg a]

/-- `Sd` on the affine simplex with vertices `v` is the pushforward of `sdLC n` along `v`. -/
theorem Sd_gen_linSimplex_eq (n : ℕ) (v : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1))) :
    Sd (Delta n) n (gen (Delta n) n (linSimplex v))
      = toChain n n (Finsupp.mapDomain (affComp v) (sdLC n)) := by
  rw [Sd_gen, sdElem_eq, show sdChain n = toChain n n (sdLC n) from rfl]
  exact chainComplexMap_toChain (f := sdMap n (linSimplex v)) (g := affComp v)
    (fun u => toSSet_map_sdMap_linSimplex v u) (sdLC n)

/-- Pushing a single vertex family with coefficient forward along itself. -/
theorem pushLC_single_apply (n : ℕ) (v : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1)))
    (b : ℤ) (c : LinChain n n) :
    pushLC n n (Finsupp.single v b) c = b • Finsupp.mapDomain (affComp v) c := by
  have h : pushLC n n (Finsupp.single v b)
      = b • (Finsupp.lmapDomain ℤ ℤ (fun u => affComp v u)) := by
    simp only [pushLC, Finsupp.linearCombination_single]
  rw [h, LinearMap.smul_apply, Finsupp.lmapDomain_apply]

theorem Sd_toChain_pushLC (n : ℕ) (C : LinChain n n) :
    Sd (Delta n) n (toChain n n C) = toChain n n (pushLC n n C (sdLC n)) := by
  refine Finsupp.induction_linear C ?_ ?_ ?_
  · rw [LinearMap.map_zero (pushLC n n), LinearMap.zero_apply, LinearMap.map_zero (toChain n n),
      LinearMap.map_zero (Sd (Delta n) n)]
  · intro x y ihx ihy
    rw [LinearMap.map_add (toChain n n) x y, LinearMap.map_add (Sd (Delta n) n),
      LinearMap.map_add (pushLC n n) x y, LinearMap.add_apply, LinearMap.map_add (toChain n n),
      ihx, ihy]
  · intro a b
    rw [toChain_apply_single n n a b, map_zsmul, pushLC_single_apply]
    rw [map_zsmul]
    congr 1
    exact Sd_gen_linSimplex_eq n a

end

end Work.Cohomology
