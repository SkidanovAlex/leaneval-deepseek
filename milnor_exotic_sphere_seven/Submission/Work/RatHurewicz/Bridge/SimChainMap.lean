import Mathlib
import Submission.Work.RatHurewicz.Bridge.Defs
import Submission.Work.RatHurewicz.Bridge.H_faces
import Submission.Work.RatHurewicz.Bridge.SimLemmas

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false

/-!
# The comparison `σ ↦ σ ∘ H n` is a chain map modulo degenerate cubes

* `cofaceCube`, `faceCube'` : the cubes occurring in the two sides of the identity;
* `sim_chainMap_cube` : the cube-level computation: for a singular simplex `s : Δⁿ⁺¹ → X`,
  `∂((-1)ⁿ⁺¹·(s ∘ H (n+1))) - ∑ᵢ (-1)ⁱ·(s ∘ cofaceᵢ ∘ H n) ∈ Deg n X`.
-/

open scoped unitInterval Topology Simplicial
open CategoryTheory AlgebraicTopology
open Work.Stems.Cubical

namespace Work.RatHurewicz.Bridge

noncomputable section

/-- The cube `s ∘ cofaceᵢ ∘ H n` attached to the `i`-th coface of a singular simplex. -/
def cofaceCube (n : ℕ) {X : Type} [TopologicalSpace X]
    (s : C(stdSimplex ℝ (Fin (n + 2)), X)) (i : Fin (n + 2)) : C(IC n, X) :=
  s.comp ((coface n i).comp (H n))

/-- The cube `s ∘ H (n+1) ∘ faceCM k b` attached to the `k`-th face of the cube `Iⁿ⁺¹`. -/
def faceCube' (n : ℕ) {X : Type} [TopologicalSpace X]
    (s : C(stdSimplex ℝ (Fin (n + 2)), X)) (k : Fin (n + 1)) (b : unitInterval) : C(IC n, X) :=
  s.comp ((H (n + 1)).comp (faceCM k b))

/-- The face `t_k = 1` is the `k`-th coface. -/
theorem faceCube'_one (n : ℕ) {X : Type} [TopologicalSpace X]
    (s : C(stdSimplex ℝ (Fin (n + 2)), X)) (k : Fin (n + 1)) :
    faceCube' n s k 1 = cofaceCube n s (Fin.castSucc k) := by
  rw [faceCube', cofaceCube, H_face_one n k]

/-- The face `t_m = 0` is the last coface. -/
theorem faceCube'_last_zero (n : ℕ) {X : Type} [TopologicalSpace X]
    (s : C(stdSimplex ℝ (Fin (n + 2)), X)) :
    faceCube' n s (Fin.last n) 0 = cofaceCube n s (Fin.last (n + 1)) := by
  rw [faceCube', cofaceCube, H_face_last_zero n]

/-- The other faces `t_k = 0` are degenerate. -/
theorem faceCube'_zero_mem_Deg (n : ℕ) {X : Type} [TopologicalSpace X]
    (s : C(stdSimplex ℝ (Fin (n + 2)), X)) (k : Fin n) :
    Finsupp.single (faceCube' n s (Fin.castSucc k) 0) (1 : ℤ) ∈ Deg n X := by
  rw [faceCube']
  have h := Deg_cubMap s (H_face_zero_mem_Deg n (Fin.castSucc k) k.isLt)
  rwa [cubMap_single, one_smul] at h

/-- `(-1)ⁿ⁺¹ = -(-1)ⁿ`. -/
theorem negOnePow_succ (n : ℕ) : (-1 : ℤ) ^ (n + 1) = -((-1 : ℤ) ^ n) := by
  rw [pow_succ]; ring

/-- `(-1)ⁿ·(-1)ⁿ = 1`. -/
theorem negOnePow_mul_self (n : ℕ) : (-1 : ℤ) ^ n * (-1) ^ n = 1 := by
  rw [← pow_add, show n + n = 2 * n by ring]
  exact Even.neg_one_pow ⟨n, by ring⟩

/-- **The cube-level chain identity.** -/
theorem sim_chainMap_cube (n : ℕ) (X : TopCat)
    (s : C(stdSimplex ℝ (Fin (n + 2)), X)) :
    cubD n X ((-1 : ℤ) ^ (n + 1) • Finsupp.single (s.comp (H (n + 1))) (1 : ℤ))
      - (-1 : ℤ) ^ (n : ℕ) • (∑ i : Fin (n + 2),
          (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (cofaceCube n s i) (1 : ℤ))
      ∈ Deg n X := by
  -- the cubical boundary of the single cube, in terms of the face cubes
  have hsingle : cubD n X (Finsupp.single (s.comp (H (n + 1))) (1 : ℤ))
      = ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) •
          (Finsupp.single (faceCube' n s k 0) (1 : ℤ)
            - Finsupp.single (faceCube' n s k 1) (1 : ℤ)) := by
    rw [cubD_single]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [faceCube', faceCube']
    rfl
  -- split the coface sum (over `Fin (n+2)`) at its last term
  have hsum : (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        Finsupp.single (cofaceCube n s i) (1 : ℤ))
      = (∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) •
          Finsupp.single (cofaceCube n s (Fin.castSucc k)) (1 : ℤ))
        + (-1 : ℤ) ^ (n + 1) • Finsupp.single (cofaceCube n s (Fin.last (n + 1))) (1 : ℤ) := by
    rw [Fin.sum_univ_castSucc]
    congr 1
  -- split the face sum (over `Fin (n+1)`) at its last term
  have hsum2 : (∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) •
        (Finsupp.single (faceCube' n s k 0) (1 : ℤ)
          - Finsupp.single (faceCube' n s k 1) (1 : ℤ)))
      = (∑ k : Fin n, (-1 : ℤ) ^ (k : ℕ) •
            (Finsupp.single (faceCube' n s (Fin.castSucc k) 0) (1 : ℤ)
              - Finsupp.single (faceCube' n s (Fin.castSucc k) 1) (1 : ℤ)))
        + (-1 : ℤ) ^ (n : ℕ) •
            (Finsupp.single (faceCube' n s (Fin.last n) 0) (1 : ℤ)
              - Finsupp.single (faceCube' n s (Fin.last n) 1) (1 : ℤ)) := by
    rw [Fin.sum_univ_castSucc]
    congr 1
  -- split the coface sum (over `Fin (n+1)`) at its last term
  have hsum3 : (∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) •
        Finsupp.single (cofaceCube n s (Fin.castSucc k)) (1 : ℤ))
      = (∑ k : Fin n, (-1 : ℤ) ^ ((Fin.castSucc k : Fin (n + 1)) : ℕ) •
          Finsupp.single (cofaceCube n s (Fin.castSucc (Fin.castSucc k))) (1 : ℤ))
        + (-1 : ℤ) ^ ((Fin.last n : Fin (n + 1)) : ℕ) •
          Finsupp.single (cofaceCube n s (Fin.castSucc (Fin.last n))) (1 : ℤ) := by
    rw [Fin.sum_univ_castSucc]
  -- the identification with the final answer
  have hmain : cubD n X ((-1 : ℤ) ^ (n + 1) • Finsupp.single (s.comp (H (n + 1))) (1 : ℤ))
      - (-1 : ℤ) ^ (n : ℕ) • (∑ i : Fin (n + 2),
          (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (cofaceCube n s i) (1 : ℤ))
      = (-1 : ℤ) ^ (n + 1) •
          (∑ k : Fin n, (-1 : ℤ) ^ (k : ℕ) •
            Finsupp.single (faceCube' n s (Fin.castSucc k) 0) (1 : ℤ)) := by
    rw [map_smul, hsingle, hsum, hsum2, hsum3]
    simp only [faceCube'_one, faceCube'_last_zero, Finset.smul_sum, smul_add, smul_sub,
      Finset.sum_sub_distrib]
    rw [negOnePow_succ n]
    simp only [negOnePow_mul_self, Fin.val_last, Fin.val_castSucc, ← Finset.smul_sum]
    module
  rw [hmain]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (faceCube'_zero_mem_Deg n s k))

/-- The application of a finite sum of linear maps. -/
theorem sum_linearMap_apply {N R : Type} [Semiring R] [AddCommMonoid N] [Module R N] {ι : Type}
    (s : Finset ι) (g : ι → (R →ₗ[R] N)) (x : R) :
    (∑ i ∈ s, g i) x = ∑ i ∈ s, g i x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, LinearMap.add_apply, ih]

/-- The application of a finite sum of linear maps, unbounded form. -/
theorem sum_linearMap_apply' {N R : Type} [Semiring R] [AddCommMonoid N] [Module R N]
    {ι : Type} [Fintype ι] (g : ι → (R →ₗ[R] N)) (x : R) :
    (∑ i, g i) x = ∑ i, g i x :=
  sum_linearMap_apply Finset.univ g x

/-- The boundary of the generator of a simplex. -/
theorem d_ιChainComplex_one (X : SSet) (n : ℕ)
    (a : X.obj (Opposite.op (SimplexCategory.mk (n + 1)))) :
    (X.chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n
        ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) a).hom (1 : ℤ))
      = ∑ i : Fin (n + 2),
          (-1 : ℤ) ^ (i : ℕ) •
            (X.ιChainComplex (R := ModuleCat.of ℤ ℤ) ((X.δ i) a)).hom (1 : ℤ) := by
  have hh := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ (X.chainComplex (ModuleCat.of ℤ ℤ)).X n) =>
    (ConcreteCategory.hom g) (1 : ℤ)) (SSet.ιChainComplex_d X (ModuleCat.of ℤ ℤ) a)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum, ModuleCat.hom_zsmul] at hh
  rw [sum_linearMap_apply'] at hh
  exact hh

/-- The value of `Sim` on the chain carried by a simplex. -/
theorem Sim_ιChainComplex_one (n : ℕ) (X : TopCat)
    (a : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    Sim n X (simpChain n ((X.toSSetObjEquivOld (Opposite.op (SimplexCategory.mk n))) a))
      = SimGen n X a := by
  rw [Sim_simpChain, SimGen, simplexToCube]

/-- **The chain-map property, on a single singular simplex.** -/
theorem sim_chainMap_gen (n : ℕ) (X : TopCat)
    (s : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk (n + 1)))) :
    cubD n X (SimGen (n + 1) X s)
      - ∑ i : Fin (n + 2),
          (-1 : ℤ) ^ (i : ℕ) • SimGen n X ((TopCat.toSSet.obj X).δ i s)
      ∈ Deg n X := by
  set s' := (X.toSSetObjEquivOld (Opposite.op (SimplexCategory.mk (n + 1)))) s with hs'
  have hface : ∀ i : Fin (n + 2),
      ((X.toSSetObjEquivOld (Opposite.op (SimplexCategory.mk n)))
          ((TopCat.toSSet.obj X).δ i s)) = s'.comp (coface n i) := by
    intro i
    ext z
    rw [ContinuousMap.comp_apply, TopCat.toSSetObjEquivOld_δ_apply]
    rfl
  have hcube := sim_chainMap_cube n X s'
  have hsum : (∑ i : Fin (n + 2),
        (-1 : ℤ) ^ (i : ℕ) • SimGen n X ((TopCat.toSSet.obj X).δ i s))
      = (-1 : ℤ) ^ n • (∑ i : Fin (n + 2),
          (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (cofaceCube n s' i) (1 : ℤ)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SimGen, simplexToCube, hface i, cofaceCube]
    rw [smul_smul, smul_smul, mul_comm, ContinuousMap.comp_assoc]
  rw [show SimGen (n + 1) X s
      = (-1 : ℤ) ^ (n + 1) • Finsupp.single (s'.comp (H (n + 1))) (1 : ℤ) from rfl, hsum]
  exact hcube

/-- The boundary of the chain carried by a simplex, in the `simpChain` presentation. -/
theorem d_simpChain (n : ℕ) (X : TopCat)
    (a : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk (n + 1)))) :
    (Work.Cohomology.singularChains ℤ X).d (n + 1) n
        (simpChain (n + 1) ((X.toSSetObjEquivOld (Opposite.op (SimplexCategory.mk (n + 1)))) a))
      = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          simpChain n ((X.toSSetObjEquivOld (Opposite.op (SimplexCategory.mk n)))
            (((TopCat.toSSet.obj X).δ i) a)) := by
  have e1 : simpChain (n + 1) ((X.toSSetObjEquivOld (Opposite.op (SimplexCategory.mk (n + 1)))) a)
      = ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) a).hom (1 : ℤ) := by
    rw [simpChain, simplexOf, Equiv.symm_apply_apply, Work.Cohomology.Crux33.mk_single]
  have e2 : ∀ i : Fin (n + 2),
      simpChain n ((X.toSSetObjEquivOld (Opposite.op (SimplexCategory.mk n)))
          (((TopCat.toSSet.obj X).δ i) a))
        = ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
            (((TopCat.toSSet.obj X).δ i) a)).hom (1 : ℤ) := by
    intro i
    rw [simpChain, simplexOf, Equiv.symm_apply_apply, Work.Cohomology.Crux33.mk_single]
  rw [e1]
  change ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n
      (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) a).hom (1 : ℤ))
      = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          simpChain n ((X.toSSetObjEquivOld (Opposite.op (SimplexCategory.mk n)))
            (((TopCat.toSSet.obj X).δ i) a))
  rw [d_ιChainComplex_one]
  exact Finset.sum_congr rfl fun i _ =>
    congrArg (fun z => (-1 : ℤ) ^ (i : ℕ) • z) (e2 i).symm

/-- **The chain-map property of `Sim`.** -/
theorem sim_chainMap (n : ℕ) (X : TopCat)
    (u : (Work.Cohomology.singularChains ℤ X).X (n + 1)) :
    cubD n X (Sim (n + 1) X u) - Sim n X ((Work.Cohomology.singularChains ℤ X).d (n + 1) n u)
      ∈ Deg n X := by
  let Φ : (Work.Cohomology.singularChains ℤ X).X (n + 1) →ₗ[ℤ] Cub n X :=
    (cubD n X).comp (Sim (n + 1) X)
      - (Sim n X).comp (((Work.Cohomology.singularChains ℤ X).d (n + 1) n).hom)
  have hΦ : Φ u = cubD n X (Sim (n + 1) X u)
      - Sim n X ((Work.Cohomology.singularChains ℤ X).d (n + 1) n u) := rfl
  rw [← hΦ]
  -- the generator case
  have hgen : ∀ a : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk (n + 1))),
      Φ (simpChain (n + 1) ((X.toSSetObjEquivOld (Opposite.op (SimplexCategory.mk (n + 1)))) a))
        ∈ Deg n X := by
    intro a
    have h1 : Sim (n + 1) X
        (simpChain (n + 1) ((X.toSSetObjEquivOld (Opposite.op (SimplexCategory.mk (n + 1)))) a))
        = SimGen (n + 1) X a := Sim_ιChainComplex_one (n + 1) X a
    have h2 : Sim n X ((Work.Cohomology.singularChains ℤ X).d (n + 1) n
        (simpChain (n + 1) ((X.toSSetObjEquivOld (Opposite.op (SimplexCategory.mk (n + 1)))) a)))
        = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • SimGen n X ((TopCat.toSSet.obj X).δ i a) := by
      rw [d_simpChain, map_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [map_zsmul, Sim_ιChainComplex_one n X (((TopCat.toSSet.obj X).δ i) a)]
    simp only [Φ, LinearMap.sub_apply, LinearMap.comp_apply]
    rw [h1, h2]
    exact sim_chainMap_gen n X a
  -- linearity in the coordinates
  let Ψ : ((TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk (n + 1))) →₀ ℤ) →ₗ[ℤ]
      Cub n X :=
    Φ.comp (Work.Cohomology.Crux33.mk (TopCat.toSSet.obj X) (n + 1))
  have hcoord : ∀ c : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk (n + 1))) →₀ ℤ,
      Ψ c ∈ Deg n X := by
    intro c
    refine Finsupp.induction_linear c ?_ ?_ ?_
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro f g hf hg
      rw [map_add]
      exact add_mem hf hg
    · intro a b
      have hs : (Finsupp.single a b :
          (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk (n + 1))) →₀ ℤ)
          = b • Finsupp.single a 1 :=
        (Finsupp.smul_single_one a b).symm
      have h2 : Ψ (Finsupp.single a 1)
          = Φ (simpChain (n + 1)
              ((X.toSSetObjEquivOld (Opposite.op (SimplexCategory.mk (n + 1)))) a)) := by
        show Φ ((Work.Cohomology.Crux33.mk (TopCat.toSSet.obj X) (n + 1))
            (Finsupp.single a 1)) = _
        rw [simpChain, simplexOf, Equiv.symm_apply_apply]
      rw [hs, map_smul, h2]
      exact Submodule.smul_mem _ _ (hgen a)
  have hu : u = Work.Cohomology.Crux33.mk (TopCat.toSSet.obj X) (n + 1)
      (Work.Cohomology.Crux33.coords (TopCat.toSSet.obj X) (n + 1) u) :=
    (LinearMap.congr_fun
      (Work.Cohomology.Crux33.mk_comp_coords (TopCat.toSSet.obj X) (n + 1)) u).symm
  rw [hu]
  exact hcoord _
