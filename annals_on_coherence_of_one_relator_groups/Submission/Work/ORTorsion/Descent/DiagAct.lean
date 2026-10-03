/-
# The diagonal action of `K[H]` on `V ⊗[K] M` for `↥(D H)`-modules `M`

This file packages, for a `TorsionData L` and a subgroup `H ≤ G`, the "diagonal" action of
`K[H]` on `V ⊗[K] M`, where `V` is a `K[G]`-module and `M` is a module over the division closure
`↥(L.D H)`:

* if `M = ↥(L.D H)` this is the action used in the hypothesis of
  `Work.ORTorsion.Descent.injective_of_injective_DH`;
* if `M = ↥(L.D ⊤)` this is the action of `K[H] ⊆ K[G]` induced by the diagonal action on
  `V ⊗[K] ↥(L.D ⊤)`;
* it is functorial: for an `↥(L.D H)`-linear map `f`, the map `id ⊗ f` is `K[H]`-linear.

The main point is `diagAct_map`, which is the "additive functor" property of `V ⊗[K] -` used in
the descent argument.
-/
import Mathlib
import Submission.Work.ORTorsion.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped TensorProduct

open Work.ORTorsion

namespace Work.ORTorsion.Descent

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Algebra K U]

/-! ## The `↥(L.D H)`-module structure on `↥(L.D ⊤)` -/

/-- The `↥(L.D H)`-module structure on `↥(L.D ⊤)` by left multiplication (restriction of scalars
along the algebra inclusion `↥(L.D H) → ↥(L.D ⊤)`). -/
noncomputable instance instModuleDHtop (L : TorsionData K G U) (H : Subgroup G) :
    Module ↥(L.D H) ↥(L.D ⊤) :=
  (Subalgebra.inclusion (L.D_mono le_top)).toModule

/-- The `↥(L.D H)`-module structure on `↥(L.D ⊤)` is compatible with the `K`-structure. -/
instance instIsScalarTowerDHtop (L : TorsionData K G U) (H : Subgroup G) :
    IsScalarTower K ↥(L.D H) ↥(L.D ⊤) :=
  Subalgebra.inclusion.isScalarTower_left (h := L.D_mono le_top) K

/-- The image of `h : H` in `↥(L.D H)` maps to its image in `↥(L.D ⊤)`. -/
theorem inclusion_genD (L : TorsionData K G U) (H : Subgroup G) (h : H) :
    Subalgebra.inclusion (L.D_mono le_top) (L.genD H h) = L.genTop (h : G) :=
  Subtype.ext rfl

/-! ## The action of a single algebra element -/

/-- Left multiplication by `a : A` on an `A`-module `M`, as a `K`-linear map. -/
noncomputable def smulEnd {A : Type*} [Ring A] [Algebra K A] {M : Type*} [AddCommGroup M]
    [Module K M] [Module A M] [IsScalarTower K A M] (a : A) : M →ₗ[K] M where
  toFun m := a • m
  map_add' m n := smul_add a m n
  map_smul' k m := by
    show a • (k • m) = k • (a • m)
    rw [← IsScalarTower.algebraMap_smul (R := K) A k m,
      ← IsScalarTower.algebraMap_smul (R := K) A k (a • m), smul_smul, smul_smul,
      Algebra.commutes]

@[simp] theorem smulEnd_apply {A : Type*} [Ring A] [Algebra K A] {M : Type*} [AddCommGroup M]
    [Module K M] [Module A M] [IsScalarTower K A M] (a : A) (m : M) :
    smulEnd (K := K) a m = a • m := rfl

theorem smulEnd_one {A : Type*} [Ring A] [Algebra K A] {M : Type*} [AddCommGroup M]
    [Module K M] [Module A M] [IsScalarTower K A M] :
    (smulEnd (K := K) (1 : A) : M →ₗ[K] M) = LinearMap.id := by
  ext m; simp [smulEnd]

theorem smulEnd_mul {A : Type*} [Ring A] [Algebra K A] {M : Type*} [AddCommGroup M]
    [Module K M] [Module A M] [IsScalarTower K A M] (a b : A) :
    (smulEnd (K := K) (a * b) : M →ₗ[K] M) =
      (smulEnd (K := K) a).comp (smulEnd (K := K) b) := by
  ext m; simp [smulEnd, mul_smul]

/-! ## The diagonal action -/

/-- The diagonal action of `h : H` on `V ⊗[K] M`: `v ⊗ m ↦ (h • v) ⊗ (h • m)`. -/
noncomputable def diagActGroup (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (H : Subgroup G) (M : Type*) [AddCommGroup M] [Module K M] [Module ↥(L.D H) M]
    [IsScalarTower K ↥(L.D H) M] : H →* Module.End K (V ⊗[K] M) where
  toFun h := TensorProduct.map (gAct (h : G)) (smulEnd (K := K) (L.genD H h))
  map_one' := by
    show TensorProduct.map (gAct (1 : G)) (smulEnd (K := K) (L.genD H 1)) = 1
    rw [map_one, smulEnd_one, gAct_one (K := K), TensorProduct.map_id]
    rfl
  map_mul' h h' := by
    show TensorProduct.map (gAct ((h : G) * (h' : G))) (smulEnd (K := K) (L.genD H (h * h')))
      = TensorProduct.map (gAct (h : G)) (smulEnd (K := K) (L.genD H h))
        * TensorProduct.map (gAct (h' : G)) (smulEnd (K := K) (L.genD H h'))
    rw [map_mul, smulEnd_mul, gAct_mul (K := K) (h : G) (h' : G), TensorProduct.map_comp]
    rfl

/-- The diagonal action of `K[H]` on `V ⊗[K] M`. -/
noncomputable def diagAct (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (H : Subgroup G) (M : Type*) [AddCommGroup M] [Module K M] [Module ↥(L.D H) M]
    [IsScalarTower K ↥(L.D H) M] : MonoidAlgebra K H →ₐ[K] Module.End K (V ⊗[K] M) :=
  MonoidAlgebra.lift K (Module.End K (V ⊗[K] M)) H (diagActGroup L H M)

theorem diagAct_single (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (H : Subgroup G) (M : Type*) [AddCommGroup M] [Module K M] [Module ↥(L.D H) M]
    [IsScalarTower K ↥(L.D H) M] (h : H) :
    diagAct L H M (MonoidAlgebra.single h (1 : K) : MonoidAlgebra K H)
      = (TensorProduct.map (gAct (h : G)) (smulEnd (K := K) (L.genD H h)) :
          V ⊗[K] M →ₗ[K] V ⊗[K] M) := by
  show (MonoidAlgebra.lift K (Module.End K (V ⊗[K] M)) H (diagActGroup L H M))
      (MonoidAlgebra.single h (1 : K) : MonoidAlgebra K H) = _
  rw [MonoidAlgebra.lift_single, one_smul]
  rfl

/-- **Functoriality of the diagonal action.**  If `f : M →ₗ[↥(L.D H)] N` is `↥(L.D H)`-linear,
then `id ⊗ f` is `K[H]`-linear for the diagonal actions. -/
theorem diagAct_map (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (H : Subgroup G) {M : Type*} [AddCommGroup M] [Module K M] [Module ↥(L.D H) M]
    [IsScalarTower K ↥(L.D H) M]
    {N : Type*} [AddCommGroup N] [Module K N] [Module ↥(L.D H) N]
    [IsScalarTower K ↥(L.D H) N]
    (f : M →ₗ[↥(L.D H)] N) (x : MonoidAlgebra K H) (y : V ⊗[K] M) :
    TensorProduct.map (LinearMap.id : V →ₗ[K] V) (f.restrictScalars K) (diagAct L H M x y)
      = diagAct L H N x (TensorProduct.map (LinearMap.id : V →ₗ[K] V) (f.restrictScalars K) y) := by
  let T : V ⊗[K] M →ₗ[K] V ⊗[K] N :=
    TensorProduct.map (LinearMap.id : V →ₗ[K] V) (f.restrictScalars K)
  have hsingle : ∀ (h : H) (y : V ⊗[K] M),
      T (diagAct L H M (MonoidAlgebra.single h (1 : K) : MonoidAlgebra K H) y)
        = diagAct L H N (MonoidAlgebra.single h (1 : K) : MonoidAlgebra K H) (T y) := by
    intro h y
    rw [diagAct_single, diagAct_single]
    have hfa : (f.restrictScalars K).comp (smulEnd (K := K) (L.genD H h) : M →ₗ[K] M)
        = (smulEnd (K := K) (L.genD H h) : N →ₗ[K] N).comp (f.restrictScalars K) := by
      ext m
      simp only [LinearMap.comp_apply]
      exact map_smul f (L.genD H h) m
    have key : T.comp (TensorProduct.map (gAct (h : G))
          (smulEnd (K := K) (L.genD H h) : M →ₗ[K] M))
        = (TensorProduct.map (gAct (h : G))
          (smulEnd (K := K) (L.genD H h) : N →ₗ[K] N)).comp T := by
      unfold T
      rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
      rw [LinearMap.id_comp, LinearMap.comp_id, hfa]
    exact LinearMap.congr_fun key y
  have hmain : ∀ z : MonoidAlgebra K H,
      T (diagAct L H M z y) = diagAct L H N z (T y) := by
    intro z
    induction z using MonoidAlgebra.induction_on with
    | of m => simpa only [MonoidAlgebra.of_apply] using hsingle m y
    | add p q hp hq =>
        simp only [map_add, LinearMap.add_apply]
        rw [hp, hq]
    | smul k p hp =>
        simp only [map_smul, LinearMap.smul_apply, hp]
  exact hmain x

end Work.ORTorsion.Descent
