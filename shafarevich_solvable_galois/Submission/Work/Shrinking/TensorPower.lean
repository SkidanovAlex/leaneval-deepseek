import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Submission.Work.Shrinking.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Shrinking

open scoped TensorProduct

universe u

variable {p : ℕ}

/-! ## Coordinate projections of tensor powers -/

section TensorExpand

variable {M : Type*} [AddCommGroup M] [Module (ZMod p) M]

/-- The `e`-th coordinate projection `(M^r)^{⊗s} → M^{⊗s}`, `⊗_j x_j ↦ ⊗_j x_j (e j)`. -/
def tensorExpand (s r : ℕ) (e : Fin s → Fin r) :
    (⨂[ZMod p]^s (Fin r → M)) →ₗ[ZMod p] ⨂[ZMod p]^s M :=
  PiTensorProduct.map (fun j : Fin s => LinearMap.proj (e j))

@[simp]
lemma tensorExpand_tprod (s r : ℕ) (e : Fin s → Fin r) (x : Fin s → (Fin r → M)) :
    tensorExpand (p := p) s r e (PiTensorProduct.tprod (ZMod p) x)
      = PiTensorProduct.tprod (ZMod p) (fun j => x j (e j)) := by
  rw [tensorExpand, PiTensorProduct.map_tprod]
  rfl

/-- The tensor power of a folding map is the homogeneous degree-`s` polynomial map
`∑_{e : Fin s → Fin r} (∏ j, a (e j)) • tensorExpand e` in `a`. -/
lemma map_foldMap_eq_sum (s r : ℕ) (a : Fin r → ZMod p) :
    PiTensorProduct.map (fun _ : Fin s => foldMap (M := M) a)
      = ∑ e : Fin s → Fin r, (∏ j, a (e j)) • tensorExpand (p := p) s r e := by
  have h1 : (fun _ : Fin s => foldMap (M := M) a)
      = fun _ : Fin s => ∑ i, a i • (LinearMap.proj i : (Fin r → M) →ₗ[ZMod p] M) := by
    funext j
    refine LinearMap.ext fun x => ?_
    rw [foldMap_apply, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [LinearMap.smul_apply, LinearMap.proj_apply]
  calc PiTensorProduct.map (fun _ : Fin s => foldMap (M := M) a)
      = PiTensorProduct.mapMultilinear (ZMod p) (fun _ : Fin s => (Fin r → M))
          (fun _ : Fin s => M) (fun _ : Fin s => foldMap (M := M) a) :=
        (PiTensorProduct.mapMultilinear_apply (ZMod p) (fun _ : Fin s => (Fin r → M))
          (fun _ : Fin s => M) _).symm
    _ = PiTensorProduct.mapMultilinear (ZMod p) (fun _ : Fin s => (Fin r → M))
          (fun _ : Fin s => M)
          (fun _ : Fin s => ∑ i, a i • (LinearMap.proj i : (Fin r → M) →ₗ[ZMod p] M)) := by
          rw [h1]
    _ = ∑ e : Fin s → Fin r,
          PiTensorProduct.mapMultilinear (ZMod p) (fun _ : Fin s => (Fin r → M))
            (fun _ : Fin s => M)
            (fun j => a (e j) • (LinearMap.proj (e j) : (Fin r → M) →ₗ[ZMod p] M)) :=
          MultilinearMap.map_sum _ _
    _ = ∑ e : Fin s → Fin r, (∏ j, a (e j)) • tensorExpand (p := p) s r e := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [MultilinearMap.map_smul_univ]
          rfl

end TensorExpand

/-! ## Equivariance

The maps above are `𝔽_p[G]`-homomorphisms for the diagonal `G`-action on tensor powers
(and, after tensoring with `N`, on `M ⊗ N`). -/

section Equivariance

variable {G M N : Type*} [Group G]
  [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M]

/-- The diagonal action on a tensor power is induced by the diagonal action on the factors. -/
lemma smul_tensorPower_eq_map (s : ℕ) (g : G) (y : ⨂[ZMod p]^s M) :
    g • y = PiTensorProduct.map (fun _ : Fin s => actLinear (p := p) g) y := rfl

/-- The tensor power of the folding map commutes with the diagonal actions. -/
lemma map_foldMap_comp_actLinear (s r : ℕ) (a : Fin r → ZMod p) (g : G) :
    PiTensorProduct.map (fun _ : Fin s => foldMap (M := M) a)
        ∘ₗ PiTensorProduct.map (fun _ : Fin s => actLinear (p := p) g)
      = PiTensorProduct.map (fun _ : Fin s => actLinear (p := p) g)
        ∘ₗ PiTensorProduct.map (fun _ : Fin s => foldMap (M := M) a) := by
  rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  congr 1
  funext j
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, actLinear_apply]
  exact foldMap_equivariant a g x

/-- `TensorPower.map (fun _ => φ_a)` is `G`-equivariant. -/
lemma map_foldMap_smul (s r : ℕ) (a : Fin r → ZMod p) (g : G)
    (y : ⨂[ZMod p]^s (Fin r → M)) :
    PiTensorProduct.map (fun _ : Fin s => foldMap (M := M) a) (g • y)
      = g • PiTensorProduct.map (fun _ : Fin s => foldMap (M := M) a) y := by
  conv_lhs => rw [smul_tensorPower_eq_map (p := p) (M := Fin r → M) s g y]
  rw [← LinearMap.comp_apply, map_foldMap_comp_actLinear, LinearMap.comp_apply,
    smul_tensorPower_eq_map (p := p) (M := M) s g]

/-- The map `f ⊗ id` is `G`-equivariant whenever `f` is. -/
lemma rTensor_smul (s r : ℕ) (f : (⨂[ZMod p]^s (Fin r → M)) →ₗ[ZMod p] ⨂[ZMod p]^s M)
    (hf : ∀ (g : G) (y : ⨂[ZMod p]^s (Fin r → M)), f (g • y) = g • f y)
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N] [SMulCommClass G (ZMod p) N]
    (g : G) (z : (⨂[ZMod p]^s (Fin r → M)) ⊗[ZMod p] N) :
    f.rTensor N (g • z) = g • (f.rTensor N z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul x n =>
    rw [diagTensor_smul_tmul, LinearMap.rTensor_tmul, hf, LinearMap.rTensor_tmul,
      diagTensor_smul_tmul]
  | add z w hz hw => simp only [smul_add, map_add, hz, hw]

/-- `(TensorPower.map (fun _ => φ_a)) ⊗ id_N` is `G`-equivariant. -/
lemma rTensor_map_foldMap_smul (s r : ℕ) (a : Fin r → ZMod p) (g : G)
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N] [SMulCommClass G (ZMod p) N]
    (z : (⨂[ZMod p]^s (Fin r → M)) ⊗[ZMod p] N) :
    ((PiTensorProduct.map (fun _ : Fin s => foldMap (M := M) a)).rTensor N) (g • z)
      = g • ((PiTensorProduct.map (fun _ : Fin s => foldMap (M := M) a)).rTensor N) z :=
  rTensor_smul s r _ (fun g y => map_foldMap_smul s r a g y) g z

end Equivariance

/-! ## The polynomial form after tensoring with `N` -/

section RTensor

variable {M N : Type*} [AddCommGroup M] [Module (ZMod p) M]
  [AddCommGroup N] [Module (ZMod p) N]

/-- The value of the tensor power of a folding map on an element of `(⨂^s (M^r)) ⊗ N`,
written as the value of the degree-`s` polynomial map `∑ e, (∏ j, a (e j)) • tensorExpand e`. -/
lemma rTensor_map_foldMap_apply (s r : ℕ) (a : Fin r → ZMod p)
    (z : (⨂[ZMod p]^s (Fin r → M)) ⊗[ZMod p] N) :
    ((PiTensorProduct.map (fun _ : Fin s => foldMap (M := M) a)).rTensor N) z
      = ∑ e : Fin s → Fin r,
          (∏ j, a (e j)) • (((tensorExpand (p := p) s r e).rTensor N) z) := by
  have key : PiTensorProduct.map (fun _ : Fin s => foldMap (M := M) a)
      = ∑ e : Fin s → Fin r, (∏ j, a (e j)) • (tensorExpand (p := p) (M := M) s r e) :=
    map_foldMap_eq_sum (p := p) (M := M) s r a
  have key2 :
      ((∑ e : Fin s → Fin r, (∏ j, a (e j)) • (tensorExpand (p := p) (M := M) s r e)).rTensor N)
      = ∑ e : Fin s → Fin r,
          (∏ j, a (e j)) • (tensorExpand (p := p) (M := M) s r e).rTensor N := by
    have h : ((∑ e : Fin s → Fin r,
          (∏ j, a (e j)) • (tensorExpand (p := p) (M := M) s r e)).rTensor N)
        = LinearMap.rTensorHom N (∑ e : Fin s → Fin r,
            (∏ j, a (e j)) • (tensorExpand (p := p) (M := M) s r e)) := rfl
    rw [h, map_sum]
    simp only [map_smul, LinearMap.coe_rTensorHom]
  rw [key, key2]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]

/-- The fundamental identity of the shrinking procedure, tensored with `id_N`. -/
lemma rTensor_map_foldMap_eq_sum (s r : ℕ) (a : Fin r → ZMod p) :
    (PiTensorProduct.map (fun _ : Fin s => foldMap (M := M) a)).rTensor N
      = ∑ e : Fin s → Fin r, (∏ j, a (e j)) • (tensorExpand (p := p) s r e).rTensor N := by
  refine LinearMap.ext fun z => ?_
  rw [rTensor_map_foldMap_apply (p := p) (M := M) (N := N) s r a]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]

end RTensor

end Work.Shrinking
