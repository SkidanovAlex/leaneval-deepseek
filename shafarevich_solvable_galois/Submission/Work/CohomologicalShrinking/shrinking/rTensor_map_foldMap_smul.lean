import Mathlib
import Submission.Work.Shrinking.TensorPower
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.shrinking

open scoped TensorProduct

/-- The folding map `φ_a : (Fin r → M) →ₗ[𝔽_p] M`, `x ↦ ∑ i, a i • x i`, is `𝔽_p`-linear in
the coefficient vector `a`: `φ_{c • a} = c • φ_a`. -/
private lemma foldMap_smul_const {p : ℕ} {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    {r : ℕ} (c : ZMod p) (a : Fin r → ZMod p) :
    Work.Shrinking.foldMap (M := M) (c • a) = c • Work.Shrinking.foldMap (M := M) a := by
  apply LinearMap.ext
  intro x
  simp only [Work.Shrinking.foldMap_apply, Pi.smul_apply, LinearMap.smul_apply]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, mul_smul]

/-- `PiTensorProduct.map` over `Fin j` of a constant family of linear maps scaled by `c` is the
`j`-th power of `c` times the tensor product of the unscaled family (multilinearity). -/
private lemma piTensorProduct_map_const_smul {p : ℕ} {M : Type*} [AddCommGroup M]
    [Module (ZMod p) M]
    (j r : ℕ) (c : ZMod p) (f : (Fin r → M) →ₗ[ZMod p] M) :
    PiTensorProduct.map (fun _ : Fin j => c • f)
      = c ^ j • PiTensorProduct.map (fun _ : Fin j => f) := by
  rw [← PiTensorProduct.mapMultilinear_apply (ZMod p) (fun _ : Fin j => (Fin r → M))
        (fun _ : Fin j => M) (fun _ => c • f)]
  rw [← PiTensorProduct.mapMultilinear_apply (ZMod p) (fun _ : Fin j => (Fin r → M))
        (fun _ : Fin j => M) (fun _ => f)]
  rw [MultilinearMap.map_smul_univ]
  simp

theorem rTensor_map_foldMap_smul (p : ℕ) {G M N : Type*} [Group G] [AddCommGroup M]
    [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    [AddCommGroup N] [Module (ZMod p) N]
    (j r : ℕ) (c : ZMod p) (a : Fin r → ZMod p)
    (z : TensorProduct (ZMod p) (PiTensorProduct (ZMod p) (fun _ : Fin j => Fin r → M)) N) :
    LinearMap.rTensor N (PiTensorProduct.map
        (fun _ : Fin j => Work.Shrinking.foldMap (M := M) (c • a))) z
      = c ^ j • (LinearMap.rTensor N (PiTensorProduct.map
          (fun _ : Fin j => Work.Shrinking.foldMap (M := M) a)) z) := by
  have hfold : (fun _ : Fin j => Work.Shrinking.foldMap (M := M) (c • a))
      = fun _ : Fin j => c • Work.Shrinking.foldMap (M := M) a := by
    funext i; exact foldMap_smul_const c a
  rw [hfold]
  rw [piTensorProduct_map_const_smul j r c (Work.Shrinking.foldMap (M := M) a)]
  rw [LinearMap.rTensor_smul]
  simp

end Work.CohomologicalShrinking.shrinking
