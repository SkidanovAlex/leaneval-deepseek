import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Trace

open scoped TensorProduct

theorem pi_trace {k : Type*} [Field k] {ι S : Type*} [Fintype ι] [AddCommGroup S]
    [Module k S] [Module.Finite k S] [Module.Free k S] (φ : S →ₗ[k] S) :
    LinearMap.trace k (ι → S) (LinearMap.pi fun i => φ.comp (LinearMap.proj i)) =
      (Fintype.card ι : k) • LinearMap.trace k S φ := by
  classical
  let f : (ι → S) →ₗ[k] (ι → S) := LinearMap.pi fun i => φ.comp (LinearMap.proj i)
  let e := TensorProduct.piScalarRight (R := k) (S := k) (N := S) (ι := ι)
  -- `f` is the conjugation of `φ ⊗ id` under `e.symm`.
  have hconj : e.symm.conj f = TensorProduct.map φ (LinearMap.id) := by
    apply TensorProduct.ext'
    intro n g
    have h1 : e (n ⊗ₜ[k] g) = fun j => g j • n := by simp [e]
    have h2 : f (fun j => g j • n) = fun j => g j • φ n := by
      funext i; simp [f]
    have h3 : (fun j => g j • φ n) = e (φ n ⊗ₜ[k] g) := by simp [e]
    simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm]
    rw [h1, h2, h3, LinearEquiv.symm_apply_apply]
    simp [TensorProduct.map_tmul]
  have htrace :
      LinearMap.trace k (TensorProduct k S (ι → k)) (TensorProduct.map φ (LinearMap.id)) =
        LinearMap.trace k S φ * (Fintype.card ι : k) := by
    rw [LinearMap.trace_tensorProduct', LinearMap.trace_id, Module.finrank_pi]
  have hmain : LinearMap.trace k (ι → S) f = LinearMap.trace k S φ * (Fintype.card ι : k) := by
    rw [← LinearMap.trace_conj' f e.symm, hconj, htrace]
  show LinearMap.trace k (ι → S) f = (Fintype.card ι : k) • LinearMap.trace k S φ
  rw [hmain, smul_eq_mul, mul_comm]

end Work.Trace
