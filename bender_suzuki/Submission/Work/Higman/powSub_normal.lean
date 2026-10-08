import Mathlib
import Submission.Work.Higman.PowSub

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- The `n`-th power subgroup of a normal subgroup is normal.

The generators `x ^ n` of `powSub C n` (with `x ∈ C`) are permuted by conjugation,
since `g * x ^ n * g⁻¹ = (g * x * g⁻¹) ^ n` and `g * x * g⁻¹ ∈ C` when `C` is normal;
so the subgroup they generate is invariant under conjugation. -/
theorem powSub_normal {P : Type} [Group P] {C : Subgroup P} (hC : C.Normal) (n : ℕ) :
    (Work.Higman.powSub C n).Normal := by
  refine Subgroup.Normal.mk (fun a ha g => ?_)
  rw [powSub] at ha ⊢
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact Subgroup.subset_closure ⟨g * y * g⁻¹, hC.conj_mem y hy g, conj_pow⟩
  | one => simpa using Subgroup.one_mem (Subgroup.closure {y : P | ∃ x ∈ C, x ^ n = y})
  | mul u v hu hv ihu ihv =>
      have h : g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) := by group
      rw [h]
      exact Subgroup.mul_mem _ ihu ihv
  | inv u hu ihu =>
      have h : g * u⁻¹ * g⁻¹ = (g * u * g⁻¹)⁻¹ := by group
      rw [h]
      exact Subgroup.inv_mem _ ihu

end Work.Higman
