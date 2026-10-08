import Mathlib
import Submission.Work.Higman.Layers.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Layers

/-- The kernel of an idempotent projection onto `C` that commutes with `σ` is a `σ`-invariant
complement of `C`.  (`hPmem` and `hPid` say that `P` is a projection onto `C`.) -/
theorem ker_projection_isInv_isCompl {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {σ P : V →ₗ[ZMod 2] V} {C : Submodule (ZMod 2) V}
    (hcomm : P * σ = σ * P) (hPmem : ∀ v : V, P v ∈ C) (hPid : ∀ u : V, u ∈ C → P u = u) :
    Work.Higman.Layers.IsInv σ (LinearMap.ker P) ∧
      C ⊓ LinearMap.ker P = ⊥ ∧ C ⊔ LinearMap.ker P = ⊤ := by
  -- `P` commutes with `σ`, so `P (σ v) = σ (P v)` for every `v`.
  have hcomm' : ∀ v : V, P (σ v) = σ (P v) := fun v => LinearMap.congr_fun hcomm v
  -- `P` is idempotent: `P v ∈ C` hence `P (P v) = P v`.
  have hidem : ∀ v : V, P (P v) = P v := fun v => hPid (P v) (hPmem v)
  refine ⟨?_, ?_, ?_⟩
  · -- `ker P` is `σ`-invariant.
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hcomm' v, hv, map_zero]
  · -- `C` and `ker P` are disjoint.
    rw [Submodule.eq_bot_iff]
    intro u hu
    rw [Submodule.mem_inf] at hu
    obtain ⟨huC, huker⟩ := hu
    rw [LinearMap.mem_ker] at huker
    rw [← hPid u huC, huker]
  · -- `C` and `ker P` span `V`: split `v = P v + (v - P v)`.
    apply le_antisymm le_top
    intro v _
    rw [Submodule.mem_sup]
    exact ⟨P v, hPmem v, v - P v,
      by rw [LinearMap.mem_ker, map_sub, hidem, sub_self], by abel⟩

end Work.Higman.Layers
