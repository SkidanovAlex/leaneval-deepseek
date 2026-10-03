import Mathlib

universe u

namespace Work.Section3.RkFinModel

/-- For an idempotent endomorphism `E` (`E * E = E`) of `Fin n → S`, the range of `E`
meets the span of `u - E u` trivially.

Indeed `u - E u` lies in the kernel of `E`, hence the whole span of `u - E u` does;
and for an idempotent `E` one has `range E ⊓ ker E = ⊥` since every `x ∈ range E`
satisfies `E x = x`. -/
theorem rkcs_range_inf_span_sub_proj_eq_bot {S : Type u} [Ring S] {n : ℕ}
    (E : Module.End S (Fin n → S)) (hE : E * E = E) (u : Fin n → S) :
    LinearMap.range E ⊓ Submodule.span S ({u - E u} : Set (Fin n → S)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨hxr, hxs⟩ := hx
  -- `u - E u` is killed by `E`.
  have hv : E (u - E u) = 0 := by
    rw [map_sub, ← Module.End.mul_apply, hE, sub_self]
  -- hence every element of the span of `u - E u` is killed by `E`.
  obtain ⟨a, ha⟩ := (Submodule.mem_span_singleton).mp hxs
  have hzero : E x = 0 := by
    rw [← ha, map_smul, hv, smul_zero]
  -- on the other hand `E` fixes its range because it is idempotent.
  obtain ⟨y, hy⟩ := (LinearMap.mem_range).mp hxr
  have hfix : E x = x := by
    rw [← hy, ← Module.End.mul_apply, hE]
  rw [← hfix, hzero]

end Work.Section3.RkFinModel
