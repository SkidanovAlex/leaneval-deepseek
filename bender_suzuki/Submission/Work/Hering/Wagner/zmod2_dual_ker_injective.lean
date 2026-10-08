import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.Wagner

/-- The only nonzero element of `ZMod 2` is `1`. -/
private lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

theorem zmod2_dual_ker_injective {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {φ ψ : Module.Dual (ZMod 2) V} (hφ : φ ≠ 0) (hψ : ψ ≠ 0)
    (h : LinearMap.ker φ = LinearMap.ker ψ) : φ = ψ := by
  -- `φ` is nonzero, so it takes a nonzero value somewhere.
  have hne : ∃ v, φ v ≠ 0 := by
    by_contra hc
    exact hφ (LinearMap.ext fun w => by
      by_contra hw
      exact hc ⟨w, hw⟩)
  obtain ⟨v, hv⟩ := hne
  -- Over `ZMod 2` a nonzero value is `1`, so `φ v = 1` and `ψ v = 1`.
  have hv1 : φ v = 1 := zmod2_eq_one_of_ne_zero hv
  have hψv : ψ v ≠ 0 := by
    intro h0
    have : v ∈ LinearMap.ker ψ := LinearMap.mem_ker.mpr h0
    rw [← h] at this
    exact hv (LinearMap.mem_ker.mp this)
  have hψ1 : ψ v = 1 := zmod2_eq_one_of_ne_zero hψv
  -- `w - φ w • v` lies in `ker φ = ker ψ`, which forces `ψ w = φ w`.
  apply LinearMap.ext
  intro w
  have h1 : w - φ w • v ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker, map_sub, map_smul, hv1, smul_eq_mul, mul_one, sub_self]
  have h1' : w - φ w • v ∈ LinearMap.ker ψ := by rw [← h]; exact h1
  rw [LinearMap.mem_ker, map_sub, map_smul, hψ1, smul_eq_mul, mul_one] at h1'
  exact (sub_eq_zero.mp h1').symm

end Work.Hering.Wagner
