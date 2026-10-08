import Mathlib
import Submission.Work.PSU3.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB

/-- Every endomorphism of `(E n)ˣ`, the multiplicative group of the finite field
`E n = GF(2^{2n})`, is a power map `a ↦ a ^ μ`.  Indeed `(E n)ˣ` is cyclic (the unit group
of a finite field), so such a homomorphism is determined by the image of a generator
`g`, say `nm g = g ^ μ`, and `nm (g ^ k) = (g ^ μ) ^ k = g ^ (μ * k) = (g ^ k) ^ μ`. -/
theorem nm_pow_map (n : ℕ) (nm : (Work.PSU3.E n)ˣ →* (Work.PSU3.E n)ˣ) :
    ∃ μ : ℕ, ∀ a : (Work.PSU3.E n)ˣ, nm a = a ^ μ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (Work.PSU3.E n)ˣ)
  obtain ⟨μ, hμ0⟩ := mem_powers_iff_mem_zpowers.mpr (hg (nm g))
  have hμ : g ^ μ = nm g := hμ0
  refine ⟨μ, fun a => ?_⟩
  obtain ⟨k, hk0⟩ := mem_powers_iff_mem_zpowers.mpr (hg a)
  have hk : g ^ k = a := hk0
  calc nm a = nm (g ^ k) := by rw [hk]
    _ = (nm g) ^ k := map_pow _ _ _
    _ = (g ^ μ) ^ k := by rw [hμ]
    _ = g ^ (μ * k) := (pow_mul g μ k).symm
    _ = g ^ (k * μ) := congrArg (fun e => g ^ e) (Nat.mul_comm μ k)
    _ = (g ^ k) ^ μ := pow_mul g k μ
    _ = a ^ μ := by rw [hk]

end Work.PSU3.StageB
