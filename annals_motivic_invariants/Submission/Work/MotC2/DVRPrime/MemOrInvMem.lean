import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2.DVRPrime

/-- A subalgebra `S ⊆ K` of a field whose elements generate `K` as a fraction
field ("`S` has fraction field `K`"), and which is a prevaluation ring (for
`a b : S`, one of `a ∣ b`, `b ∣ a` holds), is a valuation subring of `K`:
every nonzero `f : K` satisfies `f ∈ S` or `f⁻¹ ∈ S`.

Proof: write `f = s₁ / s₂` with `s₁, s₂ ∈ S`, `s₂ ≠ 0` (possible by `hfrac`).
Prevaluation gives `c : S` with `s₂ * c = s₁` (then `f = c`) or `s₁ * c = s₂`
(then `f * c = 1`, so `f⁻¹ = c`). -/
theorem MemOrInvMem {L K : Type*} [Field L] [Field K] [Algebra L K]
    (S : Subalgebra L K) [PreValuationRing S]
    (hfrac : ∀ f : K, ∃ s₁ s₂ : S, (s₂ : K) ≠ 0 ∧ f * (s₂ : K) = (s₁ : K))
    {f : K} (hf : f ≠ 0) : f ∈ S ∨ f⁻¹ ∈ S := by
  obtain ⟨s₁, s₂, hs₂ne, hf_eq⟩ := hfrac f
  obtain ⟨c, hc | hc⟩ := PreValuationRing.cond s₂ s₁
  · -- `s₂ * c = s₁`, so `f = c`
    left
    have hcK : (s₁ : K) = (s₂ : K) * (c : K) := by rw [← hc, Subalgebra.coe_mul]
    have hfeq : f = (c : K) := by
      apply mul_right_cancel₀ hs₂ne
      calc f * (s₂ : K) = (s₁ : K) := hf_eq
        _ = (s₂ : K) * (c : K) := hcK
        _ = (c : K) * (s₂ : K) := by ring
    rw [hfeq]; exact c.2
  · -- `s₁ * c = s₂`, so `f * c = 1` and `f⁻¹ = c`
    right
    have hcK : (s₂ : K) = (s₁ : K) * (c : K) := by rw [← hc, Subalgebra.coe_mul]
    have hs₁ : (s₁ : K) ≠ 0 := by rw [← hf_eq]; exact mul_ne_zero hf hs₂ne
    have h1 : f * (c : K) = 1 := by
      have hh : (f * (c : K)) * (s₁ : K) = 1 * (s₁ : K) := by
        rw [one_mul]
        calc (f * (c : K)) * (s₁ : K)
            = f * ((s₁ : K) * (c : K)) := by ring
          _ = f * (s₂ : K) := by rw [hcK]
          _ = (s₁ : K) := hf_eq
      exact mul_right_cancel₀ hs₁ hh
    have hinv : f⁻¹ = (c : K) := inv_eq_of_mul_eq_one_right h1
    rw [hinv]; exact c.2

end Work.MotC2.DVRPrime
