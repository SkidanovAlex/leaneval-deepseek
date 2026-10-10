import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.Nodes.UEPR

open Localization

/-- The elements of the localization `A[S⁻¹]` of a domain `B` in its fraction field `Ω`,
considered via `Localization.subalgebra.ofField`, are exactly the `a * s⁻¹` with `s ∈ S`. -/
theorem mem_ofField_iff' {B Ω : Type*} [CommRing B] [IsDomain B] [Field Ω] [Algebra B Ω]
    [IsFractionRing B Ω] (S : Submonoid B) (hS : S ≤ nonZeroDivisors B) (x : Ω) :
    x ∈ Localization.subalgebra.ofField Ω S hS ↔
      ∃ (a s : B) (_hs : s ∈ S), x = algebraMap B Ω a * (algebraMap B Ω s)⁻¹ := by
  rw [Localization.subalgebra.ofField_eq, Localization.subalgebra, Subalgebra.copy_eq,
    Localization.subalgebra.mem_range_mapToFractionRing_iff_ofField Ω S hS (Localization S) x]

/-- If a subring `W ⊆ Ω` contains the image of `B` and contains every `algebraMap B Ω s`,
`s ∈ Pᶜ`, as a unit of `W`, then it contains the whole localization `B[Pᶜ] ⊆ Ω`. -/
theorem algebraMap_ofField_range_le {B Ω : Type*} [CommRing B] [IsDomain B] [Field Ω] [Algebra B Ω] [IsFractionRing B Ω] (P : Ideal B) [P.IsPrime] (hP : P.primeCompl ≤ nonZeroDivisors B) (W : Subring Ω) (hBW : (algebraMap B Ω).range ≤ W) (hunit : ∀ s : P.primeCompl, ∃ u : Wˣ, ((u : W) : Ω) = algebraMap B Ω (s : B)) : (algebraMap ↥(Localization.subalgebra.ofField Ω P.primeCompl hP) Ω).range ≤ W := by
  intro y hy
  rcases hy with ⟨v, rfl⟩
  change (v : Ω) ∈ W
  obtain ⟨a, s, hs, hv⟩ := (mem_ofField_iff' P.primeCompl hP (v : Ω)).mp v.2
  rw [hv]
  obtain ⟨u, hu⟩ := hunit ⟨s, hs⟩
  have hmem : algebraMap B Ω a ∈ W := hBW ⟨a, rfl⟩
  have hcoe : ((u⁻¹ : Wˣ) : Ω) = (algebraMap B Ω s)⁻¹ := by
    rw [← hu]
    have h1 : (((u : Wˣ) : W) : Ω) * ((u⁻¹ : Wˣ) : Ω) = 1 := by
      simp [← Subring.coe_mul]
    exact eq_inv_of_mul_eq_one_right h1
  rw [← hcoe]
  exact W.mul_mem hmem ((u⁻¹ : Wˣ) : W).2

end Work.MotV5.Nodes.UEPR
