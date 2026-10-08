import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

/-- If `P ≤ R`, `Y` normalizes `R` and centralizes `P`, and `u ∈ R \ P`, then for
`y ∈ Y` and `p ∈ P` the element `p * (y * u * y⁻¹)` lies in `R` but not in `P`.

The element lies in `R` because `Y` normalizes `R` (so `y * u * y⁻¹ ∈ R`) and `P ≤ R`.
It is outside `P` because `P` is closed under inverses and multiplication: from
`p * (y * u * y⁻¹) ∈ P` we get `y * u * y⁻¹ ∈ P`, and since `y` centralizes `P`
this forces `y * u * y⁻¹ = u`, contradicting `u ∉ P`. -/
theorem mul_conj_mem_sdiff {G : Type} [Group G] {P R Y : Subgroup G} {u : G}
    (hPR : P ≤ R) (hYR : Y ≤ Subgroup.normalizer (R : Set G))
    (hYP : Y ≤ Subgroup.centralizer (P : Set G))
    (hu : u ∈ R) (huP : u ∉ P) (y : ↥Y) (p : ↥P) :
    (p : G) * ((y : G) * u * (y : G)⁻¹) ∈ (R : Set G) \ (P : Set G) := by
  have hyu : (y : G) * u * (y : G)⁻¹ ∈ R :=
    (Subgroup.le_normalizer_iff.mp hYR) (y : G) y.2 u hu
  refine ⟨?_, ?_⟩
  · exact mul_mem (hPR p.2) hyu
  · intro hmem
    have hp_inv : (p : G)⁻¹ ∈ P := inv_mem p.2
    have hw_mem : (y : G) * u * (y : G)⁻¹ ∈ P := by
      have := mul_mem hp_inv hmem
      simpa using this
    have hy_cent : (y : G) ∈ Subgroup.centralizer (P : Set G) := hYP y.2
    have hcomm : ((y : G) * u * (y : G)⁻¹) * (y : G) = (y : G) * ((y : G) * u * (y : G)⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hy_cent) _ hw_mem
    have h2 : (y : G) * u = (y : G) * ((y : G) * u * (y : G)⁻¹) := by
      rw [← hcomm]; group
    have h_eq : u = (y : G) * u * (y : G)⁻¹ := mul_left_cancel h2
    exact huP (h_eq ▸ hw_mem)

end Work.ThmF.ChV3.Prove
