import Mathlib
import Submission.Work.ThmF.ChV12.irreducible_of_orderOf_prime
import Submission.Work.ThmF.ChV12.mulAut_mul_comm_of_commute_of_irreducible

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

/-- The conclusion `ρ σ * ρ h * (ρ σ)⁻¹ * (ρ h)⁻¹ ∈ Subgroup.map ρ K` is, by injectivity of
`ρ`, exactly the statement `σ * h * σ⁻¹ * h⁻¹ ∈ K`. -/
lemma mem_map_rho_commutator_iff {A D : Type} [Group A] [Group D] (ρ : D →* MulAut A)
    (hfaith : Function.Injective ρ) (σ h : D) (K : Subgroup D) :
    (ρ σ * ρ h * (ρ σ)⁻¹ * (ρ h)⁻¹ ∈ Subgroup.map ρ K) ↔ (σ * h * σ⁻¹ * h⁻¹ ∈ K) := by
  constructor
  · intro hmem
    rw [Subgroup.mem_map] at hmem
    obtain ⟨k, hk, hk_eq⟩ := hmem
    have : ρ (σ * h * σ⁻¹ * h⁻¹) = ρ k := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hk_eq]
    exact (hfaith this) ▸ hk
  · intro hmem
    rw [Subgroup.mem_map]
    exact ⟨σ * h * σ⁻¹ * h⁻¹, hmem, by rw [map_mul, map_mul, map_mul, map_inv, map_inv]⟩

theorem ppd_trivial_on_abelian_normal_section {A D : Type} [Group A] [Finite A] [Group D] [Finite D]
    (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x) {k q : ℕ}
    (hk1 : 1 ≤ k) (hk : Nat.card A = 2 ^ k) (hq : Nat.Prime q)
    (hord : orderOf (2 : ZMod q) = k)
    (ρ : D →* MulAut A) (hfaith : Function.Injective ρ)
    (σ : D) (hσ : orderOf σ = q)
    (H : Subgroup D) (hHnorm : H.Normal)
    (K : Subgroup D) (hKnorm : K.Normal) (hKH : K ≤ H)
    (hab : ∀ x ∈ H, ∀ y ∈ H, x * y * x⁻¹ * y⁻¹ ∈ K) :
    ∀ h ∈ H, ρ σ * ρ h * (ρ σ)⁻¹ * (ρ h)⁻¹ ∈ Subgroup.map ρ K := by sorry

end Work.ThmF.ChV12
