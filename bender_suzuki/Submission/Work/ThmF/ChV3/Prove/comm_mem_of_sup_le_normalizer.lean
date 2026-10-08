import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

/-- If `R ⊔ M` normalizes `R` and `s ∈ R ⊔ M` commutes with `M` modulo `R`, then
`s` commutes with all of `R ⊔ M` modulo `R`.

The set `A = {g ∈ R ⊔ M | g * s * g⁻¹ * s⁻¹ ∈ R}` is a subgroup containing both
`R` and `M`, hence contains `R ⊔ M`. -/
theorem comm_mem_of_sup_le_normalizer {G : Type*} [Group G] {R M : Subgroup G}
    (hN : R ⊔ M ≤ Subgroup.normalizer (R : Set G)) {s : G} (hs : s ∈ R ⊔ M)
    (hM : ∀ x ∈ M, x * s * x⁻¹ * s⁻¹ ∈ R) :
    ∀ g ∈ R ⊔ M, g * s * g⁻¹ * s⁻¹ ∈ R := by
  let A : Subgroup G :=
  { carrier := {g | g ∈ R ⊔ M ∧ g * s * g⁻¹ * s⁻¹ ∈ R}
    one_mem' := by
      refine ⟨one_mem _, ?_⟩
      simp
    mul_mem' := by
      rintro a b ⟨haN, hac⟩ ⟨hbN, hbc⟩
      refine ⟨mul_mem haN hbN, ?_⟩
      have ha_norm : a ∈ Subgroup.normalizer (R : Set G) := hN haN
      have h1 : a * (b * s * b⁻¹ * s⁻¹) * a⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp ha_norm _).mp hbc
      have h2 : (a * b) * s * (a * b)⁻¹ * s⁻¹
          = (a * (b * s * b⁻¹ * s⁻¹) * a⁻¹) * (a * s * a⁻¹ * s⁻¹) := by
        group
      rw [h2]
      exact mul_mem h1 hac
    inv_mem' := by
      rintro a ⟨haN, hac⟩
      refine ⟨inv_mem haN, ?_⟩
      have ha_inv_norm : a⁻¹ ∈ Subgroup.normalizer (R : Set G) :=
        (Subgroup.normalizer (R : Set G)).inv_mem (hN haN)
      have h1 : a⁻¹ * (a * s * a⁻¹ * s⁻¹)⁻¹ * (a⁻¹)⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp ha_inv_norm _).mp (inv_mem hac)
      convert h1 using 1
      group }
  have hR_le : R ≤ A := by
    intro r hr
    refine ⟨Subgroup.mem_sup_left hr, ?_⟩
    have hs_norm : s ∈ Subgroup.normalizer (R : Set G) := hN hs
    have h2 : s * r⁻¹ * s⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hs_norm _).mp (inv_mem hr)
    have : r * s * r⁻¹ * s⁻¹ = r * (s * r⁻¹ * s⁻¹) := by group
    rw [this]
    exact mul_mem hr h2
  have hM_le : M ≤ A := fun x hx => ⟨Subgroup.mem_sup_right hx, hM x hx⟩
  have hNM : R ⊔ M ≤ A := sup_le hR_le hM_le
  intro g hg
  exact (hNM hg).2

end Work.ThmF.ChV3.Prove
