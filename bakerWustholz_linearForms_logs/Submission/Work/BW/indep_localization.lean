import Mathlib
import Submission.Work.BW.wuestholzDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- `monoPow` is compatible with ring homomorphisms: `f (∏ uᵢ^βᵢ) = ∏ (f uᵢ)^βᵢ`. -/
lemma map_monoPow {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) {ℓ : ℕ}
    (u : Fin ℓ → R) (β : Fin ℓ → ℕ) :
    f (monoPow u β) = monoPow (fun i => f (u i)) β := by
  simp [monoPow, map_prod, map_pow]

/-- The image of the weighted sum commutes with `monoPow`: applying a ring hom to
`∑_{|β|=τ} C β · u^β` gives `∑_{|β|=τ} (f ∘ C) β · (f ∘ u)^β`. -/
lemma map_weightedSum {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {ℓ τ : ℕ}
    (C : (Fin ℓ → ℕ) → R) (u : Fin ℓ → R) :
    f (∑ β ∈ weightFinset ℓ τ, C β * monoPow u β)
      = ∑ β ∈ weightFinset ℓ τ, f (C β) * monoPow (fun i => f (u i)) β := by
  rw [map_sum]
  exact Finset.sum_congr rfl (fun β _ => by rw [map_mul, map_monoPow])

/-- Clear denominators: the independence of the degree-`τ` monomials in the `uᵢ` modulo
`J + 𝔓^{τ+1}` passes from `R` to a localization `S` (multiply by a common denominator from the
submonoid `M`, using `IsLocalization.exist_integer_multiples_of_finite`). -/
theorem indep_localization {R : Type*} [CommRing R] {M : Submonoid R} {S : Type*} [CommRing S]
    [Algebra R S] [IsLocalization M S] {ℓ : ℕ} (J 𝔓 : Ideal R) (u : Fin ℓ → R) (τ : ℕ)
    (hR : ∀ C : (Fin ℓ → ℕ) → R,
      algebraMap R S (∑ β ∈ weightFinset ℓ τ, C β * monoPow u β)
        ∈ Ideal.map (algebraMap R S) (J + 𝔓 ^ (τ + 1)) →
      ∀ α ∈ weightFinset ℓ τ, C α ∈ 𝔓)
    (C : (Fin ℓ → ℕ) → S)
    (hmem : (∑ β ∈ weightFinset ℓ τ, C β * monoPow (fun i => algebraMap R S (u i)) β)
        ∈ Ideal.map (algebraMap R S) J + (Ideal.map (algebraMap R S) 𝔓) ^ (τ + 1)) :
    ∀ α ∈ weightFinset ℓ τ, C α ∈ Ideal.map (algebraMap R S) 𝔓 := by
  classical
  -- Clear the denominators of the finitely many values `C β`, `β ∈ weightFinset ℓ τ`.
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finset M ((weightFinset ℓ τ).image C)
  have hb' : ∀ β : Fin ℓ → ℕ, β ∈ weightFinset ℓ τ →
      ∃ x : R, algebraMap R S x = (b : R) • C β := by
    intro β hβ
    have hmem_img : C β ∈ (weightFinset ℓ τ).image C := Finset.mem_image_of_mem C hβ
    have h := hb (C β) hmem_img
    rw [IsLocalization.IsInteger] at h
    exact h
  obtain ⟨x, hx⟩ : ∃ x : (Fin ℓ → ℕ) → R,
      ∀ β (h : β ∈ weightFinset ℓ τ), algebraMap R S (x β) = (b : R) • C β := by
    refine ⟨fun β => if h : β ∈ weightFinset ℓ τ then Classical.choose (hb' β h) else 0, ?_⟩
    intro β h
    simp only [dif_pos h]
    exact Classical.choose_spec (hb' β h)
  -- Multiplying the localized relation by `b` exhibits it as the image of an integral relation.
  have hkey : algebraMap R S (∑ β ∈ weightFinset ℓ τ, x β * monoPow u β)
      = (b : R) •
          (∑ β ∈ weightFinset ℓ τ, C β * monoPow (fun i => algebraMap R S (u i)) β) := by
    rw [map_weightedSum, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun β hβ => by
      rw [hx β hβ, Algebra.smul_def, Algebra.smul_def, mul_assoc])
  have hb_mem : (b : R) •
        (∑ β ∈ weightFinset ℓ τ, C β * monoPow (fun i => algebraMap R S (u i)) β)
      ∈ Ideal.map (algebraMap R S) J + (Ideal.map (algebraMap R S) 𝔓) ^ (τ + 1) := by
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ (algebraMap R S (b : R)) hmem
  have hI_eq : Ideal.map (algebraMap R S) (J + 𝔓 ^ (τ + 1))
      = Ideal.map (algebraMap R S) J + (Ideal.map (algebraMap R S) 𝔓) ^ (τ + 1) := by
    change Ideal.map (algebraMap R S) (J ⊔ 𝔓 ^ (τ + 1))
      = Ideal.map (algebraMap R S) J ⊔ (Ideal.map (algebraMap R S) 𝔓) ^ (τ + 1)
    rw [Ideal.map_sup, Ideal.map_pow]
  have hxmem : ∀ α ∈ weightFinset ℓ τ, x α ∈ 𝔓 := by
    refine hR x ?_
    rw [hkey, hI_eq]
    exact hb_mem
  intro α hα
  have h1 : algebraMap R S (x α) ∈ Ideal.map (algebraMap R S) 𝔓 :=
    Ideal.mem_map_of_mem (algebraMap R S) (hxmem α hα)
  rw [hx α hα] at h1
  -- `algebraMap b` is a unit of `S`, so we may divide the membership by it.
  obtain ⟨v, hv⟩ := IsLocalization.map_units S b
  have hCα : C α = (↑(v⁻¹) : S) * ((b : R) • C α) := by
    rw [Algebra.smul_def, ← hv, ← mul_assoc, Units.inv_mul, one_mul]
  rw [hCα]
  exact Ideal.mul_mem_left (Ideal.map (algebraMap R S) 𝔓) (↑(v⁻¹) : S) h1

end Work.BW
