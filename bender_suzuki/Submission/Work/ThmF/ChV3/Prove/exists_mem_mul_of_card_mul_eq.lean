import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

/-- If `K` and `V` are subgroups of `D` with `K ⊓ V = ⊥` and
`|K| * |V| = |D|`, then every element of `D` is a product `k * v`
with `k ∈ K`, `v ∈ V`. -/
theorem exists_mem_mul_of_card_mul_eq {G : Type} [Group G] [Finite G] {D K V : Subgroup G}
    (hK : K ≤ D) (hV : V ≤ D) (hinf : K ⊓ V = ⊥)
    (hcard : Nat.card ↥K * Nat.card ↥V = Nat.card ↥D) :
    ∀ y ∈ D, ∃ k ∈ K, ∃ v ∈ V, y = k * v := by
  classical
  have : Fintype ↥K := Fintype.ofFinite _
  have : Fintype ↥V := Fintype.ofFinite _
  have : Fintype ↥D := Fintype.ofFinite _
  -- The multiplication map `K × V → D`, which is injective because `K ⊓ V = ⊥`.
  let f : ↥K × ↥V → ↥D := fun p => ⟨(p.1 : G) * (p.2 : G),
    D.mul_mem (hK p.1.2) (hV p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨k₁, v₁⟩ ⟨k₂, v₂⟩ h
    have h' : (k₁ : G) * (v₁ : G) = (k₂ : G) * (v₂ : G) := by
      have := congrArg (fun z : ↥D => (z : G)) h
      simpa [f] using this
    have hkey : (k₂ : G)⁻¹ * (k₁ : G) = (v₂ : G) * (v₁ : G)⁻¹ := by
      have h2 := congrArg (fun x : G => (k₂ : G)⁻¹ * x * (v₁ : G)⁻¹) h'
      simpa [mul_assoc] using h2
    have hmem : (k₂ : G)⁻¹ * (k₁ : G) ∈ K ⊓ V := by
      refine ⟨K.mul_mem (K.inv_mem k₂.2) k₁.2, ?_⟩
      rw [hkey]
      exact V.mul_mem v₂.2 (V.inv_mem v₁.2)
    have hbot : (k₂ : G)⁻¹ * (k₁ : G) = 1 := by
      have hh := hmem
      rw [hinf] at hh
      exact Subgroup.mem_bot.mp hh
    have hk : k₁ = k₂ := Subtype.ext (inv_mul_eq_one.mp hbot).symm
    have hv : v₁ = v₂ := by
      apply Subtype.ext
      rw [hk] at h'
      exact mul_left_cancel h'
    rw [hk, hv]
  -- Domain and codomain have the same cardinality, so `f` is also surjective.
  have hfcard : Fintype.card (↥K × ↥V) = Fintype.card ↥D := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    rw [Nat.card_prod]
    exact hcard
  have himg : (Finset.univ.image f).card = Fintype.card ↥D := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, hfcard]
  have huniv : (Finset.univ.image f : Finset ↥D) = Finset.univ :=
    Finset.eq_univ_of_card _ himg
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥D) ∈ (Finset.univ.image f : Finset ↥D) := by
    rw [huniv]; exact Finset.mem_univ _
  rw [Finset.mem_image] at hy'
  obtain ⟨p, _, hp⟩ := hy'
  refine ⟨p.1, p.1.2, p.2, p.2.2, ?_⟩
  have hh := congrArg (fun z : ↥D => (z : G)) hp
  simpa [f] using hh.symm

end Work.ThmF.ChV3.Prove
