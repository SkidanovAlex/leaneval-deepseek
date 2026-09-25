import Mathlib
import Submission.Work.Tower.FrattiniLayer.Basic

namespace Work.Tower.FrattiniLayer

/-- **The Frattini layer separates the cubic layer from the quadratic one.**

If `E₁, E₂` are cubic everywhere unramified Galois extensions of `F` inside `Ω`, and `L/F` is a
quadratic Galois extension, then `E₁ ⊔ L = E₂ ⊔ L` forces `E₁ = E₂`.

The point is that `E₁/F` (degree `3`) and `L/F` (degree `2`) are linearly disjoint, so
`[E₁ ⊔ L : F] = 6`: the compositum `E₁ · L` is a *degree `6`* extension of `F`, and it contains
`E₂`. Were `E₁ ≠ E₂`, the two degree-`3` fields would meet in `F`, hence be linearly disjoint,
so `E₁ ⊔ E₂` would have degree `9` over `F`; but `E₁ ⊔ E₂ ≤ E₁ ⊔ L` forces `9 ∣ 6`. -/
theorem sup_left_injective {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (L : IntermediateField F Ω) [IsGalois F L] (hL : Module.finrank F L = 2)
    {E₁ E₂ : IntermediateField F Ω}
    (h1 : Work.Tower.FrattiniLayer.IsCubicUnramified F Ω E₁)
    (h2 : Work.Tower.FrattiniLayer.IsCubicUnramified F Ω E₂)
    (h : E₁ ⊔ L = E₂ ⊔ L) : E₁ = E₂ := by
  obtain ⟨hE1, hG1, -⟩ := h1
  obtain ⟨hE2, -, -⟩ := h2
  -- `E₁/F` and `E₂/F` are finite (they have degree `3`).
  have : FiniteDimensional F ↥E₁ := Module.finite_of_finrank_pos (by rw [hE1]; norm_num)
  have : FiniteDimensional F ↥E₂ := Module.finite_of_finrank_pos (by rw [hE2]; norm_num)
  have : IsGalois F ↥E₁ := hG1
  -- Coprime degrees `3` and `2` make `E₁` and `L` linearly disjoint, so `[E₁ ⊔ L : F] = 6`.
  have hdisj1 : E₁.LinearDisjoint L :=
    IntermediateField.LinearDisjoint.of_finrank_coprime (by rw [hE1, hL]; decide)
  have hM6 : Module.finrank F ↥(E₁ ⊔ L) = 6 := by
    have h6 := hdisj1.finrank_sup
    rw [hE1, hL] at h6
    omega
  by_contra hne
  -- Two distinct degree-`3` subfields of the compositum meet in `F` (as `3` is prime).
  have hKbot : E₁ ⊓ E₂ = ⊥ := by
    have hdvd : Module.finrank F ↥(E₁ ⊓ E₂) ∣ 3 := by
      have hd := IntermediateField.finrank_dvd_of_le_right (F := E₁ ⊓ E₂) (E := E₁) inf_le_left
      rwa [hE1] at hd
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd with h1' | h3'
    · exact IntermediateField.finrank_eq_one_iff.mp h1'
    · exfalso
      apply hne
      have hKE : E₁ ⊓ E₂ = E₁ :=
        IntermediateField.eq_of_le_of_finrank_eq (F := E₁ ⊓ E₂) (E := E₁) inf_le_left
          (by rw [h3', hE1])
      have hle : E₁ ≤ E₂ := hKE ▸ inf_le_right
      exact IntermediateField.eq_of_le_of_finrank_eq (F := E₁) (E := E₂) hle (by rw [hE1, hE2])
  -- Hence they are linearly disjoint, so `[E₁ ⊔ E₂ : F] = 9`.
  have hdisj2 : E₁.LinearDisjoint E₂ := IntermediateField.LinearDisjoint.of_inf_eq_bot hKbot
  have hE9 : Module.finrank F ↥(E₁ ⊔ E₂) = 9 := by
    have h9 := hdisj2.finrank_sup
    rw [hE1, hE2] at h9
    omega
  -- But `E₁ ⊔ E₂ ≤ E₁ ⊔ L`, forcing `9 ∣ 6`.
  have hKM : E₁ ⊔ E₂ ≤ E₁ ⊔ L := sup_le le_sup_left (le_sup_left.trans_eq h.symm)
  have hdvd := IntermediateField.finrank_dvd_of_le_right (F := E₁ ⊔ E₂) (E := E₁ ⊔ L) hKM
  rw [hE9, hM6] at hdvd
  exact absurd hdvd (by decide)

end Work.Tower.FrattiniLayer
