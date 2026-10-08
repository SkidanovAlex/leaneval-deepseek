import Mathlib
import Submission.Work.BG.CharBridge

namespace Work.BG

theorem singleCoincidence {G : Type*} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {a b c d : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1)
    {α β γ ζ : OddOrder.RepresentationTheory.ClassFunction G ℂ}
    (hα : α ∈ OddOrder.RepresentationTheory.irreducibleCharacters G)
    (hβ : β ∈ OddOrder.RepresentationTheory.irreducibleCharacters G)
    (hγ : γ ∈ OddOrder.RepresentationTheory.irreducibleCharacters G)
    (hζ : ζ ∈ OddOrder.RepresentationTheory.irreducibleCharacters G)
    (hαβ : α ≠ β) (hγζ : γ ≠ ζ)
    (h : (α = γ ∧ β ≠ ζ) ∨ (α = ζ ∧ β ≠ γ) ∨ (β = γ ∧ α ≠ ζ) ∨ (β = ζ ∧ α ≠ γ)) :
    OddOrder.RepresentationTheory.ClassFunction.inner ((a : ℂ) • α + (b : ℂ) • β)
        ((c : ℂ) • γ + (d : ℂ) • ζ) ≠ 0 := by
  classical
  -- Orthonormality of irreducible characters, in the two forms used below.
  have key_self : ∀ {χ : OddOrder.RepresentationTheory.ClassFunction G ℂ},
      OddOrder.RepresentationTheory.IsIrreducibleCharacter χ →
      OddOrder.RepresentationTheory.ClassFunction.inner χ χ = (1 : ℂ) := by
    intro χ hχ
    have := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨χ, hχ⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
      (⟨χ, hχ⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
    simpa using this
  have key_eq : ∀ {χ ψ : OddOrder.RepresentationTheory.ClassFunction G ℂ},
      OddOrder.RepresentationTheory.IsIrreducibleCharacter χ →
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ → χ = ψ →
      OddOrder.RepresentationTheory.ClassFunction.inner χ ψ = (1 : ℂ) := by
    intro χ ψ hχ hψ heq
    subst heq
    exact key_self hχ
  have key_ne : ∀ {χ ψ : OddOrder.RepresentationTheory.ClassFunction G ℂ},
      OddOrder.RepresentationTheory.IsIrreducibleCharacter χ →
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ → χ ≠ ψ →
      OddOrder.RepresentationTheory.ClassFunction.inner χ ψ = (0 : ℂ) := by
    intro χ ψ hχ hψ hne
    have hne' : (⟨χ, hχ⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter G) ≠
        ⟨ψ, hψ⟩ := fun hh => hne (Subtype.ext_iff.mp hh)
    have := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨χ, hχ⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
      (⟨ψ, hψ⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
    rw [ite_eq_right hne'] at this
    simpa using this
  -- A product of two elements of `{1, -1}` is nonzero in `ℂ`.
  have hprod : ∀ x y : ℤ, (x = 1 ∨ x = -1) → (y = 1 ∨ y = -1) →
      (x : ℂ) * (y : ℂ) ≠ 0 := by
    intro x y hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] <;> norm_num
  -- Bilinear expansion of the pairing.
  have expand : OddOrder.RepresentationTheory.ClassFunction.inner
        ((a : ℂ) • α + (b : ℂ) • β) ((c : ℂ) • γ + (d : ℂ) • ζ)
      = (a : ℂ) * star (c : ℂ) *
            OddOrder.RepresentationTheory.ClassFunction.inner α γ
        + (a : ℂ) * star (d : ℂ) *
            OddOrder.RepresentationTheory.ClassFunction.inner α ζ
        + (b : ℂ) * star (c : ℂ) *
            OddOrder.RepresentationTheory.ClassFunction.inner β γ
        + (b : ℂ) * star (d : ℂ) *
            OddOrder.RepresentationTheory.ClassFunction.inner β ζ := by
    simp only [OddOrder.RepresentationTheory.ClassFunction.inner_add_left,
      OddOrder.RepresentationTheory.ClassFunction.inner_add_right,
      OddOrder.RepresentationTheory.ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.ClassFunction.inner_smul_right]
    ring
  rcases h with ⟨hαγ, hβζne⟩ | ⟨hαζ, hβγne⟩ | ⟨hβγ, hαζne⟩ | ⟨hβζ, hαγne⟩
  · -- α = γ, β ≠ ζ
    have hαζ : α ≠ ζ := fun hh => hγζ (hαγ.symm.trans hh)
    have hβγ : β ≠ γ := fun hh => hαβ (hh.trans hαγ.symm).symm
    rw [expand, key_eq hα hγ hαγ, key_ne hα hζ hαζ, key_ne hβ hγ hβγ,
      key_ne hβ hζ hβζne]
    have hsc : star (c : ℂ) = (c : ℂ) := by simp
    rw [hsc]; simpa using hprod a c ha hc
  · -- α = ζ, β ≠ γ
    have hαγ : α ≠ γ := fun hh => hγζ (hαζ.symm.trans hh).symm
    have hβζ : β ≠ ζ := fun hh => hαβ (hh.trans hαζ.symm).symm
    rw [expand, key_ne hα hγ hαγ, key_eq hα hζ hαζ, key_ne hβ hγ hβγne,
      key_ne hβ hζ hβζ]
    have hsd : star (d : ℂ) = (d : ℂ) := by simp
    rw [hsd]; simpa using hprod a d ha hd
  · -- β = γ, α ≠ ζ
    have hαγ : α ≠ γ := fun hh => hαβ (hh.trans hβγ.symm)
    have hβζ : β ≠ ζ := fun hh => hγζ (hβγ.symm.trans hh)
    rw [expand, key_ne hα hγ hαγ, key_ne hα hζ hαζne, key_eq hβ hγ hβγ,
      key_ne hβ hζ hβζ]
    have hsc : star (c : ℂ) = (c : ℂ) := by simp
    rw [hsc]; simpa using hprod b c hb hc
  · -- β = ζ, α ≠ γ
    have hαζ : α ≠ ζ := fun hh => hαβ (hh.trans hβζ.symm)
    have hβγ : β ≠ γ := fun hh => hγζ (hβζ.symm.trans hh).symm
    rw [expand, key_ne hα hγ hαγne, key_ne hα hζ hαζ, key_ne hβ hγ hβγ,
      key_eq hβ hζ hβζ]
    have hsd : star (d : ℂ) = (d : ℂ) := by simp
    rw [hsd]; simpa using hprod b d hb hd

end Work.BG
