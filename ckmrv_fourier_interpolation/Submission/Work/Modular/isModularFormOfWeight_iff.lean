import Mathlib
import Submission.Work.Modular.Basic

namespace Work.Modular

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

/-- Transporting a modular form along an equality of weights does not change the
underlying function. -/
lemma modularForm_coe_cast {k₁ k₂ : ℤ} (h : k₁ = k₂) (g : ModularForm 𝒮ℒ k₁) :
    ⇑(h ▸ g : ModularForm 𝒮ℒ k₂) = ⇑g := by
  cases h
  rfl

/-- A function `f : ℍ → ℂ` is a holomorphic modular form of weight `k` for `SL(2, ℤ)`
(in the depth-zero sense of `Work.Modular.IsModularFormOfWeight`) if and only if it is
the underlying function of a Mathlib `ModularForm 𝒮ℒ k`. -/
theorem isModularFormOfWeight_iff {k : ℤ} {f : ℍ → ℂ} :
    IsModularFormOfWeight k f ↔ ∃ g : ModularForm 𝒮ℒ k, ⇑g = f := by
  unfold IsModularFormOfWeight IsQuasiModularFormDepth
  constructor
  · rintro ⟨m, hm⟩
    have h : k - 2 * ((0 : Fin (0 + 1)) : ℤ) = k := by simp
    refine ⟨(h ▸ m 0 : ModularForm 𝒮ℒ k), ?_⟩
    rw [modularForm_coe_cast h, hm]
    rw [Fin.sum_univ_one]
    simp
  · rintro ⟨g, hg⟩
    have hj : ∀ j : Fin (0 + 1), k - 2 * (j : ℤ) = k := by
      intro j
      have hj0 : (j : ℤ) = 0 := by
        have h0 := Fin.eq_zero j
        rw [h0]; rfl
      rw [hj0]; simp
    refine ⟨fun j => ((hj j).symm ▸ g : ModularForm 𝒮ℒ (k - 2 * (j : ℤ))), ?_⟩
    rw [Fin.sum_univ_one, modularForm_coe_cast (hj 0).symm]
    simp only [Fin.val_zero, pow_zero, one_mul]
    exact hg.symm

end Work.Modular
