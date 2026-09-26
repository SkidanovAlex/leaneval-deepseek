import Mathlib
import Submission.Work.Modular.Basic

namespace Work.Modular

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

/-- Transporting a modular form along an equality of weights does not change the
underlying function. -/
private lemma coe_cast_weight' {k₁ k₂ : ℤ} (h : k₁ = k₂) (g : ModularForm 𝒮ℒ k₁) :
    ⇑(h ▸ g : ModularForm 𝒮ℒ k₂) = ⇑g := by
  subst h
  rfl

/-- A function is a quasimodular form of weight `k` and depth at most `1` iff it is the sum of a
modular form of weight `k` and `E₂` times a modular form of weight `k - 2`. -/
theorem isQuasiModularForm_iff {k : ℤ} {f : ℍ → ℂ} :
    IsQuasiModularForm k f ↔ ∃ m0 : ModularForm 𝒮ℒ k, ∃ m1 : ModularForm 𝒮ℒ (k - 2),
      f = ⇑m0 + E2 * ⇑m1 := by
  constructor
  · -- Forward: read off the two summands of the representing sum.
    rintro ⟨m, hm⟩
    have hw : k - 2 * ((0 : Fin 2) : ℤ) = k := by norm_num
    refine ⟨(hw ▸ m 0 : ModularForm 𝒮ℒ k), (m 1), ?_⟩
    rw [coe_cast_weight' hw, hm, Fin.sum_univ_two]
    simp
  · -- Backward: assemble the two modular forms into a `Fin 2`-indexed family.
    rintro ⟨m0, m1, hf⟩
    have hw0 : ∀ {j : Fin 2}, (j : ℕ) = 0 → k - 2 * (j : ℤ) = k := by
      intro j hj
      have h : ((j : ℕ) : ℤ) = 0 := by rw [hj]; rfl
      rw [h]; ring
    have hw1 : ∀ {j : Fin 2}, (j : ℕ) ≠ 0 → k - 2 * (j : ℤ) = k - 2 := by
      intro j hj
      have hjlt : (j : ℕ) < 2 := j.isLt
      have h1 : (j : ℕ) = 1 := by omega
      have h : ((j : ℕ) : ℤ) = 1 := by rw [h1]; rfl
      rw [h]; ring
    let m : (j : Fin 2) → ModularForm 𝒮ℒ (k - 2 * (j : ℤ)) :=
      fun j => if hj : (j : ℕ) = 0 then (hw0 hj).symm ▸ m0 else (hw1 hj).symm ▸ m1
    refine ⟨m, ?_⟩
    have hz : ((0 : Fin 2) : ℕ) = 0 := by decide
    have ho : ((1 : Fin 2) : ℕ) = 1 := by decide
    have hm0 : ⇑(m 0) = ⇑m0 := by
      have he : m 0 = (hw0 hz).symm ▸ m0 := by
        simp only [m]
        rw [dif_pos hz]
      rw [he]
      exact coe_cast_weight' _ m0
    have hm1 : ⇑(m 1) = ⇑m1 := by
      have hne : ¬ ((1 : Fin 2) : ℕ) = 0 := by decide
      have he : m 1 = (hw1 hne).symm ▸ m1 := by
        simp only [m]
        rw [dif_neg hne]
      rw [he]
    rw [hf, Fin.sum_univ_two, hm0, hm1, hz, ho]
    simp

end Work.Modular
