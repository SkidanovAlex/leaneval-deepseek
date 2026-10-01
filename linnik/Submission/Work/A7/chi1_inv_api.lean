import Mathlib
import Submission.Work.A7.zeroMult_conj_inv
import Submission.Work.A7.lamChar_api

namespace Work.A7

open DirichletCharacter Complex

set_option linter.style.haveILetI false

/-- `λ(ρ) = (1 - Re ρ) log q` is invariant under complex conjugation. -/
lemma lamOf_star (q : ℕ) (ρ : ℂ) :
    Work.LinnikContract.lamOf q ((starRingEnd ℂ) ρ) = Work.LinnikContract.lamOf q ρ := by
  simp [Work.LinnikContract.lamOf]

/-- The absolute value of the imaginary part is invariant under complex conjugation. -/
lemma abs_im_star (ρ : ℂ) : |((starRingEnd ℂ) ρ).im| = |ρ.im| := by
  simp

/-- Membership in HB's working region passes to the inverse character and the conjugate zero. -/
lemma isZ_inv_star {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : Work.LinnikContract.IsZ χ ρ) :
    Work.LinnikContract.IsZ χ⁻¹ ((starRingEnd ℂ) ρ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hc
    exact h.1 (inv_eq_one.mp hc)
  · rw [Work.A7.zeroMult_conj_inv χ ρ]
    exact h.2.1
  · rw [abs_im_star]
    exact h.2.2

/-- Converse direction:  a zero of `χ⁻¹` conjugates back to a zero of `χ`. -/
lemma isZ_star_inv {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : Work.LinnikContract.IsZ χ⁻¹ ρ) :
    Work.LinnikContract.IsZ χ ((starRingEnd ℂ) ρ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hc
    exact h.1 (by rw [hc, inv_one])
  · have hh : Work.LinnikContract.zeroMult χ⁻¹ ρ =
        Work.LinnikContract.zeroMult χ ((starRingEnd ℂ) ρ) := by
      simpa using Work.A7.zeroMult_conj_inv χ ((starRingEnd ℂ) ρ)
    rw [← hh]
    exact h.2.1
  · rw [abs_im_star]
    exact h.2.2

theorem chi1_inv_api {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {c : ℝ}
    (hmin : Work.LinnikContract.IsMin1 χ₁ ρ₁) (h0 : Work.LinnikContract.Lam0Bound χ₁ ρ₁ c) :
    (Work.LinnikContract.lamChar χ₁⁻¹ = Work.LinnikContract.lamOf q ρ₁) ∧
    (Work.LinnikContract.IsZ χ₁⁻¹ ((starRingEnd ℂ) ρ₁)) ∧
    (Work.LinnikContract.zeroMult χ₁⁻¹ ((starRingEnd ℂ) ρ₁) = Work.LinnikContract.zeroMult χ₁ ρ₁) ∧
    (Work.LinnikContract.lamOf q ((starRingEnd ℂ) ρ₁) = Work.LinnikContract.lamOf q ρ₁) ∧
    (Work.LinnikContract.Lam0Bound χ₁⁻¹ ((starRingEnd ℂ) ρ₁) c) ∧
    (∀ R : ℝ, Work.LinnikContract.InBox q R ρ₁ → Work.LinnikContract.InBox q R ((starRingEnd ℂ) ρ₁)) := by
  obtain ⟨hIsZ, hmin'⟩ := hmin
  obtain ⟨h0a, h0b⟩ := h0
  have hIsZ' : Work.LinnikContract.IsZ χ₁⁻¹ ((starRingEnd ℂ) ρ₁) := isZ_inv_star hIsZ
  have hlam_star : Work.LinnikContract.lamOf q ((starRingEnd ℂ) ρ₁) =
      Work.LinnikContract.lamOf q ρ₁ := lamOf_star q ρ₁
  have hzm : Work.LinnikContract.zeroMult χ₁⁻¹ ((starRingEnd ℂ) ρ₁) =
      Work.LinnikContract.zeroMult χ₁ ρ₁ := Work.A7.zeroMult_conj_inv χ₁ ρ₁
  refine ⟨?_, hIsZ', hzm, hlam_star, ?_, ?_⟩
  · -- the least zero-parameter of `χ₁⁻¹` is attained at `conj ρ₁`
    apply le_antisymm
    · calc Work.LinnikContract.lamChar χ₁⁻¹
          ≤ Work.LinnikContract.lamOf q ((starRingEnd ℂ) ρ₁) := lamChar_le_lamOf hq hIsZ'
        _ = Work.LinnikContract.lamOf q ρ₁ := hlam_star
    · have hne : (lamSet χ₁⁻¹).Nonempty :=
        ⟨Work.LinnikContract.lamOf q ((starRingEnd ℂ) ρ₁), ⟨(starRingEnd ℂ) ρ₁, hIsZ', rfl⟩⟩
      rw [lamChar_eq_sInf_lamSet]
      exact le_csInf hne (by
        rintro x ⟨ρ, hZρ, rfl⟩
        exact hmin' χ₁⁻¹ ρ hZρ)
  · -- `Lam0Bound` transfers across `χ ↦ χ⁻¹`, `ρ ↦ conj ρ`
    refine ⟨?_, ?_⟩
    · intro h2
      rw [hzm] at h2
      rw [hlam_star]
      exact h0a h2
    · intro ρ hZρ hne hreal
      have hZ1 : Work.LinnikContract.IsZ χ₁ ((starRingEnd ℂ) ρ) := isZ_star_inv hZρ
      have hne' : (starRingEnd ℂ) ρ ≠ ρ₁ := by
        intro h
        apply hne
        have := congrArg (starRingEnd ℂ) h
        simpa using this
      have hreal' : χ₁ ^ 2 = 1 → (starRingEnd ℂ) ρ ≠ (starRingEnd ℂ) ρ₁ := by
        intro hχ hc
        have hInv : (χ₁⁻¹) ^ 2 = 1 := by rw [inv_pow, hχ, inv_one]
        have hρρ₁ : ρ ≠ ρ₁ := by simpa using hreal hInv
        apply hρρ₁
        have := congrArg (starRingEnd ℂ) hc
        simpa using this
      have := h0b ((starRingEnd ℂ) ρ) hZ1 hne' hreal'
      rwa [lamOf_star q ρ] at this
  · -- `InBox` is conjugation-invariant
    intro R hR
    exact ⟨by rw [hlam_star]; exact hR.1, by rw [abs_im_star]; exact hR.2⟩

end Work.A7
