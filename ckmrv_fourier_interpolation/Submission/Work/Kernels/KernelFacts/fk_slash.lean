import Mathlib
import Submission.Work.Kernels.Kernels

/-!
# Invariance of the functions `f_k` under the slash action

The functions `f_k` of CKMRV Section 4.4 are the classical modular forms

  `f_{-2} = E₁₀/Δ`, `f_0 = 1`, `f_2 = E₁₄/Δ`, `f_4 = E₄`, `f_6 = E₆`, `f_8 = E₈ = E₄²`,
  `f_{10} = E₁₀ = E₄E₆`, `f_{12} = Δ`, `f_{14} = E₁₄ = E₄²E₆`

of weights `-2, 0, 2, 4, 6, 8, 10, 12, 14`, so each of them is slash-invariant in its own
weight.  This file records that invariance, `SlashAction.map k γ (f_k) = f_k`, for `γ ∈ SL(2,ℤ)`
and `k` in that list.
-/

namespace Work.Kernels.KernelFacts

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

/-- `mapGL ℝ γ` is the image in `GL(2,ℝ)` of `γ ∈ SL(2,ℤ)`; it lies in `𝒮ℒ`. -/
lemma memSLO (γ : SL(2, ℤ)) : Matrix.SpecialLinearGroup.mapGL ℝ γ ∈ 𝒮ℒ :=
  MonoidHom.mem_range.mpr ⟨γ, rfl⟩

lemma E4Fun_slash (γ : SL(2, ℤ)) :
    SlashAction.map (4:ℤ) γ Work.Kernels.E4Fun = Work.Kernels.E4Fun :=
  SlashInvariantForm.slash_action_eqn _ _ (memSLO γ)

lemma E6Fun_slash (γ : SL(2, ℤ)) :
    SlashAction.map (6:ℤ) γ Work.Kernels.E6Fun = Work.Kernels.E6Fun :=
  SlashInvariantForm.slash_action_eqn _ _ (memSLO γ)

lemma DeltaFun_slash (γ : SL(2, ℤ)) :
    SlashAction.map (12:ℤ) γ Work.Kernels.DeltaFun = Work.Kernels.DeltaFun :=
  SlashInvariantForm.slash_action_eqn _ _ (memSLO γ)

lemma one_slash (γ : SL(2, ℤ)) :
    SlashAction.map (0:ℤ) γ (1 : ℍ → ℂ) = 1 :=
  ModularForm.is_invariant_one γ

/-- The product of two slash-invariant functions is slash-invariant in the sum of the weights. -/
lemma mul_slash_inv {k1 k2 : ℤ} (γ : SL(2, ℤ)) {f g : ℍ → ℂ}
    (hf : SlashAction.map k1 γ f = f) (hg : SlashAction.map k2 γ g = g) :
    SlashAction.map (k1 + k2) γ (f * g) = f * g := by
  rw [ModularForm.mul_slash_SL2, hf, hg]

/-- The quotient of two slash-invariant functions is slash-invariant in the difference of the
weights. -/
lemma div_slash_inv {k1 k2 : ℤ} (γ : SL(2, ℤ)) {f g : ℍ → ℂ}
    (hf : SlashAction.map k1 γ f = f) (hg : SlashAction.map k2 γ g = g) :
    SlashAction.map (k1 - k2) γ (f / g) = f / g := by
  rw [ModularForm.div_slash_SL2, hf, hg]

lemma E8Fun_slash (γ : SL(2, ℤ)) :
    SlashAction.map (8:ℤ) γ Work.Kernels.E8Fun = Work.Kernels.E8Fun := by
  have h : Work.Kernels.E8Fun = Work.Kernels.E4Fun * Work.Kernels.E4Fun := by
    funext τ; simp [Work.Kernels.E8Fun, pow_two]
  rw [h]
  simpa using mul_slash_inv γ (k1 := 4) (k2 := 4) (E4Fun_slash γ) (E4Fun_slash γ)

lemma E10Fun_slash (γ : SL(2, ℤ)) :
    SlashAction.map (10:ℤ) γ Work.Kernels.E10Fun = Work.Kernels.E10Fun := by
  have h : Work.Kernels.E10Fun = Work.Kernels.E4Fun * Work.Kernels.E6Fun := by
    funext τ; simp [Work.Kernels.E10Fun]
  rw [h]
  simpa using mul_slash_inv γ (k1 := 4) (k2 := 6) (E4Fun_slash γ) (E6Fun_slash γ)

lemma E14Fun_slash (γ : SL(2, ℤ)) :
    SlashAction.map (14:ℤ) γ Work.Kernels.E14Fun = Work.Kernels.E14Fun := by
  have h : Work.Kernels.E14Fun = Work.Kernels.E8Fun * Work.Kernels.E6Fun := by
    funext τ; simp [Work.Kernels.E14Fun, Work.Kernels.E8Fun, pow_two]
  rw [h]
  simpa using mul_slash_inv γ (k1 := 8) (k2 := 6) (E8Fun_slash γ) (E6Fun_slash γ)

lemma E10DivDelta_slash (γ : SL(2, ℤ)) :
    SlashAction.map (-2:ℤ) γ (Work.Kernels.E10Fun / Work.Kernels.DeltaFun)
      = Work.Kernels.E10Fun / Work.Kernels.DeltaFun := by
  simpa using div_slash_inv γ (k1 := 10) (k2 := 12) (E10Fun_slash γ) (DeltaFun_slash γ)

lemma E14DivDelta_slash (γ : SL(2, ℤ)) :
    SlashAction.map (2:ℤ) γ (Work.Kernels.E14Fun / Work.Kernels.DeltaFun)
      = Work.Kernels.E14Fun / Work.Kernels.DeltaFun := by
  simpa using div_slash_inv γ (k1 := 14) (k2 := 12) (E14Fun_slash γ) (DeltaFun_slash γ)

lemma fk_neg_two : Work.Kernels.fk (-2) = Work.Kernels.E10Fun / Work.Kernels.DeltaFun := by
  funext τ; simp [Work.Kernels.fk]

lemma fk_zero : Work.Kernels.fk (0:ℤ) = (1 : ℍ → ℂ) := by
  funext τ; simp [Work.Kernels.fk]

lemma fk_two : Work.Kernels.fk (2:ℤ) = Work.Kernels.E14Fun / Work.Kernels.DeltaFun := by
  funext τ; simp [Work.Kernels.fk]

lemma fk_four : Work.Kernels.fk (4:ℤ) = Work.Kernels.E4Fun := by
  funext τ; simp [Work.Kernels.fk]

lemma fk_six : Work.Kernels.fk (6:ℤ) = Work.Kernels.E6Fun := by
  funext τ; simp [Work.Kernels.fk]

lemma fk_eight : Work.Kernels.fk (8:ℤ) = Work.Kernels.E8Fun := by
  funext τ; simp [Work.Kernels.fk]

lemma fk_ten : Work.Kernels.fk (10:ℤ) = Work.Kernels.E10Fun := by
  funext τ; simp [Work.Kernels.fk]

lemma fk_twelve : Work.Kernels.fk (12:ℤ) = Work.Kernels.DeltaFun := by
  funext τ; simp [Work.Kernels.fk]

lemma fk_fourteen : Work.Kernels.fk (14:ℤ) = Work.Kernels.E14Fun := by
  funext τ; simp [Work.Kernels.fk]

theorem fk_slash (k : ℤ)
    (hk : k = -2 ∨ k = 0 ∨ k = 2 ∨ k = 4 ∨ k = 6 ∨ k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 14)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    SlashAction.map k γ (Work.Kernels.fk k) = Work.Kernels.fk k := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [fk_neg_two]; exact E10DivDelta_slash γ
  · rw [fk_zero]; exact one_slash γ
  · rw [fk_two]; exact E14DivDelta_slash γ
  · rw [fk_four]; exact E4Fun_slash γ
  · rw [fk_six]; exact E6Fun_slash γ
  · rw [fk_eight]; exact E8Fun_slash γ
  · rw [fk_ten]; exact E10Fun_slash γ
  · rw [fk_twelve]; exact DeltaFun_slash γ
  · rw [fk_fourteen]; exact E14Fun_slash γ

end Work.Kernels.KernelFacts
