import Mathlib
import Submission.Work.Smooth.BoxGeneric.Defs

open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.BoxGeneric.Case

/-- On `Fin 3`, three pairwise distinct elements exhaust the type. -/
private lemma fin3_cover {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ i : Fin 3, i = a ∨ i = b ∨ i = c := by
  intro i
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases i <;> simp_all

/-- If a face norm equals `s`, one of the two opposite signed faces attains `s`. -/
private lemma exists_sign_of_faceNorm_eq {c : R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ} {i : Fin 3}
    {y : R3} (h : Work.Smooth.BoxGeneric.faceNorm c σ i y = s) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ Work.Smooth.BoxGeneric.faceLin c σ i ε y = s := by
  have habs : |Work.Smooth.BoxGeneric.signedFace c σ i y| = s := by
    rw [← Work.Smooth.BoxGeneric.faceNorm_eq_abs_signedFace]; exact h
  rcases lt_or_ge (Work.Smooth.BoxGeneric.signedFace c σ i y) 0 with hlt | hge
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [Work.Smooth.BoxGeneric.faceLin_neg_one]
    rw [abs_of_neg hlt] at habs
    linarith
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [Work.Smooth.BoxGeneric.faceLin_one]
    rwa [abs_of_nonneg hge] at habs

theorem exists_active_signed_of_not_vertex {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ} {y : LeanEval.KnotTheory.PardonDistortion.R3} (hs : 0 < s) (hbox : Submission.boxNorm c σ y = s) (hnv : ¬ Work.Smooth.BoxGeneric.IsBoxVertexPoint c σ s y) : (∃ (i : Fin 3) (ε : ℝ), (ε = 1 ∨ ε = -1) ∧ Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε y ∧ ∀ j : Fin 3, j ≠ i → Work.Smooth.BoxGeneric.faceNorm c σ j y < s) ∨ (∃ (i j : Fin 3) (ε ε' : ℝ), i ≠ j ∧ (ε = 1 ∨ ε = -1) ∧ (ε' = 1 ∨ ε' = -1) ∧ Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε y ∧ Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s j ε' y ∧ ∀ k : Fin 3, k ≠ i → k ≠ j → Work.Smooth.BoxGeneric.faceNorm c σ k y < s) := by
  -- some face is active (its norm equals the box norm `s`)
  obtain ⟨i0, hi0⟩ := Work.Smooth.BoxGeneric.exists_faceNorm_eq_boxNorm c σ y
  have hi0s : Work.Smooth.BoxGeneric.faceNorm c σ i0 y = s := by rw [hi0, hbox]
  -- every face norm is at most `s`
  have hle : ∀ i : Fin 3, Work.Smooth.BoxGeneric.faceNorm c σ i y ≤ s := fun i => by
    rw [← hbox]; exact Work.Smooth.BoxGeneric.faceNorm_le_boxNorm c σ i y
  -- packaging: an active signed face only needs the signed face to equal `s`
  have hmk : ∀ (i : Fin 3) (ε : ℝ),
      Work.Smooth.BoxGeneric.faceLin c σ i ε y = s →
      Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε y :=
    fun i ε h => ⟨h, hle⟩
  by_cases hsecond : ∃ j : Fin 3, j ≠ i0 ∧ Work.Smooth.BoxGeneric.faceNorm c σ j y = s
  · -- two distinct active faces `i0`, `j`; the remaining face is strictly inactive
    obtain ⟨j, hji, hjs⟩ := hsecond
    have hthird : ∀ k : Fin 3, k ≠ i0 → k ≠ j →
        Work.Smooth.BoxGeneric.faceNorm c σ k y < s := by
      intro k hki hkj
      refine lt_of_le_of_ne (hle k) (fun hk => ?_)
      -- if `k` were active too, all three faces would be active: `y` would be a vertex
      apply hnv
      intro i
      rcases fin3_cover (a := i0) (b := j) (c := k) (Ne.symm hji) (Ne.symm hki) (Ne.symm hkj) i with
        h | h | h
      · rw [h]; exact hi0s
      · rw [h]; exact hjs
      · rw [h]; exact hk
    obtain ⟨ε, hε, hεs⟩ := exists_sign_of_faceNorm_eq hi0s
    obtain ⟨ε', hε', hε's⟩ := exists_sign_of_faceNorm_eq hjs
    exact Or.inr ⟨i0, j, ε, ε', Ne.symm hji, hε, hε', hmk i0 ε hεs, hmk j ε' hε's, hthird⟩
  · -- `i0` is the unique active face
    have huniq : ∀ j : Fin 3, j ≠ i0 → Work.Smooth.BoxGeneric.faceNorm c σ j y < s := by
      intro j hj
      exact lt_of_le_of_ne (hle j) (fun hj' => hsecond ⟨j, hj, hj'⟩)
    obtain ⟨ε, hε, hεs⟩ := exists_sign_of_faceNorm_eq hi0s
    exact Or.inl ⟨i0, ε, hε, hmk i0 ε hεs, huniq⟩

end Work.Smooth.BoxGeneric.Case
