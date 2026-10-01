/-
# LinnikContract2 — `A7/WindowAPI.lean`

Helpers for ROUND 2's **window**: the sub-case of HB §15 in which the numbered (wide) minimiser
`ρ₁` does *not* lie in the working region (`¬ IsZ χ₁ ρ₁`).  In that branch the §15 argument is run
with the *narrow* (working-region) minimiser `(χ₀,ρ₀)` as the decay pivot — which does lie in the
working region (`IsMin1N` unfolds to round 1's `IsMin1`, hence `IsZ`), so round 1's §15 machinery
applies to it verbatim — while the counting rows of Table 13 are those opened by the wide `λ₁`,
through round 2's `(D2)` whose hypothesis is the wide one.
-/
import Mathlib
import Submission.Work.A7.sec15_uniform
import Submission.Work.A7.sec15_helper
import Submission.Work.A7.box_api7
import Submission.Work.A7.chi1_inv_api
import Submission.Work.A7.zeroMult_conj_sq_one
import Submission.Work.LinnikAreas.A7.WBox
import Submission.Work.LinnikAreas.A7.Basic7
import Submission.Work.LinnikAreas.A7.ValueLemmas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikContract2.A7

open Work.LinnikContract (IsMin1 Lam0Bound Lam2Bound Lam3Bound IsZ lamOf Ncount)

/-- For a real (quadratic) character, `IsZ χ (conj ρ)` implies `IsZ χ ρ`. -/
lemma isZ_conj_sq_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (hsq : χ ^ 2 = 1) (h : IsZ χ ((starRingEnd ℂ) ρ)) : IsZ χ ρ :=
  ⟨h.1, by simpa [Work.A7.zeroMult_conj_sq_one χ hsq ρ] using h.2.1,
    by rw [← Work.A7.abs_im_star ρ]; exact h.2.2⟩

/-- `¬ IsZ χ₁ ρ₁` transfers to the inverse character at the conjugate zero. -/
lemma not_isZ_conj_inv {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (hnZ : ¬ IsZ χ₁ ρ₁) : ¬ IsZ χ₁⁻¹ ((starRingEnd ℂ) ρ₁) :=
  fun h => hnZ (by simpa using Work.A7.isZ_star_inv h)

/-- The `λ`-value of a narrow zero `ρ` of `χ₁` which is neither `ρ₁` nor its conjugate is at
least `l₀`. -/
lemma lam0_of_narrow {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ ρ : ℂ} {l₀ : ℝ}
    (hL0 : Lam0Bound χ₁ ρ₁ l₀) (hZ : IsZ χ₁ ρ) (hρ : ρ ≠ ρ₁) (hnZ : ¬ IsZ χ₁ ρ₁) :
    l₀ ≤ lamOf q ρ :=
  hL0.2 ρ hZ hρ (fun hsq hconj => hnZ (isZ_conj_sq_one hsq (hconj ▸ hZ)))

/-- `Lam0Bound` transfers to the inverse character at the conjugate zero. -/
lemma lam0Bound_inv_of {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {l₀ : ℝ}
    (hL0 : Lam0Bound χ₁ ρ₁ l₀) : Lam0Bound χ₁⁻¹ ((starRingEnd ℂ) ρ₁) l₀ := by
  refine ⟨?_, ?_⟩
  · intro h2
    rw [Work.A7.zeroMult_conj_inv χ₁ ρ₁] at h2
    rw [Work.A7.lamOf_star]
    exact hL0.1 h2
  · intro ρ hZ hρ hsq
    have hZ' : IsZ χ₁ ((starRingEnd ℂ) ρ) := Work.A7.isZ_star_inv hZ
    have hρ' : (starRingEnd ℂ) ρ ≠ ρ₁ :=
      fun hc => hρ (by simpa using congrArg (starRingEnd ℂ) hc)
    have hthird : χ₁ ^ 2 = 1 → (starRingEnd ℂ) ρ ≠ (starRingEnd ℂ) ρ₁ :=
      fun hsq0 hc => hsq (by simpa [inv_pow] using hsq0)
        (by simpa using congrArg (starRingEnd ℂ) hc)
    have h := hL0.2 ((starRingEnd ℂ) ρ) hZ' hρ' hthird
    rwa [Work.A7.lamOf_star] at h

/-- **The second clause at the narrow pivot.** -/
lemma lam2Bound_narrow_of_wide {q : ℕ} [NeZero q]
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {χ₀ : DirichletCharacter ℂ q} {ρ₀ : ℂ} {l₀ l₂ : ℝ}
    (hL0 : Lam0Bound χ₁ ρ₁ l₀) (hL2 : Lam2Bound χ₁ l₂) (hl : l₂ ≤ l₀)
    (hnarrow : IsMin1 χ₀ ρ₀) (hnZ : ¬ IsZ χ₁ ρ₁) :
    Lam2Bound χ₀ l₂ := by
  by_cases hχ : χ₀ = χ₁
  · rw [hχ]; exact hL2
  by_cases hχ' : χ₀ = χ₁⁻¹
  · subst hχ'
    intro χ ρ hZ h1 h2
    exact hL2 χ ρ hZ (fun h => h2 (h.trans (inv_inv χ₁).symm)) (fun h => h1 h)
  · intro χ ρ hZ h1 h2
    by_cases hc : χ = χ₁
    · subst hc
      exact le_trans hl (lam0_of_narrow hL0 hZ (fun h => hnZ (h ▸ hZ)) hnZ)
    by_cases hc' : χ = χ₁⁻¹
    · subst hc'
      have h := lam0_of_narrow (χ₁ := χ₁⁻¹) (ρ₁ := (starRingEnd ℂ) ρ₁)
        (lam0Bound_inv_of hL0) hZ
        (fun hconj => not_isZ_conj_inv hnZ (hconj ▸ hZ))
        (not_isZ_conj_inv hnZ)
      exact le_trans hl h
    · exact hL2 χ ρ hZ (fun h => hc h) (fun h => hc' h)

/-- **The third clause at the narrow pivot.** -/
lemma lam3Bound_narrow_of_wide {q : ℕ} [NeZero q]
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {χ₀ : DirichletCharacter ℂ q} {ρ₀ : ℂ} {l₀ l₃ : ℝ}
    (hL0 : Lam0Bound χ₁ ρ₁ l₀) (hL3 : Lam3Bound χ₁ l₃)
    (hnarrow : IsMin1 χ₀ ρ₀) (hnZ : ¬ IsZ χ₁ ρ₁) :
    Lam3Bound χ₀ (min l₀ l₃) := by
  obtain ⟨χ₂, hχ₂⟩ := hL3
  by_cases hχ : χ₀ = χ₁
  · subst hχ
    exact ⟨χ₂, fun χ ρ hZ h1 h2 h3 h4 => le_trans (min_le_right _ _) (hχ₂ χ ρ hZ h1 h2 h3 h4)⟩
  by_cases hχ' : χ₀ = χ₁⁻¹
  · subst hχ'
    refine ⟨χ₂, fun χ ρ hZ h1 h2 h3 h4 =>
      le_trans (min_le_right _ _) (hχ₂ χ ρ hZ ?_ ?_ h3 h4)⟩
    · intro h; exact h2 (h.trans (inv_inv χ₁).symm)
    · intro h; exact h1 h
  · refine ⟨χ₂, fun χ ρ hZ h1 h2 h3 h4 => ?_⟩
    by_cases hc : χ = χ₁
    · subst hc
      exact le_trans (min_le_left _ _) (lam0_of_narrow hL0 hZ (fun h => hnZ (h ▸ hZ)) hnZ)
    by_cases hc' : χ = χ₁⁻¹
    · subst hc'
      have h := lam0_of_narrow (χ₁ := χ₁⁻¹) (ρ₁ := (starRingEnd ℂ) ρ₁)
        (lam0Bound_inv_of hL0) hZ
        (fun hconj => not_isZ_conj_inv hnZ (hconj ▸ hZ))
        (not_isZ_conj_inv hnZ)
      exact le_trans (min_le_left _ _) h
    · exact le_trans (min_le_right _ _) (hχ₂ χ ρ hZ (fun h => hc h) (fun h => hc' h) h3 h4)

/-- **The pivot's own level.**  At the narrow pivot `(χ₀,ρ₀)`, `λ(ρ₀) ≥ l₂`. -/
lemma lamOf_narrow_ge {q : ℕ} [NeZero q]
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {χ₀ : DirichletCharacter ℂ q} {ρ₀ : ℂ} {l₀ l₂ : ℝ}
    (hL0 : Lam0Bound χ₁ ρ₁ l₀) (hL2 : Lam2Bound χ₁ l₂) (hl : l₂ ≤ l₀)
    (hnarrow : IsMin1 χ₀ ρ₀) (hnZ : ¬ IsZ χ₁ ρ₁) : l₂ ≤ lamOf q ρ₀ := by
  by_cases hχ : χ₀ = χ₁
  · subst hχ
    exact le_trans hl (lam0_of_narrow hL0 hnarrow.1 (fun h => hnZ (h ▸ hnarrow.1)) hnZ)
  by_cases hχ' : χ₀ = χ₁⁻¹
  · subst hχ'
    have h := lam0_of_narrow (χ₁ := χ₁⁻¹) (ρ₁ := (starRingEnd ℂ) ρ₁)
      (lam0Bound_inv_of hL0) hnarrow.1
      (fun hconj => not_isZ_conj_inv hnZ (hconj ▸ hnarrow.1))
      (not_isZ_conj_inv hnZ)
    exact le_trans hl h
  · exact hL2 χ₀ ρ₀ hnarrow.1 (fun h => hχ h) (fun h => hχ' h)

/-- **The counting interface.**  The rows of Table 13 whose column `c` satisfies `c ≤ λ₁` are
available under the *narrow* zero-free hypothesis: the caller supplies the restricted `(D2)`
(round 2's `(D2)` has the *wide* hypothesis, discharged by the wide minimality with `c ≤ λ₁`). -/
lemma Ncount_le_table_w {q : ℕ} [NeZero q] {c lam₁ lam : ℝ} {χ₀ : DirichletCharacter ℂ q}
    {ρ₀ : ℂ} (hmin : IsMin1 χ₀ ρ₀) (hlam : lamOf q ρ₀ = lam) (hcol : c ≤ lam) (hc : c ≤ lam₁)
    (hD2 : ∀ e ∈ Work.LinnikContract.table13, e.2.1 ≤ lam₁ →
        (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → e.2.1 ≤ lamOf q ρ) →
        Ncount q e.1 ≤ e.2.2)
    {t : ℝ} {N : ℕ} (hmem : (t, c, N) ∈ Work.LinnikContract.table13) : Ncount q t ≤ N :=
  hD2 (t, c, N) hmem (by simpa using hc)
    (fun χ ρ hZ => le_trans hcol (hlam ▸ hmin.2 χ ρ hZ))

end Work.LinnikContract2.A7
