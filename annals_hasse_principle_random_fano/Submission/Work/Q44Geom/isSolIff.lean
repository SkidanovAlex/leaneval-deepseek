import Mathlib
import Submission.Work.Q44Geom.defs
import Submission.Work.Q44Geom.taylorDefs
import Submission.Work.Q44Geom.evalTaylorHom
import Submission.Work.Q44Geom.mapEvalSigma
import Submission.Work.Q44Geom.finSuccCoeff

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open MvPolynomial

namespace Work.Q44Geom

/-- The substitution `X i ↦ C (z i) * Y₀ + C (b₁ i) * Y₁ + C (b₂ i) * Y₂`. -/
def threeSubst (z b₁ b₂ : Fin 5 → ℚ) : Fin 5 → MvPolynomial (Fin 3) ℚ :=
  fun i => MvPolynomial.C (z i) * MvPolynomial.X 0 + MvPolynomial.C (b₁ i) * MvPolynomial.X 1
    + MvPolynomial.C (b₂ i) * MvPolynomial.X 2

theorem taylorHom_zero (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ)
    (f : MvPolynomial (Fin 5) ℚ)
    (hℓ : ∀ u : Fin 2 → ℚ, MvPolynomial.eval (u 0 • b₁ + u 1 • b₂) f = 0) :
    taylorHom 0 b₁ b₂ f = 0 := by
  apply MvPolynomial.funext
  intro u
  simp only [map_zero]
  have hpt0 : substPoint w b₁ b₂ 0 (0 : Fin 2 → ℚ) = 0 := by
    funext i; simp [substPoint]
  have hptu : substPoint w b₁ b₂ 0 u = u 0 • b₁ + u 1 • b₂ := by
    funext i; simp [substPoint, Pi.smul_apply, smul_eq_mul]
  rw [← hpt0, evalTaylorHom w b₁ b₂ f 0 u, hptu]
  exact hℓ u

theorem taylorHom_coeff_high (f : MvPolynomial (Fin 5) ℚ) (hf : f.IsHomogeneous 4)
    (z b₁ b₂ : Fin 5 → ℚ) (h0 : taylorHom 0 b₁ b₂ f = 0)
    (α : Fin 2 → ℕ) (hα : 4 ≤ α 0 + α 1) :
    (taylorHom z b₁ b₂ f).coeff (Finsupp.equivFunOnFinite.symm α) = 0 := by
  have hΨ : ∀ i, (threeSubst z b₁ b₂ i).IsHomogeneous 1 := by
    intro i
    simp only [threeSubst]
    exact (((isHomogeneous_X (R := ℚ) 0).C_mul (z i)).add
      ((isHomogeneous_X (R := ℚ) 1).C_mul (b₁ i))).add
      ((isHomogeneous_X (R := ℚ) 2).C_mul (b₂ i))
  have hG : (MvPolynomial.aeval (threeSubst z b₁ b₂) f).IsHomogeneous 4 := by
    simpa using hf.aeval (threeSubst z b₁ b₂) hΨ
  have hρ1f : MvPolynomial.aeval
        (fun k : Fin 3 => ![MvPolynomial.C (1 : ℚ), MvPolynomial.X 0, MvPolynomial.X 1] k)
        (MvPolynomial.aeval (threeSubst z b₁ b₂) f) = taylorHom z b₁ b₂ f := by
    have hρ1 : (MvPolynomial.aeval
          (fun k : Fin 3 => ![MvPolynomial.C (1 : ℚ), MvPolynomial.X 0, MvPolynomial.X 1] k)).comp
        (MvPolynomial.aeval (threeSubst z b₁ b₂)) = taylorHom z b₁ b₂ := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, taylorHom_X, threeSubst]
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      ring
    have hh := congrArg (fun (φ : MvPolynomial (Fin 5) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ) => φ f) hρ1
    simpa [AlgHom.comp_apply] using hh
  have hρ0f : MvPolynomial.aeval
        (fun k : Fin 3 => ![0, MvPolynomial.X 0, MvPolynomial.X 1] k)
        (MvPolynomial.aeval (threeSubst z b₁ b₂) f) = taylorHom 0 b₁ b₂ f := by
    have hρ0 : (MvPolynomial.aeval
          (fun k : Fin 3 => ![0, MvPolynomial.X 0, MvPolynomial.X 1] k)).comp
        (MvPolynomial.aeval (threeSubst z b₁ b₂)) = taylorHom 0 b₁ b₂ := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, taylorHom_X, threeSubst]
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      ring
    have hh := congrArg (fun (φ : MvPolynomial (Fin 5) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ) => φ f) hρ0
    simpa [AlgHom.comp_apply] using hh
  rw [← hρ1f, finSuccCoeff (MvPolynomial.aeval (threeSubst z b₁ b₂) f) 4 hG 1 α hα, hρ0f, h0]
  simp

theorem isSol_iff_levelForms_aux (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ)
    (f : MvPolynomial (Fin 5) ℚ) (hf : f.IsHomogeneous 4) (p : Fin 3 → ℚ)
    (h0 : taylorHom 0 b₁ b₂ f = 0) :
    (∀ u : Fin 2 → ℚ, MvPolynomial.eval (substPoint w b₁ b₂ p u) f = 0)
      ↔ ∀ α : Fin 2 → ℕ, α 0 + α 1 ≤ 3 →
          MvPolynomial.eval p (levelForm w b₁ b₂ f α) = 0 := by
  have hhigh : ∀ α : Fin 2 → ℕ, 4 ≤ α 0 + α 1 →
      (taylorHom (substPoint w b₁ b₂ p 0) b₁ b₂ f).coeff (Finsupp.equivFunOnFinite.symm α) = 0 :=
    fun α hα => taylorHom_coeff_high f hf (substPoint w b₁ b₂ p 0) b₁ b₂ h0 α hα
  have hCoeff : ∀ α : Fin 2 → ℕ,
      (taylorHom (substPoint w b₁ b₂ p 0) b₁ b₂ f).coeff (Finsupp.equivFunOnFinite.symm α)
        = MvPolynomial.eval p (levelForm w b₁ b₂ f α) := by
    intro α
    rw [← mapEvalSigma w b₁ b₂ f p, MvPolynomial.coeff_map]
    rfl
  have hfun : (∀ u : Fin 2 → ℚ,
        MvPolynomial.eval u (taylorHom (substPoint w b₁ b₂ p 0) b₁ b₂ f) = 0)
      ↔ (taylorHom (substPoint w b₁ b₂ p 0) b₁ b₂ f) = 0 := by
    constructor
    · intro h
      apply MvPolynomial.funext
      intro u
      rw [h u, map_zero]
    · intro h u
      rw [h, map_zero]
  have hzero : ((taylorHom (substPoint w b₁ b₂ p 0) b₁ b₂ f) = 0)
      ↔ ∀ α : Fin 2 → ℕ,
          (taylorHom (substPoint w b₁ b₂ p 0) b₁ b₂ f).coeff (Finsupp.equivFunOnFinite.symm α) = 0 := by
    constructor
    · intro h α
      rw [h]
      simp
    · intro h
      ext m
      have h1 := h (Finsupp.equivFunOnFinite m)
      rwa [Equiv.symm_apply_apply] at h1
  have hmain : (∀ u : Fin 2 → ℚ,
        MvPolynomial.eval u (taylorHom (substPoint w b₁ b₂ p 0) b₁ b₂ f) = 0)
      ↔ ∀ α : Fin 2 → ℕ, α 0 + α 1 ≤ 3 →
          MvPolynomial.eval p (levelForm w b₁ b₂ f α) = 0 := by
    rw [hfun, hzero]
    constructor
    · intro h α hα
      rw [← hCoeff α]; exact h α
    · intro h α
      by_cases h4 : 4 ≤ α 0 + α 1
      · exact hhigh α h4
      · rw [hCoeff α]; exact h α (by omega)
  have hiff : (∀ u : Fin 2 → ℚ, MvPolynomial.eval (substPoint w b₁ b₂ p u) f = 0)
      ↔ (∀ u : Fin 2 → ℚ,
          MvPolynomial.eval u (taylorHom (substPoint w b₁ b₂ p 0) b₁ b₂ f) = 0) := by
    constructor
    · intro h u
      rw [evalTaylorHom w b₁ b₂ f p u]; exact h u
    · intro h u
      rw [← evalTaylorHom w b₁ b₂ f p u]; exact h u
  exact hiff.trans hmain

theorem isSolIff (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ)
    (f : MvPolynomial (Fin 5) ℚ) (hf : f.IsHomogeneous 4) (p : Fin 3 → ℚ)
    (hℓ : ∀ u : Fin 2 → ℚ, MvPolynomial.eval (u 0 • b₁ + u 1 • b₂) f = 0) :
    (∀ u : Fin 2 → ℚ, MvPolynomial.eval (Work.Q44Geom.substPoint w b₁ b₂ p u) f = 0)
      ↔ ∀ i ∈ Finset.range 4, ∀ j ∈ Finset.range 4, i + j ≤ 3 →
          MvPolynomial.eval p (Work.Q44Geom.levelForm w b₁ b₂ f ![i, j]) = 0 := by
  have h0 : taylorHom 0 b₁ b₂ f = 0 := taylorHom_zero w b₁ b₂ f hℓ
  have haux := isSol_iff_levelForms_aux w b₁ b₂ f hf p h0
  constructor
  · intro h i hi j hj hij
    exact haux.mp h ![i, j] (by simpa using hij)
  · intro h
    refine haux.mpr ?_
    intro α hα
    have hi : α 0 ∈ Finset.range 4 := by simp only [Finset.mem_range]; omega
    have hj : α 1 ∈ Finset.range 4 := by simp only [Finset.mem_range]; omega
    rw [show α = ![α 0, α 1] from by funext k; fin_cases k <;> simp]
    exact h (α 0) hi (α 1) hj (by omega)

end Work.Q44Geom
