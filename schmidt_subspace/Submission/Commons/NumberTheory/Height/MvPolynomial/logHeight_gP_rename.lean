import Mathlib
import Submission.Commons.NumberTheory.Height.MvPolynomial.polyHeight_mul_le

namespace Commons.NumberTheory.Height.MvPolynomial

/-- The equivalence `Option (σ →₀ ℕ) ≃ Option (τ →₀ ℕ)` induced by `e : σ ≃ τ`. -/
noncomputable def optionMapDomainEquiv {σ τ : Type*} (e : σ ≃ τ) :
    Option (σ →₀ ℕ) ≃ Option (τ →₀ ℕ) :=
  Equiv.optionCongr (Finsupp.equivCongrLeft e)

@[simp]
lemma optionMapDomainEquiv_apply_none {σ τ : Type*} (e : σ ≃ τ) :
    optionMapDomainEquiv e none = none := rfl

@[simp]
lemma optionMapDomainEquiv_apply_some {σ τ : Type*} (e : σ ≃ τ) (m : σ →₀ ℕ) :
    optionMapDomainEquiv e (some m) = some (Finsupp.mapDomain e m) := by
  simp [optionMapDomainEquiv, Finsupp.equivMapDomain_eq_mapDomain]

/-- Renaming the variables via an equivalence `e` reindexes the coefficient tuple `gP`. -/
lemma gP_rename_comp {σ τ : Type*} (e : σ ≃ τ) (P : MvPolynomial σ ℚ) :
    gP (MvPolynomial.rename e P) ∘ optionMapDomainEquiv e = gP P := by
  funext o
  cases o with
  | none => simp [gP]
  | some m =>
      simp only [Function.comp_apply, optionMapDomainEquiv_apply_some, gP, Option.elim_some]
      rw [MvPolynomial.coeff_rename_mapDomain e e.injective P m]

lemma logHeight_gP_rename {σ τ : Type*} [Fintype σ] [Fintype τ] (e : σ ≃ τ)
    (P : MvPolynomial σ ℚ) :
    Height.logHeight (Commons.NumberTheory.Height.MvPolynomial.gP (MvPolynomial.rename e P)) =
      Height.logHeight (Commons.NumberTheory.Height.MvPolynomial.gP P) := by
  rw [← gP_rename_comp e P, Height.logHeight_comp_equiv]

end Commons.NumberTheory.Height.MvPolynomial
