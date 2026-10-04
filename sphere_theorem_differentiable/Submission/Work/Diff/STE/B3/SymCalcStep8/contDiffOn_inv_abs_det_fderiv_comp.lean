import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep8

open scoped ContDiff BigOperators

/-- Smoothness of the determinant of a componentwise smooth matrix family (Leibniz's formula,
`Matrix.det_apply'`). -/
private lemma contDiff_det_of_components {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Y : (ι → ℝ) → Matrix ι ι ℝ}
    (hY : ∀ p q, ContDiff ℝ (⊤ : ℕ∞) (fun z => Y z p q)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => (Y z).det) := by
  classical
  rw [show (fun z : ι → ℝ => (Y z).det)
      = fun z => ∑ σ : Equiv.Perm ι,
          (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ k, Y z (σ k) k from by
    funext z; rw [Matrix.det_apply']]
  exact ContDiff.sum (fun σ _ => contDiff_const.mul (contDiff_prod (fun k _ => hY (σ k) k)))

/-- Smoothness of the reciprocal of the absolute Jacobian determinant of a smooth map along a
smooth map, on the open set where that determinant does not vanish.

Route: `z ↦ fderiv ℝ f (g z)` is smooth (`ContDiff.fderiv_right` composed with `hg`),
`z ↦ (fderiv ℝ f (g z)).det` is smooth because in the standard basis of `ι → ℝ` the determinant is
the polynomial `Matrix.det` of the matrix `(L (Pi.single q 1)) p` of the linear map
(`LinearMap.det_toMatrix'`, `Matrix.det_apply'`); then `|·|` is smooth on `ℝ \ {0}`
(`ContDiffOn.abs`) and inversion of a nonvanishing scalar is `ContDiffOn.inv` (both in `ℝ`, after
the coercion `ℝ → ℂ` via `Complex.ofRealCLM`). -/
theorem contDiffOn_inv_abs_det_fderiv_comp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : (ι → ℝ) → (ι → ℝ)) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => ((|(fderiv ℝ f (g z)).det| : ℝ)⁻¹ : ℂ)) {z | (fderiv ℝ f (g z)).det ≠ 0} := by
  classical
  -- `z ↦ fderiv ℝ f (g z)` is smooth.
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ f (g z)) :=
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) (by simp)).comp hg
  -- Its matrix in the standard basis `Pi.basisFun ℝ ι` has componentwise smooth entries.
  have hmat : ∀ p q : ι, ContDiff ℝ (⊤ : ℕ∞)
      (fun z => (Matrix.of (fun p q => (fderiv ℝ f (g z)) (Pi.single q 1) p)) p q) := by
    intro p q
    exact ContDiff.comp
      (ContinuousLinearMap.contDiff (ContinuousLinearMap.proj (φ := fun _ : ι => ℝ) p))
      (hfd.clm_apply (contDiff_const (c := Pi.single q (1 : ℝ))))
  -- Hence the determinant is smooth.
  have hdet : ContDiff ℝ (⊤ : ℕ∞) (fun z => (fderiv ℝ f (g z)).det) := by
    have h := contDiff_det_of_components
      (Y := fun z => Matrix.of (fun p q => (fderiv ℝ f (g z)) (Pi.single q 1) p)) hmat
    have heq : (fun z => (Matrix.of (fun p q => (fderiv ℝ f (g z)) (Pi.single q 1) p)).det)
        = fun z => (fderiv ℝ f (g z)).det := by
      funext z
      rw [show Matrix.of (fun p q => (fderiv ℝ f (g z)) (Pi.single q 1) p)
            = LinearMap.toMatrix' ((fderiv ℝ f (g z)) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) from rfl.symm]
      rw [LinearMap.det_toMatrix']
    rwa [heq] at h
  -- `|·|` is smooth where the determinant does not vanish, and so is its reciprocal.
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => |(fderiv ℝ f (g z)).det|)
      {z | (fderiv ℝ f (g z)).det ≠ 0} :=
    hdet.contDiffOn.abs (fun z hz => hz)
  have h1c : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (((|(fderiv ℝ f (g z)).det| : ℝ)) : ℂ)) {z | (fderiv ℝ f (g z)).det ≠ 0} :=
    (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp_contDiffOn h1
  exact h1c.inv (fun z hz => by
    rw [Complex.ofReal_ne_zero]; exact abs_ne_zero.mpr hz)

end Work.Diff.STE.B3.SymCalcStep8
