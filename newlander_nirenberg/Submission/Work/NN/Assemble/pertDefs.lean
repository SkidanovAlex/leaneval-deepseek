/-
The vocabulary of the **perturbed Kohn--Morrey (Hörmander) basic estimate**
(`Work.NN.Assemble.pertBasicEstimate`).

Everything here is *definitions* plus elementary consequences; no analytic input is used.  The
objects are

* `pertCoef f` — the coefficient family `F_j(z) = f z (e_j)` of a `(0,1)`-form in the flat model
  `ℂⁿ = Fin n → ℂ`, in the convention of the target statement;
* `wPair0 φ u v = ∫ u · conj v · e^{-φ}` — the `ℂ`-valued weighted pairing of *functions*, the
  shape in which the formal adjoint of `∂̄_J` is tested;
* `pertDiv A j` — the divergence of the vector field `z ↦ A z e_j`;
* `pertAdj A φ f` — the **formal adjoint of the perturbed operator** `h ↦ ∂̄_J h` (`J = Jstd + A`)
  with respect to the weight `φ`, applied to `f`.  It is the function `g` with
  `wPair0 φ g h = wP1 φ f (dbarJ_fun A h)` for every smooth compactly supported `h` (proved in
  `Submission/Work/NN/Assemble/pertAdjIdentity`, which imports this file).  Explicitly, with
  `D_V` the real directional derivative and `δ_j = ∂_j - ∂_jφ`,

  `pertAdj A φ f = dbarSt φ F + (i/2) Σ_j (F_j · div(A e_j) + D_{A e_j} F_j - F_j · D_{A e_j} φ)`,

  where `F = pertCoef f` and `dbarSt φ F = -Σ_j δ_j F_j`.
-/
import Mathlib
import Submission.Work.NN.Assemble.L2Forms
import Submission.Work.NN.Assemble.PertSetup

noncomputable section

open MeasureTheory Set
open scoped Topology ContDiff

namespace Work.NN.Assemble

/-- The coefficient family `F_j(z) = f z (e_j)` of a `(0,1)`-form. -/
noncomputable def pertCoef {n : ℕ} (f : Cn n → Cn n →L[ℝ] ℂ) : Fin n → Cn n → ℂ :=
  fun j z => f z (eb n j)

@[simp] lemma pertCoef_apply {n : ℕ} (f : Cn n → Cn n →L[ℝ] ℂ) (j : Fin n) (z : Cn n) :
    pertCoef f j z = f z (eb n j) := rfl

/-- The weighted `ℂ`-valued pairing of two functions: `wPair0 φ u v = ∫ u · conj v · e^{-φ}`. -/
noncomputable def wPair0 {n : ℕ} (φ : Cn n → ℝ) (u v : Cn n → ℂ) : ℂ :=
  ∫ z, u z * star (v z) * (Real.exp (-(φ z)) : ℂ)

/-- The divergence of the complex vector field `z ↦ A z e_j`, i.e.
`Σ_k (∂_k V_k + ∂̄_k conj V_k) = 2 Σ_k Re (∂_k V_k)` for `V_k = (A z e_j)_k`. -/
noncomputable def pertDiv {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n) (j : Fin n) (z : Cn n) : ℂ :=
  2 * ((∑ k, (Work.CR.Flat.dCoord k (fun z' => A z' (eb n j) k) z).re : ℝ) : ℂ)

/-- **The formal adjoint of the perturbed `∂̄`** (`J = Jstd + A`), with respect to the weight `φ`,
applied to a `(0,1)`-form `f`; see the module docstring. -/
noncomputable def pertAdj {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n) (φ : Cn n → ℝ)
    (f : Cn n → Cn n →L[ℝ] ℂ) : Cn n → ℂ :=
  fun z => dbarSt φ (pertCoef f) z + (Complex.I / 2) * ∑ j, (
    (fderiv ℝ (pertCoef f j) z) (A z (eb n j))
      + pertCoef f j z * pertDiv A j z
      - pertCoef f j z * ((fderiv ℝ φ z (A z (eb n j)) : ℝ) : ℂ))

/-- The weighted `L²` square norm `wN1` of a form is the `(0,1)`-coefficient weighted norm of its
coefficient family. -/
lemma wN1_eq_wnSq1_pertCoef {n : ℕ} (φ : Cn n → ℝ) (f : Cn n → Cn n →L[ℝ] ℂ) :
    wN1 φ f = wnSq1 φ (pertCoef f) := rfl

/-- The weighted `L²` square norm `wN2J` of a `(0,2)`-form given by its values is the `(0,2)`-norm
of the array of its values on the standard basis. -/
lemma wN2J_eq_wnSq2 {n : ℕ} (φ : Cn n → ℝ)
    (F : Cn n → Cn n → Cn n → ℂ) :
    wN2J φ F = wnSq2 φ (fun j k z => F z (eb n j) (eb n k)) := rfl

lemma continuous_pertCoef {n : ℕ} {f : Cn n → Cn n →L[ℝ] ℂ} (hf : ∀ m : ℕ, ContDiff ℝ m f)
    (j : Fin n) : Continuous (pertCoef f j) := by
  have h : Continuous (fun z => f z (eb n j)) :=
    (contDiff_zero.mp (hf 0)).clm_apply continuous_const
  exact h

lemma contDiff_pertCoef {n : ℕ} {f : Cn n → Cn n →L[ℝ] ℂ} (hf : ∀ m : ℕ, ContDiff ℝ m f)
    (j : Fin n) (m : ℕ) : ContDiff ℝ m (pertCoef f j) := by
  have h : ContDiff ℝ m (fun z => f z (eb n j)) := (hf m).clm_apply contDiff_const
  exact h

lemma hasCompactSupport_pertCoef {n : ℕ} {f : Cn n → Cn n →L[ℝ] ℂ} (hf : HasCompactSupport f)
    (j : Fin n) : HasCompactSupport (pertCoef f j) := by
  have h : HasCompactSupport (fun z => f z (eb n j)) :=
    hf.comp_left (g := fun φ : Cn n →L[ℝ] ℂ => φ (eb n j)) (by simp)
  exact h


/-- The complex conjugate of a `(0,1)`-form (conjugation of the values). -/
noncomputable def conjForm {n : ℕ} (f : Cn n → Cn n →L[ℝ] ℂ) : Cn n → Cn n →L[ℝ] ℂ :=
  fun z => (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (f z)

/-- The `(1,0)`-operator `∂_J` (`J = Jstd + A`), i.e. the conjugate of `∂̄_J`: `∂_J u` is the form
whose values are the conjugates of those of `∂̄_J (conj u)`. -/
noncomputable def dbarConjJ {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n) (u : Cn n → ℂ) :
    Cn n → Cn n →L[ℝ] ℂ :=
  fun z => (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (dbarJ_fun A (fun z' => star (u z')) z)

@[simp] lemma conjForm_apply {n : ℕ} (f : Cn n → Cn n →L[ℝ] ℂ) (z v : Cn n) :
    conjForm f z v = star (f z v) := rfl

@[simp] lemma dbarConjJ_apply {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n) (u : Cn n → ℂ)
    (z v : Cn n) : dbarConjJ A u z v = star (dbarJ_fun A (fun z' => star (u z')) z v) := rfl

end Work.NN.Assemble
