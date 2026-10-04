import Mathlib
import Submission.Work.Diff.STE.FlatPDE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Conjugation symmetry of the flat DeTurck Cauchy problem

If the nonlinearity `Φ` is conjugation-equivariant (`ConjEquivNonlin`), then the entrywise
conjugate of a solution of `∂_t u = Φ (·, jet u)` is again a solution.  This is the formal
statement that the "real" solutions are closed under the symmetry, and it is what makes the
`real` output of the flat short-time existence theorem a consequence of the ℂ-valued analysis.

The proof is the three-part definition of `SolvesOn`:

* smoothness: `conjMat` is (`ℝ`-)linear and continuous (it is `star`, i.e. `starL' ℝ`), so it
  preserves joint `C^∞`;
* periodicity: conjugation is applied pointwise, and `u t` is periodic;
* the equation: `∂_t` commutes with the continuous linear (over `ℝ`) map `conjMat`
  (`HasDerivWithinAt.star`), and the jets of the conjugated function are the conjugates of the
  jets (`pdM_conj`), which together with `ConjEquivNonlin` identifies the conjugated right-hand
  side.
-/

open scoped BigOperators

namespace Work.Diff.STE.flat

/-- The entrywise conjugate of a matrix is its `star`. -/
lemma conjMat_eq_star {n : ℕ} (A : Flat.MatC n) : Flat.conjMat A = star A := by
  funext i j; rfl

/-- The partial derivative commutes with complex conjugation.  (Conjugation is `ℝ`-linear, hence
`fderiv ℝ` commutes with it.) -/
lemma pd_star {n : ℕ} (c : Fin n) (g : (Fin n → ℝ) → ℂ) :
    Work.Diff.STE.pd c (fun y => star (g y)) = fun y => star (Work.Diff.STE.pd c g y) := by
  funext x
  simp only [Work.Diff.STE.pd]
  have h : (fun y : Fin n → ℝ => star (g y)) = (⇑(starL' ℝ : ℂ ≃L[ℝ] ℂ)) ∘ g := by
    funext y; rw [Function.comp_apply, starL'_apply]
  rw [h, ContinuousLinearEquiv.comp_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, starL'_apply]

/-- The coordinate derivative of a matrix-valued function commutes with entrywise conjugation. -/
lemma pdM_conj {n : ℕ} (c : Fin n) (w : Flat.Torus n) :
    Flat.pdM c (fun y => Flat.conjMat (w y)) = fun y => Flat.conjMat (Flat.pdM c w y) := by
  funext x i j
  simp only [Flat.pdM, Flat.conjMat]
  exact congrFun (pd_star c (fun y => w y i j)) x

/-- The `2`-jet of the entrywise conjugate is the entrywise conjugate of the `2`-jet. -/
lemma jetM_conj {n : ℕ} (w : Flat.Torus n) (x : Fin n → ℝ) :
    Flat.jetM (fun y => Flat.conjMat (w y)) x
      = (Flat.conjMat (w x), (fun c => Flat.conjMat (Flat.pdM c w x)),
         (fun c d => Flat.conjMat (Flat.pdM c (Flat.pdM d w) x))) := by
  refine Prod.ext rfl ?_
  refine Prod.ext ?_ ?_
  · funext c; exact congrFun (pdM_conj c w) x
  · funext c d
    show Flat.pdM c (Flat.pdM d (fun y => Flat.conjMat (w y))) x = _
    rw [pdM_conj d w]
    exact congrFun (pdM_conj c (Flat.pdM d w)) x

theorem solvesOn_conj {n : ℕ}
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hconj : Work.Diff.STE.Flat.ConjEquivNonlin Φ)
    (T : ℝ) (u : ℝ → Work.Diff.STE.Flat.Torus n)
    (hu : Work.Diff.STE.Flat.SolvesOn Φ T u) :
    Work.Diff.STE.Flat.SolvesOn Φ T (fun t => Work.Diff.STE.Flat.conjMat ∘ u t) := by
  obtain ⟨hcont, hper, hpde⟩ := hu
  refine ⟨?_, ?_, ?_⟩
  · -- smoothness: `conjMat` is the continuous linear map `starL' ℝ`
    have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun A : Flat.MatC n => Flat.conjMat A) := by
      have h := ((starL' ℝ : Flat.MatC n ≃L[ℝ] Flat.MatC n)).contDiff (n := (⊤ : ℕ∞))
      rwa [show (⇑(starL' ℝ : Flat.MatC n ≃L[ℝ] Flat.MatC n)) = fun A => Flat.conjMat A from by
            funext A; rw [starL'_apply]; exact conjMat_eq_star A] at h
    exact (hcd.comp_contDiffOn hcont).congr (fun p _ => rfl)
  · -- periodicity
    intro t ht i x
    simp only [Function.comp_apply]
    rw [hper t ht i x]
  · -- the equation
    intro t ht x
    have hstar : HasDerivWithinAt (fun s => star (u s x))
        (star (Φ (x, Flat.jetM (u t) x))) (Set.Ico 0 T) t := (hpde t ht x).star
    have hkey : star (Φ (x, Flat.jetM (u t) x))
        = Φ (x, Flat.jetM (Flat.conjMat ∘ u t) x) := by
      rw [← conjMat_eq_star]
      rw [show Flat.jetM (u t) x = ((u t x), (fun c => Flat.pdM c (u t) x),
              (fun c d => Flat.pdM c (Flat.pdM d (u t)) x)) from rfl]
      rw [(hconj x (u t x) (fun c => Flat.pdM c (u t) x)
            (fun c d => Flat.pdM c (Flat.pdM d (u t)) x)).symm]
      rw [← jetM_conj (u t) x]
      rfl
    rw [hkey] at hstar
    rw [show (fun s => (Flat.conjMat ∘ u s) x) = (fun s => star (u s x)) from by
          funext s; simp only [Function.comp_apply, conjMat_eq_star]]
    exact hstar

end Work.Diff.STE.flat
