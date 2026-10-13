/-
  Work.WilE2 — area E2.  The set of *bad* (critical) values for the old system map is null.

  `KhoRegValue S F y` says that `y` is a regular value of the system map

      Φ_S,F : ℝⁿ → ℝⁿ,   x ↦ (fun i => S.ev (F i) x),

  i.e. that every root over `y` has invertible symbolic Jacobian
  `(S.ev (S.d j (F i)) x)_{ij}` (equivalently, invertible Fréchet derivative `fderiv ℝ Φ x`).

  The complement is therefore *by definition* the set of critical values of `Φ`, the image of
  the critical set `{x | (fderiv ℝ Φ x).det = 0}`.  The two ingredients are

  * `Jac.fderiv_system`/`Jac.fderiv_system_apply` — the Fréchet derivative of `Φ` is the tuple
    of gradients `(S.grad (F i) x)`, so its matrix on the standard basis is exactly the symbolic
    Jacobian `(S.ev (S.d j (F i)) x)_{ij}` (`fderiv_system_matrix`);
  * `Submission.Work.WilE2.sard_square` — Sard's lemma in the square case, giving nullity of the
    image of the critical set for any differentiable map `ℝⁿ → ℝⁿ`.

  No polynomiality is needed: differentiability of `Φ` is enough, and that comes from the chain
  rule for evaluated EA polynomials (`ev_hasFDerivAt`).
-/
import Mathlib
import Submission.Work.WilE2.KhoGood
import Submission.Work.WilE2.Jac
import Submission.Work.WilE2.sard_square

noncomputable section

namespace Work.WilE2

open Classical
open WilkiesDesign WilkiesDesign.E WilkiesConjecture

/-- The determinant of a continuous linear endomorphism of `ℝⁿ` is the determinant of the
matrix of its values on the standard basis vectors (Mathlib's `LinearMap.toMatrix'`). -/
theorem clm_det_eq {n : ℕ} (f : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    f.det = (Matrix.of fun i j => f (Pi.single j 1) i).det := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix']
  congr 1

/-- The matrix of the differential of the system map on the standard basis is the symbolic
Jacobian `(S.ev (S.d j (F i)) x)_{ij}`. -/
theorem fderiv_system_matrix {n r : ℕ} (S : ESys n r) (F : Fin n → EPoly n r)
    (x : Fin n → ℝ) :
    (Matrix.of fun i j => S.ev (S.d j (F i)) x)
      = (Matrix.of fun i j =>
          fderiv ℝ (fun y : Fin n → ℝ => fun i => S.ev (F i) y) x (Pi.single j 1) i) := by
  ext i j
  rw [Matrix.of_apply, Matrix.of_apply, fderiv_system_apply]

/-- Consequently the two determinants agree: the Jacobian determinant of the system at `x` is
the determinant of the differential of the system map at `x`. -/
theorem fderiv_system_det {n r : ℕ} (S : ESys n r) (F : Fin n → EPoly n r) (x : Fin n → ℝ) :
    (fderiv ℝ (fun y : Fin n → ℝ => fun i => S.ev (F i) y) x).det
      = (Matrix.of fun i j => S.ev (S.d j (F i)) x).det := by
  rw [clm_det_eq, fderiv_system_matrix]

/-- The values at which the old system is not regular are exactly the critical values of the
system map. -/
theorem nonReg_eq_image_critical {n s : ℕ} (S : ESys n (s + 1))
    (F : Fin n → EPoly n (s + 1)) :
    {y : Fin n → ℝ | ¬ KhoRegValue S F y}
      = (fun x : Fin n → ℝ => fun i => S.ev (F i) x) ''
        {x | (fderiv ℝ (fun y : Fin n → ℝ => fun i => S.ev (F i) y) x).det = 0} := by
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · intro hy
    simp only [KhoRegValue, not_forall] at hy
    obtain ⟨x, hxy, hdet⟩ := hy
    exact ⟨x, by rw [fderiv_system_det]; exact not_not.mp hdet, hxy⟩
  · rintro ⟨x, hdet, hxy⟩
    intro h
    have h1 : (Matrix.of fun i j => S.ev (S.d j (F i)) x).det ≠ 0 := h x hxy
    have h2 : (Matrix.of fun i j => S.ev (S.d j (F i)) x).det = 0 := by
      rw [← fderiv_system_det]; exact hdet
    exact h1 h2

/-- **The bad values of the old system are null.**  This is Sard's lemma for the polynomial
system map: the values at which some root has a singular Jacobian form a Lebesgue-null set. -/
theorem khoReg_bad_null {n s : ℕ} (S : ESys n (s + 1)) (F : Fin n → EPoly n (s + 1)) :
    MeasureTheory.volume {y : Fin n → ℝ | ¬ KhoRegValue S F y} = 0 := by
  rw [nonReg_eq_image_critical]
  have hset : {x : Fin n → ℝ |
        (fderiv ℝ (fun y : Fin n → ℝ => fun i => S.ev (F i) y) x).det = 0}
      = {x : Fin n → ℝ |
        (ContinuousLinearMap.pi fun i => S.grad (F i) x).det = 0} := by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, fderiv_system]
  rw [hset]
  exact sard_square _ _ (fun x => system_hasFDerivAt S F x)

end Work.WilE2
