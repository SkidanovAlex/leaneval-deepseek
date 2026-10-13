import Mathlib
import Submission.Work.WilE3K.Elim
import Submission.Work.WilE2.ift_perturbation
import Submission.Work.WilE3K.contDiff_map_and_det

set_option maxHeartbeats 1000000

namespace Work.WilE3K

/-- Perturbation form of the inverse function statement at the nondegenerate zeros of `E`: every nondegenerate zero `z` of the lifted system is a nondegenerate zero of the square map `E.map` (`E.map z = 0` because all `E.evP i` and `E.tanFun j` vanish, and `det (fderiv ℝ E.map z) = (E.jac z).det ≠ 0` by the Jacobian dictionary), so `Work.WilE2.ift_perturbation` applies to the `C¹` map `E.map` and the finite set `s`. The smoothness `ContDiff ℝ 1 E.map` and the identity `(fderiv ℝ E.map z).det = (E.jac z).det` follow from `Work.WilE3K.ContAux` (`E.evalPoly_eq_eaEval`, `E.dPoly_eq_eaD`), `Work.WilE9.EaD.eaEval_contDiff`, `Work.WilE9.EaD.eaD_hasFDerivAt` (the matrix of `fderiv ℝ E.map z` on the standard basis is `E.jac z`, with `Real.hasDerivAt_arctan` on the `tan` rows) and `Work.WilE2.clm_det_eq`. -/
theorem ET_ift_perturbation {N rt n re : ℕ} (E : Work.WilE3K.ETData N (rt + 1) n re)
    (s : Finset (Fin (N + 1) → ℝ)) (hs : ∀ z ∈ s, E.Nondegen z) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ y' : Fin (N + 1) → ℝ, dist y' 0 < ρ →
      ∃ t : Finset (Fin (N + 1) → ℝ), t.card = s.card ∧ ∀ z ∈ t, E.map z = y' := by
  -- `E.map` is `C¹` (indeed `C²`).
  have hcont : ContDiff ℝ 1 E.map := (ETData.contDiff_map E).of_le (by norm_num)
  -- Every nondegenerate zero of `E` is a zero of `E.map`.
  have hzero : ∀ z ∈ s, E.map z = 0 := by
    intro z hz
    funext r
    by_cases hr : (r : ℕ) < rt + 1
    · rw [← E.tanCoord_tanIndex r hr, E.map_tan]
      simpa using ETData.Nondegen.tanFun E (hs z hz) (E.tanIndex r hr)
    · rw [← E.freeCoord_freeIndex r (not_lt.mp hr), E.map_free]
      simpa using ETData.Nondegen.evP E (hs z hz) (E.freeIndex r (not_lt.mp hr))
  -- The Jacobian determinant of `E.map` at such a zero is nonzero.
  have hnd : ∀ z ∈ s, (fderiv ℝ E.map z).det ≠ 0 := by
    intro z hz
    rw [ETData.fderiv_map_det E z]
    exact ETData.Nondegen.det E (hs z hz)
  exact Work.WilE2.ift_perturbation E.map hcont s hzero hnd

end Work.WilE3K
