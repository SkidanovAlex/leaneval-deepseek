import Mathlib
import Submission.Work.KT.PatchProjDefs
import Submission.Work.KT.FiberUtil
import Submission.Work.KT.stdProj_isIdem

namespace Work.KT

/-- Conjugating an idempotent by a unit (i.e. by an invertible element `g` with inverse `g'`) is
again idempotent. -/
private lemma mul_conj_idem {R : Type} [Ring R] {g g' S : R} (hS : S * S = S)
    (hgg' : g * g' = 1) : (g' * S * g) * (g' * S * g) = g' * S * g := by
  calc (g' * S * g) * (g' * S * g)
      = g' * S * (g * g') * S * g := by noncomm_ring
    _ = g' * S * 1 * S * g := by rw [hgg']
    _ = g' * S * S * g := by rw [mul_one]
    _ = g' * (S * S) * g := by noncomm_ring
    _ = g' * S * g := by rw [hS]

/-- The clutching projection `clipP` of `Work.KT.PatchProjDefs` is idempotent.  Its first
component is `G⁻¹ · Z · G` with `Z = diag(1_n,0_n)` idempotent and `G` a unit, and its second
component is `Z`; use `fiberMatrix_mul` and the idempotency of `stdProj` (available as
`Work.KT.mapMatrix_fstHom_clipZ`, `Work.KT.mapMatrix_sndHom_clipZ` and `stdProj_isIdem`). -/
theorem clipP_isIdem (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ)
    (γ : (Matrix (Fin n) (Fin n) C(Sph V, ℂ))ˣ) (G : (BallMat V n)ˣ)
    (hG : RingHom.mapMatrix (restRho V) (↑G : BallMat V n) = diagGlue V n γ) :
    clipP V n γ G hG * clipP V n γ G hG = clipP V n γ G hG := by
  rw [clipP, fiberMatrix_mul]
  apply fiberMatrix_ext
  · -- First component: `G⁻¹ · Z · G` is idempotent because `Z` is.
    rw [mapMatrix_fstHom_fiberMatrix, mapMatrix_fstHom_fiberMatrix, mapMatrix_fstHom_clipZ]
    have hS : stdProj C(Ball V, ℂ) n * stdProj C(Ball V, ℂ) n = stdProj C(Ball V, ℂ) n :=
      stdProj_isIdem n
    have hGG : (↑G : BallMat V n) * (↑(G⁻¹) : BallMat V n) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    exact mul_conj_idem hS hGG
  · -- Second component: `Z` is idempotent.
    rw [mapMatrix_sndHom_fiberMatrix, mapMatrix_sndHom_fiberMatrix, mapMatrix_sndHom_clipZ]
    exact stdProj_isIdem n

end Work.KT
