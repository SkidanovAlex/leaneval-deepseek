import Mathlib
import Submission.Work.KT.PatchProjDefs
import Submission.Work.KT.FiberUtil
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.stdProj_isIdem
import Submission.Work.KT.stdProj_mvN

/-!
# Auxiliary `K₀` identifications for the clutching projection (`Work.KT.clipP_cls_aux`)

The class in `K₀(TwoDisk V) = K₀(C(S^{dim V}))` of the clutching projection `clipP` of
`Work.KT.PatchProjDefs` is the class of the trivial bundle of rank `n`: the projection has rank
`n` at the centre of the first disk, so its class is reduced, and the reduced `K`-theory of the
odd-dimensional sphere `S^{2j+1} = Sph (WithLp 2 (V × ℝ))` (when `finrank ℝ V = 2j+1`) vanishes
(`Work.KT.sphere_K_even_aux`).
-/

namespace Work.KT

open Matrix

noncomputable section

set_option maxHeartbeats 800000

/-- Conjugation of an idempotent by an invertible matrix is a Murray–von Neumann equivalence. -/
theorem mvN_conj_mat_pc {R : Type} [Ring R] {N : ℕ} {M M' : Matrix (Fin N) (Fin N) R}
    (h1 : M * M' = 1) (h2 : M' * M = 1) {p : Matrix (Fin N) (Fin N) R} (hp : p * p = p) :
    Mat.MvN (⟨N, M' * p * M⟩ : Mat R) ⟨N, p⟩ := by
  refine ⟨p * M, M' * p, ?_, ?_⟩
  · show M' * p * (p * M) = M' * p * M
    rw [← mul_assoc (M' * p) p M, mul_assoc M' p p, hp]
  · show p * M * (M' * p) = p
    rw [mul_assoc p M (M' * p), ← mul_assoc M M' p, h1, one_mul, hp]

/-- `Mat.map` of the identity matrix. -/
theorem Mat.map_one_pc {R S : Type} [Ring R] [Ring S] (φ : R →+* S) (n : ℕ) :
    (Mat.one R n).map φ = Mat.one S n := by
  have h : (1 : Matrix (Fin n) (Fin n) R).map (⇑φ) = 1 := by
    rw [← RingHom.mapMatrix_apply]
    exact (RingHom.mapMatrix φ).map_one
  unfold Mat.one Mat.map
  rw [h]

/-- Conjugating an idempotent over `ℂ` does not change its `K₀`-class. -/
theorem cls_conj_pc {N : ℕ} {M M' : Matrix (Fin N) (Fin N) ℂ} (h1 : M * M' = 1)
    (h2 : M' * M = 1) {p : Matrix (Fin N) (Fin N) ℂ} (hp : p * p = p) :
    cls (⟨N, M' * p * M⟩ : Mat ℂ) = cls (⟨N, p⟩ : Mat ℂ) := by
  have hidem : Mat.IsIdem (⟨N, M' * p * M⟩ : Mat ℂ) := by
    show M' * p * M * (M' * p * M) = M' * p * M
    calc M' * p * M * (M' * p * M) = M' * p * (M * M') * p * M := by noncomm_ring
      _ = M' * p * 1 * p * M := by rw [h1]
      _ = M' * (p * p) * M := by noncomm_ring
      _ = M' * p * M := by rw [hp]
  exact cls_eq_of_mvn hidem hp (mvN_conj_mat_pc h1 h2 hp)

/-- The class of the standard projection over `ℂ` is the class of the identity of rank `m`. -/
theorem cls_stdProj_pc (m : ℕ) :
    cls (⟨m + m, stdProj ℂ m⟩ : Mat ℂ) = cls (Mat.one ℂ m) :=
  cls_eq_of_mvn (stdProj_isIdem (R := ℂ) m) (Mat.one_isIdem (R := ℂ) m)
    (stdProj_mvN (R := ℂ) m)

end

end Work.KT
