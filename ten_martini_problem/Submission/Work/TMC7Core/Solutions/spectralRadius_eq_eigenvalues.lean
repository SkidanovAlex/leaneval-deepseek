import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial Matrix
open scoped ENNReal

namespace Work.TMC7Core.Solutions

/-- For a `2 × 2` complex matrix `M` with determinant `1`, whose trace equals `la + mu`
and whose determinant equals `la * mu`, the spectral radius of `M` is the maximum of the
norms of the eigenvalues `la` and `mu`. -/
theorem spectralRadius_eq_eigenvalues (M : Matrix (Fin 2) (Fin 2) ℂ) (hd : M.det = 1)
    (la mu : ℂ) (hsum : la + mu = M.trace) (hprod : la * mu = 1) :
    spectralRadius ℂ M = ENNReal.ofReal (max ‖la‖ ‖mu‖) := by
  -- The characteristic polynomial factors through the two given eigenvalues.
  have hchar : M.charpoly = (X - C la) * (X - C mu) := by
    rw [Matrix.charpoly_fin_two, ← hsum, hd, ← hprod]
    simp only [map_add, map_mul]
    ring
  -- The spectrum is exactly the set of the two eigenvalues.
  have hspec : spectrum ℂ M = {la, mu} := by
    ext z
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hchar, Polynomial.IsRoot.def,
      Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_C,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h; rcases mul_eq_zero.mp h with h | h
      · left; exact sub_eq_zero.mp h
      · right; exact sub_eq_zero.mp h
    · rintro (rfl | rfl) <;> simp
  -- Unfold the spectral radius and evaluate the supremum over the two-element spectrum.
  rw [spectralRadius_eq_of_unital]
  rw [hspec, iSup_insert, iSup_singleton]
  have hla : (‖la‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖la‖ := by rw [ofReal_norm, enorm_eq_nnnorm]
  have hmu : (‖mu‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖mu‖ := by rw [ofReal_norm, enorm_eq_nnnorm]
  rw [hla, hmu, ← ENNReal.ofReal_max]

end Work.TMC7Core.Solutions
