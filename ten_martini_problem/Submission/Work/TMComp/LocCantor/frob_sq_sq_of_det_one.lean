import Mathlib
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Scale.frob_map_ofReal_sq
import Submission.Work.TMComp.LocCantor.sqsum_smul_sub
import Submission.Work.TMC14Core.hyps_reduce

/-!
# The Frobenius norm of the square of an `SL₂(ℝ)` matrix

For a real `2 × 2` matrix `B` with `det B = 1` we have
`‖B²‖_F² = 2 + (‖B‖_F² - 2) · (tr B)²`.

This is the case `k = 2` of the Chebyshev-type formula for `SL₂(ℝ)` powers: since
`B² = tr(B) · B - 1` (Cayley–Hamilton), the sum of the squares of the entries of `B²`
equals `u₁² · Σ Bᵢⱼ² - 2 u₁ u₂ tr B + 2 u₂²` with `u₁ = tr B`, `u₂ = 1`
(`sqsum_smul_sub`), i.e. `(tr B)² ‖B‖_F² - 2 (tr B)² + 2 = 2 + (‖B‖_F² - 2)(tr B)²`.
-/

namespace Work.TMComp.LocCantor

/-- Cayley–Hamilton for a real `2 × 2` matrix: `B ^ 2 = B.trace • B - 1`. -/
lemma sq_eq_trace_smul_sub_one (B : Matrix (Fin 2) (Fin 2) ℝ) (hdet : B.det = 1) :
    B ^ 2 = B.trace • B - (1 : ℝ) • 1 := by
  have hdet' : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    rwa [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] <;>
    ring_nf <;> try nlinarith [hdet']

theorem frob_sq_sq_of_det_one (B : Matrix (Fin 2) (Fin 2) ℝ) (hdet : B.det = 1) :
    Work.TMC7Core.frob ((B.map Complex.ofRealHom) ^ 2) ^ 2
      = 2 + (Work.TMC7Core.frob (B.map Complex.ofRealHom) ^ 2 - 2) * B.trace ^ 2 := by
  have hfun : (⇑Complex.ofRealHom : ℝ → ℂ) = fun x : ℝ => (x : ℂ) := rfl
  have hmap : (B.map Complex.ofRealHom) ^ 2 = (B ^ 2).map Complex.ofRealHom :=
    (Matrix.map_pow B Complex.ofRealHom 2).symm
  rw [hmap, hfun, Work.TMC7Core.Scale.frob_map_ofReal_sq (B ^ 2),
    Work.TMC7Core.Scale.frob_map_ofReal_sq B, sq_eq_trace_smul_sub_one B hdet,
    sqsum_smul_sub B B.trace 1]
  ring

end Work.TMComp.LocCantor
